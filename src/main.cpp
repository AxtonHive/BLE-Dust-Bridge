#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <ESPmDNS.h>
#include <Preferences.h>
#include <NimBLEDevice.h>
#include <esp_coexist.h>
#include <esp_timer.h>
#include <Update.h>
#include <ArduinoJson.h>
#include <PubSubClient.h>
#include <mbedtls/sha256.h>
#include <esp_random.h>
#include <atomic>
#include <vector>
#include <algorithm>

SET_LOOP_TASK_STACK_SIZE(16384);
extern "C" bool btInUse() { return true; }
extern "C" bool bleInUse() { return true; }

// M5Stack AtomS3 Lite (ESP32-S3) built-in front button & WS2812 RGB LED
#define BTN_ATOM_GPIO 41
#define RGB_LED_GPIO  35

SemaphoreHandle_t ledMutex = nullptr;

void setAtomLed(uint8_t r, uint8_t g, uint8_t b) {
    static int lastR = -1, lastG = -1, lastB = -1;
    if (ledMutex && xSemaphoreTake(ledMutex, pdMS_TO_TICKS(10)) != pdTRUE) return;
    if ((int)r != lastR || (int)g != lastG || (int)b != lastB) {
        lastR = r; lastG = g; lastB = b;
#if defined(ESP_ARDUINO_VERSION_MAJOR) && ESP_ARDUINO_VERSION_MAJOR >= 3
        rgbLedWrite(RGB_LED_GPIO, r, g, b);
#else
        neopixelWrite(RGB_LED_GPIO, r, g, b);
#endif
    }
    if (ledMutex) xSemaphoreGive(ledMutex);
}

WebServer server(80);
Preferences prefs;

const char* hostname = "bldb";

inline unsigned long elapsedMs(unsigned long now, unsigned long past) {
    return (now >= past) ? (now - past) : 0UL;
}

SemaphoreHandle_t logMutex = nullptr;
inline void logWriteAtomic(const char* buf, int len) {
    if (len <= 0) return;
    size_t n = (len >= 256) ? 255 : (size_t)len;
    if (logMutex && xSemaphoreTake(logMutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        Serial.write((const uint8_t*)buf, n);
        xSemaphoreGive(logMutex);
    }
}
#define LOGF(fmt, ...) do { unsigned long _ms = millis(); char _logBuf[256]; int _n = snprintf(_logBuf, sizeof(_logBuf), "[%4lu.%03lu] " fmt, _ms / 1000UL, _ms % 1000UL, ##__VA_ARGS__); logWriteAtomic(_logBuf, _n); } while (0)
#define LOGLN(msg)     do { unsigned long _ms = millis(); char _logBuf[256]; int _n = snprintf(_logBuf, sizeof(_logBuf), "[%4lu.%03lu] %s\n", _ms / 1000UL, _ms % 1000UL, msg); logWriteAtomic(_logBuf, _n); } while (0)

struct SavedWiFi { String ssid; String pass; };
std::vector<SavedWiFi> wifiList;
size_t bgWifiIdx = 0;

bool mqtt_en = false;
String mqtt_ip = "";
int mqtt_port = 1883;
String mqtt_user = "";
String mqtt_pass = "";
String mqttClientId = "BLDB_000000";

#ifndef DEFAULT_AUTH_EN
#define DEFAULT_AUTH_EN 1
#endif
#ifndef DEFAULT_AUTH_USER
#define DEFAULT_AUTH_USER "admin"
#endif
#ifndef DEFAULT_AUTH_PASS
#define DEFAULT_AUTH_PASS "admin"
#endif

bool auth_en = (DEFAULT_AUTH_EN != 0);
String auth_user = DEFAULT_AUTH_USER;
String auth_salt = "";
String auth_hash = "";
String bootAuthSecret = "";
unsigned long lastFailedLoginMs = 0;

static const size_t MAX_USED_NONCES = 8;
char usedLoginNonces[MAX_USED_NONCES][68] = {};
size_t usedLoginNonceNext = 0;

struct AuthSession {
    char token[33];
    unsigned long lastSeenMs;
    bool active;
};
static const size_t MAX_AUTH_SESSIONS = 4;
static const unsigned long AUTH_SESSION_TTL_MS = 86400000UL;
AuthSession authSessions[MAX_AUTH_SESSIONS] = {};

String generateRandomHex(size_t byteLen) {
    if (byteLen > 32) byteLen = 32;
    uint8_t buf[32];
    esp_fill_random(buf, byteLen);
    char hex[65];
    for (size_t i = 0; i < byteLen; i++) {
        snprintf(hex + (i * 2), 3, "%02x", buf[i]);
    }
    hex[byteLen * 2] = '\0';
    return String(hex);
}

String sha256Hex(const String& input) {
    uint8_t digest[32];
    mbedtls_sha256((const unsigned char*)input.c_str(), input.length(), digest, 0);
    char hex[65];
    for (size_t i = 0; i < 32; i++) {
        snprintf(hex + (i * 2), 3, "%02x", digest[i]);
    }
    hex[64] = '\0';
    return String(hex);
}

bool constantTimeHexEquals(const String& a, const String& b) {
    if (a.length() == 0 || a.length() != b.length()) return false;
    uint8_t diff = 0;
    for (size_t i = 0; i < a.length(); i++) {
        char ca = a[i];
        char cb = b[i];
        if (ca >= 'A' && ca <= 'F') ca = (char)(ca + ('a' - 'A'));
        if (cb >= 'A' && cb <= 'F') cb = (char)(cb + ('a' - 'A'));
        diff |= (uint8_t)(ca ^ cb);
    }
    return diff == 0;
}

bool verifyAndConsumeSignedNonce(const String& nonce, unsigned long nowMs) {
    int dot1 = nonce.indexOf('.');
    if (dot1 != 16) return false;
    int dot2 = nonce.indexOf('.', dot1 + 1);
    if (dot2 <= dot1 + 1) return false;

    String rHex = nonce.substring(0, dot1);
    String tsStr = nonce.substring(dot1 + 1, dot2);
    String sig = nonce.substring(dot2 + 1);
    if (sig.length() != 32 || tsStr.length() > 10) return false;

    for (size_t i = 0; i < tsStr.length(); i++) {
        if (tsStr[i] < '0' || tsStr[i] > '9') return false;
    }

    unsigned long tsSec = strtoul(tsStr.c_str(), nullptr, 10);
    unsigned long nowSec = nowMs / 1000UL;
    if (nowSec < tsSec || (nowSec - tsSec) > 30UL) return false;

    String expectedSig = sha256Hex(bootAuthSecret + ":" + rHex + ":" + tsStr).substring(0, 32);
    if (!constantTimeHexEquals(sig, expectedSig)) return false;

    for (size_t i = 0; i < MAX_USED_NONCES; i++) {
        if (usedLoginNonces[i][0] != '\0' && constantTimeHexEquals(nonce, String(usedLoginNonces[i]))) {
            return false;
        }
    }

    strncpy(usedLoginNonces[usedLoginNonceNext], nonce.c_str(), sizeof(usedLoginNonces[0]) - 1);
    usedLoginNonces[usedLoginNonceNext][sizeof(usedLoginNonces[0]) - 1] = '\0';
    usedLoginNonceNext = (usedLoginNonceNext + 1) % MAX_USED_NONCES;
    return true;
}

void clearAllAuthSessions() {
    for (size_t i = 0; i < MAX_AUTH_SESSIONS; i++) {
        authSessions[i].active = false;
        authSessions[i].token[0] = '\0';
    }
}

String extractSessionCookie() {
    if (!server.hasHeader("Cookie")) return "";
    String cookieHdr = server.header("Cookie");
    int idx = cookieHdr.indexOf("bldb_sid=");
    if (idx < 0) return "";
    int valStart = idx + 9;
    int valEnd = cookieHdr.indexOf(';', valStart);
    String tok = (valEnd >= 0) ? cookieHdr.substring(valStart, valEnd) : cookieHdr.substring(valStart);
    tok.trim();
    return tok;
}

bool isSessionAuthenticated() {
    if (!auth_en) return true;
    String tok = extractSessionCookie();
    if (tok.length() != 32) return false;
    unsigned long now = millis();
    for (size_t i = 0; i < MAX_AUTH_SESSIONS; i++) {
        if (!authSessions[i].active) continue;
        if (elapsedMs(now, authSessions[i].lastSeenMs) > AUTH_SESSION_TTL_MS) {
            authSessions[i].active = false;
            continue;
        }
        if (constantTimeHexEquals(tok, String(authSessions[i].token))) {
            authSessions[i].lastSeenMs = now;
            return true;
        }
    }
    return false;
}

bool checkAuth(bool isApi = true) {
    if (isSessionAuthenticated()) return true;
    if (isApi) {
        server.send(401, "application/json", "{\"error\":\"unauthorized\"}");
    } else {
        server.sendHeader("Location", "/login", true);
        server.send(302, "text/plain", "");
    }
    return false;
}

WiFiClient espClient;
PubSubClient mqttClient(espClient);
unsigned long lastMqttReconnect = 0;
unsigned long lastMqttHeartbeatMs = 0;
volatile bool mqttTelemDirty = false;
bool mqttDevicesDirty = false;

static NimBLEUUID DUST_SVC_UUID("0000fe39-0000-1000-8000-00805f9b34fb");
static NimBLEUUID DUST_SVC_16((uint16_t)0xFE39);
static NimBLEUUID CHAR_WRITE_UUID("3734fe03-c847-11e6-9d9d-cec0c932ce01");
static NimBLEUUID CHAR_NOTIFY_UUID("3734fe02-c847-11e6-9d9d-cec0c932ce01");

NimBLEClient* pClient = nullptr;
NimBLERemoteCharacteristic* pWriteChar  = nullptr;
NimBLERemoteCharacteristic* pNotifyChar = nullptr;
static const uint8_t FMP_ROUTE_APP_TO_MAIN = 0x41;
static const uint8_t FMP_ROUTE_APP_TO_BLE  = 0x21;
static uint8_t fmpReqId = 1;
static uint8_t rxCobsBuf[256];
static size_t rxCobsLen = 0;

char pairedMacBuf[18] = {0};
portMUX_TYPE pairedMux = portMUX_INITIALIZER_UNLOCKED;
std::atomic<bool> pairedAdvSeenFlag{false};
std::atomic<bool> extLinkConnectedLog{false};
std::atomic<bool> extLinkDisconnectedFlag{false};

enum BleConnState { STATE_DISCONNECTED, STATE_CONNECTING, STATE_CONNECTED };
volatile BleConnState connState = STATE_DISCONNECTED;
volatile bool wifiScanInProgress = false;

String pairedMac = "";
volatile uint8_t pairedAddrType = 0;
volatile int pairedRssi = 0;
volatile unsigned long pairedLastSeenMs = 0;
unsigned long lastAutoReconnectTryMs = 0;
unsigned long lastExtConnectFailMs = 0;
unsigned long scannerStartedMs = 0;
volatile unsigned long lastBleActivityMs = 0;
String targetConnectMac = "";
uint8_t targetConnectType = 0;
String extFriendlyName = "Festool Extractor";
uint8_t evacSeconds = 4;
volatile bool requestConnect = false;
bool requestReboot = false;
unsigned long rebootTimer = 0;

bool postConnectActionPending = false;
unsigned long postConnectActionAtMs = 0;

struct ExtConnTaskParams {
    NimBLEClient* client;
    char mac[18];
    uint8_t addrType;
};
std::atomic<bool> extConnTaskRunning{false};
std::atomic<bool> extConnTaskDone{false};
std::atomic<bool> extConnTaskSuccess{false};
std::atomic<bool> extUnpairPending{false};
String extConnTaskMac = "";
uint8_t extConnTaskAddrType = 0;
uint8_t extConnTaskForcedType = 255;

struct ExtractorTelemetry {
    uint32_t motorRunSec;
    uint32_t operatingCycles;
    uint32_t filterRunSec;
    bool waterLevelActive;
    int temp1F;
    int temp2F;
    char faultText[32];
    char modelName[32];
    uint8_t mainSwMajor;
    uint8_t bleSwMajor;
    char mainFw[20];
    char bleFw[20];
};
ExtractorTelemetry extTelem = {
    0, 0, 0, true, 0, 0, "Healthy", "CT MINI MIDI I", 2, 10, "--", "--"
};
portMUX_TYPE telemMux = portMUX_INITIALIZER_UNLOCKED;

void resetExtractorTelemetry() {
    portENTER_CRITICAL(&telemMux);
    extTelem.motorRunSec = 0; extTelem.operatingCycles = 0; extTelem.filterRunSec = 0;
    extTelem.waterLevelActive = true; extTelem.temp1F = 0; extTelem.temp2F = 0;
    strncpy(extTelem.faultText, "Healthy", sizeof(extTelem.faultText));
    strncpy(extTelem.modelName, "CT MINI MIDI I", sizeof(extTelem.modelName));
    extTelem.mainSwMajor = 2; extTelem.bleSwMajor = 10;
    strncpy(extTelem.mainFw, "--", sizeof(extTelem.mainFw));
    strncpy(extTelem.bleFw, "--", sizeof(extTelem.bleFw));
    portEXIT_CRITICAL(&telemMux);
}

uint8_t inferRandomAddrType(const String& macStr, uint8_t currentType) {
    // Never overwrite a known BLE address type (0 = Public, 1 = Random) from NimBLE
    if (currentType == 0 || currentType == 1) return currentType;
    if (macStr.length() >= 2) {
        uint8_t firstByte = (uint8_t)strtoul(macStr.substring(0, 2).c_str(), nullptr, 16);
        // Only static random addresses (top two bits = 11 -> 0xC0) can be inferred from MAC;
        // 0x40..0x7F includes IEEE public OUIs such as Texas Instruments (78:C5:E5).
        if ((firstByte & 0xC0) == 0xC0) return 1;
    }
    return 0;
}

void setPairedMacState(const String& mac, uint8_t addrType) {
    pairedMac = mac; pairedAddrType = addrType;
    portENTER_CRITICAL(&pairedMux);
    strncpy(pairedMacBuf, mac.c_str(), sizeof(pairedMacBuf) - 1);
    pairedMacBuf[sizeof(pairedMacBuf) - 1] = '\0';
    portEXIT_CRITICAL(&pairedMux);
}

bool isExtractorPaired() {
    portENTER_CRITICAL(&pairedMux);
    bool has = (pairedMacBuf[0] != '\0');
    portEXIT_CRITICAL(&pairedMux);
    return has;
}

volatile bool telemPollRequested = false;
volatile bool telemAwaitingReply = false;
volatile bool initialTelemDone = false;
uint8_t telemPollStep = 0;
unsigned long connectedAtMs = 0;
unsigned long lastControlTxMs = 0;
unsigned long lastCtCtrlTxMs = 0;
unsigned long lastTelemStepMs = 0;

bool identifyActive = false;
unsigned long identifyStartMs = 0;

enum BtnNormPhase { BTN_IDLE = 0, BTN_HELD, BTN_WAIT_TAP };

struct MonitoredDevice {
    String address; String name; String advName; uint8_t speed; uint8_t btnType; String activeRaw;
    bool customNamed; bool toolActive; unsigned long toolLastSeen;
    bool isGatt; bool gattReady;
    bool toggleActive; unsigned long toggleActivatedMs;
    bool isHose; bool canAdv; bool canGatt;
    uint32_t matNum; uint8_t devCat;
    uint16_t wattsThr; int32_t lastWatts;
    BtnNormPhase btnPhase = BTN_IDLE;
    bool hoseHoldActivated = false;
    int16_t btnLastSeqByte = -1;
    unsigned long btnPressStartMs = 0;
    unsigned long btnLastPacketMs = 0;
    unsigned long btnReleaseMs = 0;
    uint8_t btnTapCount = 0;
    bool momActive = false;
    uint8_t momSpeed = 20;
    uint8_t liveSpeedOverride = 0;
    uint8_t addrType = 255;
    bool waitReleaseAfterPair = false;
    unsigned long pairHoldGuardUntilMs = 0;
    bool wakePreTriggered = false;
    unsigned long wakePreTriggerMs = 0;
    bool periodicBeacon = false;

    MonitoredDevice() = default;
    MonitoredDevice(const String& addr, const String& nm, const String& advNm, uint8_t spd, uint8_t bt,
                    const String& raw, bool cn, bool tAct, unsigned long tSeen, bool gatt, bool gReady,
                    bool togAct, unsigned long togMs, bool hose, bool cAdv,
                    uint32_t mat, uint8_t cat, uint16_t wThr, int32_t lWatts,
                    bool cGatt = false, uint8_t aType = 255, bool pBcn = false)
        : address(addr), name(nm), advName(advNm), speed(spd), btnType(bt), activeRaw(raw),
          customNamed(cn), toolActive(tAct), toolLastSeen(tSeen), isGatt(gatt), gattReady(gReady),
          toggleActive(togAct), toggleActivatedMs(togMs), isHose(hose),
          canAdv(cAdv), canGatt(cGatt || gatt), matNum(mat), devCat(cat), wattsThr(wThr), lastWatts(lWatts),
          addrType(aType), periodicBeacon(pBcn) {}
};
std::vector<MonitoredDevice> monitoredList;
bool needSaveMonitored = false;
unsigned long needSaveMonitoredAtMs = 0;

static const size_t MAX_MON_MAC_CACHE = 16;
char monMacCache[MAX_MON_MAC_CACHE][18];
volatile uint8_t monMacCacheCount = 0;
portMUX_TYPE monMacMux = portMUX_INITIALIZER_UNLOCKED;

void refreshMonMacCache() {
    portENTER_CRITICAL(&monMacMux);
    uint8_t cnt = 0;
    for (size_t i = 0; i < monitoredList.size() && cnt < MAX_MON_MAC_CACHE; i++) {
        strncpy(monMacCache[cnt], monitoredList[i].address.c_str(), 17);
        monMacCache[cnt][17] = '\0';
        cnt++;
    }
    monMacCacheCount = cnt;
    portEXIT_CRITICAL(&monMacMux);
}

String lookupFestoolModelByTnr(uint32_t tnr) {
    if (tnr == 0) return "";
    switch (tnr) {
        case 202479: return "BP 18 Li 5.2 ASI (202479)";
        case 202480: return "BP 18 Li 6.2 ASI (202480)";
        case 205034: return "BP 18 Li 4.0 HPC-ASI (205034)";
        case 205035: return "BP 18 Li 5.2 ASI (205035)";
        case 205036: return "BP 18 Li 3.1 Ergo-I (205036)";
        case 576933: return "BP 18 Li 4.0 HPC-ASI (576933)";
        case 577153: return "BP 18 Li 3.0 ERGO-I (577153)";
        case 577240: return "BP 18 Li 5.0 ASI (577240)";
        case 577658: return "BP 18 Li 4.0 HPC-ASI (577658)";
        case 577659: return "BP 18 Li 5.0 ASI (577659)";
        case 577660: return "BP 18 Li 8.0 HP-ASI (577660)";
        case 202097: return "CT-F I Remote (202097)";
        case 204842: return "CT-F I/M-Set (204842)";
        case 10029918: return "CT-F I Remote (10029918)";
        case 10030046: return "CT-F I Remote (10030046)";
        case 574830: return "CT SYS I (574830)";
        case 574832: return "CT MINI I (574832)";
        case 574833: return "CT MIDI I (574833)";
        case 576936: return "CTLC MINI I (576936)";
        case 576944: return "CTLC MIDI I (576944)";
        case 577065: return "CTMC MIDI I (577065)";
        case 575267: return "CTL 26 E (575267)";
        case 575279: return "CTL 36 E (575279)";
        case 574947: return "CT 26 E (574947)";
        case 574955: return "CT 36 E (574955)";
        case 574963: return "CT 48 E (574963)";
        default:     return "Festool " + String(tnr);
    }
}

inline bool isMonitoredConfiguring(const MonitoredDevice& m, unsigned long now = 0) {
    (void)now;
    return (m.isGatt && !m.gattReady);
}

struct BleEntry {
    String name; String advName; String address; uint8_t addrType; int rssi; bool isKnownDevice; String type;
    unsigned long lastSeen; int soc; int state; uint32_t matNum; int32_t watts; String rawData;
    bool canAdv;
    bool canGatt;
    unsigned long lastPrimaryAdvMs;
    uint8_t fastCadenceHits;
    uint8_t slowCadenceHits;
    uint8_t fastWakeHits;
};
static const size_t MAX_BLE_LIST_ENTRIES = 48;
std::vector<BleEntry> bleList;

enum ScanDevCat : uint8_t { CAT_OTHER = 0, CAT_EXTRACTOR, CAT_BATTERY, CAT_FESTOOL, CAT_TOOL_PLUG, CAT_BUTTON };
struct ScanEvent {
    char mac[18]; char name[36]; char raw[96];
    uint8_t addrType; int8_t rssi; uint8_t advType; int8_t soc; int8_t state;
    uint32_t matNum; int32_t watts;
    bool isKnown; uint8_t devCat; bool isGattBtnAdv; bool isBurstBtnAdv; bool isShellyPlug;
    bool isFestoolRemote; bool isConnectable; bool hasFlags06;
    int16_t btnSeq;
    unsigned long ts;
};
static const size_t SCAN_QUEUE_CAP = 64;
ScanEvent scanQueue[SCAN_QUEUE_CAP];
volatile size_t scanQueueHead = 0;
volatile size_t scanQueueTail = 0;
portMUX_TYPE scanQueueMux = portMUX_INITIALIZER_UNLOCKED;

void pushScanEvent(const ScanEvent& ev) {
    portENTER_CRITICAL(&scanQueueMux);
    size_t nextHead = (scanQueueHead + 1) % SCAN_QUEUE_CAP;
    if (nextHead == scanQueueTail) scanQueueTail = (scanQueueTail + 1) % SCAN_QUEUE_CAP;
    scanQueue[scanQueueHead] = ev;
    scanQueueHead = nextHead;
    portEXIT_CRITICAL(&scanQueueMux);
}

bool popScanEvent(ScanEvent& out) {
    bool has = false;
    portENTER_CRITICAL(&scanQueueMux);
    if (scanQueueTail != scanQueueHead) {
        out = scanQueue[scanQueueTail];
        scanQueueTail = (scanQueueTail + 1) % SCAN_QUEUE_CAP;
        has = true;
    }
    portEXIT_CRITICAL(&scanQueueMux);
    return has;
}

uint8_t currentPowerState = 3;
uint8_t currentSuctionPct = 60;
uint8_t activePresetSpeed = 60;
uint8_t webUiSpeedOverride = 0;

volatile bool mqttVacStateDirty = false;
volatile uint8_t mqttVacStateVal = 3;
volatile bool mqttVacSpeedDirty = false;
volatile uint8_t mqttVacSpeedVal = 60;
volatile bool externalShutoffPending = false;

bool demandDirty = false;
bool forceStopNow = false;
bool hoseClearActive = false;
unsigned long hoseClearTimer = 0;

bool hoseMomentaryActive = false;
String activeHoseMomMac = "";
uint8_t hoseMomTargetSpeed = 100;

bool hoseToggleDemandActive = false;
String activeHoseToggleMac = "";
uint8_t hoseToggleTargetSpeed = 100;

bool btnToggleDemandActive = false;
String activeBtnToggleMac = "";
uint8_t btnToggleTargetSpeed = 60;

bool toolBattDemandActive = false;
String activeToolBattMac = "";
uint8_t toolBattTargetSpeed = 60;

bool webUiDemandActive = false;
uint8_t userManualSpeed = 60;

static const unsigned long ADV_TOGGLE_TAP_RELEASE_MS  = 500UL;
static const unsigned long BTN_MOMENTARY_TAP_MAX_MS   = 380UL;
static const unsigned long BTN_GATT_TAP_WINDOW_MS     = 300UL;

void evaluateMotorDemand();
void setCoexScanner();
void onButtonPacket(const String& mac, uint8_t presetSpd, unsigned long now, bool isGatt = false, int16_t seqByte = -1);
void onButtonRelease(const String& mac, unsigned long now);
bool isAnyPrimaryDemandActive();
int findGattSlotByMac(const String& macStr);
const char* devCatToTypeStr(uint8_t cat);

MonitoredDevice* findMonitoredByMac(const String& mac) {
    for (auto& m : monitoredList) {
        if (m.address.equalsIgnoreCase(mac)) return &m;
    }
    return nullptr;
}

bool isAnyButtonGestureBusy() {
    for (const auto& m : monitoredList) {
        if (m.btnType > 0 && m.btnPhase != BTN_IDLE) return true;
    }
    return false;
}

void resetMonitoredButtonGesture(MonitoredDevice& m, bool clearLatched = true) {
    m.btnPhase = BTN_IDLE;
    m.btnTapCount = 0;
    m.hoseHoldActivated = false;
    m.wakePreTriggered = false;
    if (clearLatched) {
        m.btnLastSeqByte = -1;
    }
    m.momActive = false;
    m.liveSpeedOverride = 0;
    if (clearLatched) {
        m.toggleActive = false;
        m.toggleActivatedMs = 0;
        m.toolActive = false;
        m.toolLastSeen = 0;
    }
}

void resetAllMonitoredButtonGestures(bool clearLatched = true) {
    for (auto& m : monitoredList) {
        if (m.btnType > 0) resetMonitoredButtonGesture(m, clearLatched);
    }
}

void pruneStaleBleEntries(unsigned long now) {
    for (auto it = bleList.begin(); it != bleList.end(); ) {
        bool isPinned = (pairedMac.length() > 0 && it->address.equalsIgnoreCase(pairedMac));
        bool isMon = (findMonitoredByMac(it->address) != nullptr);
        if (!isPinned && !isMon && elapsedMs(now, it->lastSeen) > 300000UL) {
            it = bleList.erase(it);
        } else {
            ++it;
        }
    }
}

// ============================================================================
// Streamlined One-Way Monitoring-Only MQTT Telemetry (Topic Root: BLE_DB/#)
// ============================================================================
void mqttPublish(const String& topic, const String& payload, bool retained = false) {
    if (mqtt_en && mqttClient.connected()) {
        mqttClient.publish(topic.c_str(), payload.c_str(), retained);
    }
}

String macToTopicId(const String& mac) {
    String id = "";
    id.reserve(12);
    for (size_t i = 0; i < mac.length(); i++) {
        char c = mac[i];
        if (c == ':') continue;
        if (c >= 'A' && c <= 'Z') c = (char)(c + ('a' - 'A'));
        id += c;
    }
    return id;
}

uint8_t rssiToBars(int rssi) {
    if (rssi >= 0) return 0;
    if (rssi >= -60) return 4;
    if (rssi >= -72) return 3;
    if (rssi >= -84) return 2;
    return 1;
}

void publishBridgeTelemetry(unsigned long now) {
    if (!mqtt_en || !mqttClient.connected()) return;
    String ipStr = (WiFi.status() == WL_CONNECTED) ? WiFi.localIP().toString() : WiFi.softAPIP().toString();
    String ssidStr = (WiFi.status() == WL_CONNECTED) ? WiFi.SSID() : String("BLE_Dust_Bridge");
    int wifiRssi = (WiFi.status() == WL_CONNECTED) ? WiFi.RSSI() : 0;
    unsigned long upSec = now / 1000UL;

    mqttPublish("BLE_DB/bridge/status", "online", true);

    StaticJsonDocument<320> doc;
    doc["status"] = "online";
    doc["ip"] = ipStr;
    doc["hostname"] = hostname;
    doc["wifi_ssid"] = ssidStr;
    doc["wifi_rssi"] = wifiRssi;
    doc["uptime_sec"] = upSec;
    doc["free_heap"] = ESP.getFreeHeap();
    String out;
    serializeJson(doc, out);
    mqttPublish("BLE_DB/bridge/telemetry", out, true);
}

void publishExtractorTelemetry(unsigned long now) {
    if (!mqtt_en || !mqttClient.connected()) return;
    ExtractorTelemetry tSnap;
    portENTER_CRITICAL(&telemMux);
    tSnap = extTelem;
    portEXIT_CRITICAL(&telemMux);

    const char* connStr = (connState == STATE_CONNECTED) ? "CONNECTED" :
                          ((connState == STATE_CONNECTING) ? "CONNECTING" : "DISCONNECTED");
    const char* stateStr = (currentPowerState == 1) ? "ON" : "OFF";
    uint8_t liveOvr = 0;
    if (webUiDemandActive) liveOvr = webUiSpeedOverride;
    else if (hoseMomentaryActive) { MonitoredDevice* s = findMonitoredByMac(activeHoseMomMac); if (s) liveOvr = s->liveSpeedOverride; }
    else if (hoseToggleDemandActive) { MonitoredDevice* s = findMonitoredByMac(activeHoseToggleMac); if (s) liveOvr = s->liveSpeedOverride; }
    else if (btnToggleDemandActive) { MonitoredDevice* s = findMonitoredByMac(activeBtnToggleMac); if (s) liveOvr = s->liveSpeedOverride; }
    else if (toolBattDemandActive) { MonitoredDevice* s = findMonitoredByMac(activeToolBattMac); if (s) liveOvr = s->liveSpeedOverride; }

    unsigned long evacRemSec = 0;
    if (hoseClearActive && evacSeconds > 0) {
        unsigned long totalMs = (unsigned long)evacSeconds * 1000UL;
        unsigned long el = elapsedMs(now, hoseClearTimer);
        if (el < totalMs) evacRemSec = (totalMs - el + 999UL) / 1000UL;
    }

    uint32_t filterRemSec = (tSnap.filterRunSec < 180000UL) ? (180000UL - tSnap.filterRunSec) : 0UL;
    float motorHours = tSnap.motorRunSec / 3600.0f;
    float filterRemHours = filterRemSec / 3600.0f;
    uint8_t filterRemPct = (uint8_t)((filterRemSec * 100UL) / 180000UL);
    String fwCombined = "V " + String(tSnap.mainSwMajor) + "/" + String(tSnap.bleSwMajor) +
                        " (" + String(tSnap.mainFw) + " / " + String(tSnap.bleFw) + ")";

    mqttPublish("BLE_DB/extractor/connection", connStr, true);
    mqttPublish("BLE_DB/extractor/state", stateStr, true);
    mqttPublish("BLE_DB/extractor/speed", String(currentSuctionPct), true);

    StaticJsonDocument<768> doc;
    doc["connection"] = connStr;
    doc["paired"] = (pairedMac.length() > 0);
    doc["paired_mac"] = pairedMac;
    doc["name"] = extFriendlyName;
    doc["rssi"] = pairedRssi;
    doc["signal_bars"] = (connState == STATE_CONNECTED && pairedRssi < 0) ? rssiToBars(pairedRssi) : 0;
    doc["state"] = stateStr;
    doc["speed"] = currentSuctionPct;
    doc["preset_speed"] = activePresetSpeed;
    doc["override_speed"] = liveOvr;
    doc["evac_active"] = hoseClearActive;
    doc["evac_sec"] = evacSeconds;
    doc["evac_rem_sec"] = evacRemSec;
    doc["motor_run_sec"] = tSnap.motorRunSec;
    doc["motor_hours"] = motorHours;
    doc["cycles"] = tSnap.operatingCycles;
    doc["filter_run_sec"] = tSnap.filterRunSec;
    doc["filter_remaining_sec"] = filterRemSec;
    doc["filter_remaining_hours"] = filterRemHours;
    doc["filter_remaining_pct"] = filterRemPct;
    doc["water_level_protection"] = tSnap.waterLevelActive ? "Active" : "Inactive";
    doc["temp1_f"] = tSnap.temp1F;
    doc["temp2_f"] = tSnap.temp2F;
    doc["faults"] = tSnap.faultText;
    doc["model"] = tSnap.modelName;
    doc["firmware"] = fwCombined;

    String out;
    serializeJson(doc, out);
    mqttPublish("BLE_DB/extractor/telemetry", out, true);
}

void publishDevicesTelemetry(unsigned long now) {
    if (!mqtt_en || !mqttClient.connected()) return;

    for (const auto& m : monitoredList) {
        String id = macToTopicId(m.address);
        if (id.length() == 0) continue;

        const BleEntry* liveBle = nullptr;
        for (const auto& b : bleList) {
            if (b.address.equalsIgnoreCase(m.address)) { liveBle = &b; break; }
        }

        int gSlot = m.isGatt ? findGattSlotByMac(m.address) : -1;
        bool gattLinked = (gSlot >= 0);
        bool hasFreshRssi = (liveBle && liveBle->rssi < 0 && (liveBle->lastSeen == 0 || elapsedMs(now, liveBle->lastSeen) <= 300000UL));
        int effRssi = hasFreshRssi ? liveBle->rssi : 0;
        uint8_t bars = hasFreshRssi ? rssiToBars(effRssi) : 0;
        unsigned long seenAgeSec = (liveBle && liveBle->lastSeen > 0) ? (elapsedMs(now, liveBle->lastSeen) / 1000UL) : 999999UL;

        uint32_t effMat = (m.matNum > 0) ? m.matNum : (liveBle ? liveBle->matNum : 0);
        String effModel = lookupFestoolModelByTnr(effMat);
        String effType = (m.btnType > 0) ? "Button" : devCatToTypeStr(m.devCat);
        if (effType == "Other" && liveBle && liveBle->type.length() > 0 && liveBle->type != "Other") {
            effType = liveBle->type;
        }
        int effSoc = liveBle ? liveBle->soc : -1;
        int32_t effWatts = (liveBle && liveBle->watts >= 0) ? liveBle->watts : m.lastWatts;
        bool isActive = (m.btnType > 0)
            ? (m.toggleActive || m.momActive || m.btnPhase == BTN_HELD)
            : m.toolActive;

        StaticJsonDocument<512> doc;
        doc["mac"] = m.address;
        doc["name"] = m.name;
        if (m.advName.length() > 0) doc["adv_name"] = m.advName;
        if (effModel.length() > 0) doc["model"] = effModel;
        if (effMat > 0) doc["mat_num"] = effMat;
        doc["type"] = effType;
        doc["active"] = isActive;
        doc["speed"] = m.speed;
        doc["live_speed_override"] = m.liveSpeedOverride;
        doc["rssi"] = effRssi;
        doc["signal_bars"] = bars;
        doc["last_seen_age_sec"] = seenAgeSec;
        if (effSoc >= 0) doc["battery_pct"] = effSoc;
        if (effType == "Tool Plug") {
            doc["watts"] = hasFreshRssi && effWatts >= 0 ? effWatts : -1;
            doc["plug_status"] = hasFreshRssi ? (isActive ? "ON" : "IDLE") : "OFF";
            doc["watts_threshold"] = m.wattsThr;
        }
        if (m.btnType > 0) {
            doc["connection_type"] = m.isGatt ? "GATT" : "ADV";
            doc["gatt_connected"] = gattLinked;
            doc["hose_mode"] = (m.isGatt && m.isHose);
            doc["toggle_active"] = m.toggleActive;
            doc["momentary_active"] = m.momActive;
        }

        String out;
        serializeJson(doc, out);
        mqttPublish("BLE_DB/devices/" + id + "/telemetry", out, true);
    }

    for (const auto& b : bleList) {
        if (!b.isKnownDevice || elapsedMs(now, b.lastSeen) > 60000UL) continue;
        if (pairedMac.length() > 0 && b.address.equalsIgnoreCase(pairedMac)) continue;
        if (findMonitoredByMac(b.address) != nullptr) continue;
        if (b.type == "Extractor" || b.type == "Festool") continue;

        String id = macToTopicId(b.address);
        if (id.length() == 0) continue;

        StaticJsonDocument<320> doc;
        doc["mac"] = b.address;
        doc["name"] = b.name;
        doc["type"] = b.type;
        doc["rssi"] = b.rssi;
        doc["signal_bars"] = rssiToBars(b.rssi);
        doc["last_seen_age_sec"] = elapsedMs(now, b.lastSeen) / 1000UL;
        if (b.matNum > 0) doc["mat_num"] = b.matNum;
        if (b.soc >= 0) doc["battery_pct"] = b.soc;
        if (b.watts >= 0) doc["watts"] = b.watts;
        if (b.state >= 0) doc["active"] = (b.state == 1);

        String out;
        serializeJson(doc, out);
        mqttPublish("BLE_DB/discovered/" + id + "/telemetry", out, false);
    }
}

void publishAllMqttTelemetry(unsigned long now) {
    if (!mqtt_en || !mqttClient.connected()) return;
    lastMqttHeartbeatMs = now;
    publishBridgeTelemetry(now);
    publishExtractorTelemetry(now);
    publishDevicesTelemetry(now);
}

void syncButtonDemandsFromMonitored() {
    bool anyHoseMom = false;
    String bestHoseMomMac = "";
    uint8_t bestHoseMomSpd = 100;
    unsigned long newestHoseMomTs = 0;

    bool anyHoseToggle = false;
    String bestHoseMac = "";
    uint8_t bestHoseSpd = 100;
    unsigned long newestHoseTs = 0;

    bool anyToolToggle = false;
    String bestToolMac = "";
    uint8_t bestToolSpd = 20;
    unsigned long newestToolTs = 0;

    for (const auto& m : monitoredList) {
        if (m.btnType == 0) continue;
        bool isHoseGatt = (m.isHose && m.isGatt);
        if (m.momActive && isHoseGatt) {
            if (!anyHoseMom || m.btnPressStartMs >= newestHoseMomTs) {
                anyHoseMom = true; newestHoseMomTs = m.btnPressStartMs; bestHoseMomMac = m.address; bestHoseMomSpd = m.momSpeed;
            }
        }
        if (m.toggleActive) {
            if (isHoseGatt) {
                if (!anyHoseToggle || m.toggleActivatedMs >= newestHoseTs) {
                    anyHoseToggle = true; newestHoseTs = m.toggleActivatedMs; bestHoseMac = m.address; bestHoseSpd = m.speed;
                }
            } else {
                if (!anyToolToggle || m.speed > bestToolSpd || (m.speed == bestToolSpd && m.toggleActivatedMs >= newestToolTs)) {
                    anyToolToggle = true; newestToolTs = m.toggleActivatedMs; bestToolMac = m.address; bestToolSpd = m.speed;
                }
            }
        }
    }

    hoseMomentaryActive = anyHoseMom;
    activeHoseMomMac = bestHoseMomMac;
    if (anyHoseMom) hoseMomTargetSpeed = bestHoseMomSpd;

    hoseToggleDemandActive = anyHoseToggle;
    activeHoseToggleMac = bestHoseMac;
    if (anyHoseToggle) hoseToggleTargetSpeed = bestHoseSpd;

    btnToggleDemandActive = anyToolToggle;
    activeBtnToggleMac = bestToolMac;
    if (anyToolToggle) btnToggleTargetSpeed = bestToolSpd;
}

void syncToolBattDemandFromMonitored(unsigned long now) {
    bool anyTool = false;
    String bestMac = "";
    uint8_t bestSpd = 20;
    unsigned long bestTs = 0;

    for (const auto& m : monitoredList) {
        if (m.btnType == 0 && m.toolActive && (m.toolLastSeen == 0 || elapsedMs(now, m.toolLastSeen) < 8000UL)) {
            if (!anyTool || m.speed > bestSpd || (m.speed == bestSpd && m.toolLastSeen >= bestTs)) {
                anyTool = true;
                bestMac = m.address;
                bestSpd = m.speed;
                bestTs = m.toolLastSeen;
            }
        }
    }

    if (anyTool) {
        if (!toolBattDemandActive || !activeToolBattMac.equalsIgnoreCase(bestMac) || toolBattTargetSpeed != bestSpd) {
            demandDirty = true;
        }
        toolBattDemandActive = true;
        activeToolBattMac = bestMac;
        toolBattTargetSpeed = bestSpd;
    } else if (toolBattDemandActive) {
        toolBattDemandActive = false;
        activeToolBattMac = "";
        demandDirty = true;
    }
}

void clearAllButtonToggles() {
    resetAllMonitoredButtonGestures(true);
    syncButtonDemandsFromMonitored();
}

void clearOtherHoseButtonStates(const String& activeMac) {
    for (auto& other : monitoredList) {
        if (other.btnType > 0 && other.isHose && !other.address.equalsIgnoreCase(activeMac)) {
            other.toggleActive = false;
            other.toggleActivatedMs = 0;
            other.momActive = false;
            other.liveSpeedOverride = 0;
        }
    }
}

uint16_t fmpCrc16(const uint8_t* data, size_t len) {
    uint16_t crc = 0x0000;
    for (size_t i = 0; i < len; i++) {
        crc ^= data[i];
        for (int b = 0; b < 8; b++) crc = (crc & 0x0001) ? ((crc >> 1) ^ 0xA001) : (crc >> 1);
    }
    return crc;
}

size_t cobsEncode(const uint8_t* src, size_t len, uint8_t* dst) {
    size_t readIdx = 0, writeIdx = 1, codeIdx = 0;
    uint8_t code = 1;
    while (readIdx < len) {
        if (src[readIdx] == 0x00) {
            dst[codeIdx] = code; code = 1; codeIdx = writeIdx++; readIdx++;
        } else {
            dst[writeIdx++] = src[readIdx++]; code++;
            if (code == 0xFF) { dst[codeIdx] = code; code = 1; codeIdx = writeIdx++; }
        }
    }
    dst[codeIdx] = code; dst[writeIdx++] = 0x00;
    return writeIdx;
}

size_t cobsDecode(const uint8_t* src, size_t len, uint8_t* dst) {
    size_t readIdx = 0, writeIdx = 0;
    while (readIdx < len) {
        uint8_t code = src[readIdx++];
        if (code == 0) break;
        for (uint8_t i = 1; i < code; i++) {
            if (readIdx >= len) return 0;
            dst[writeIdx++] = src[readIdx++];
        }
        if (code < 0xFF && readIdx < len) dst[writeIdx++] = 0x00;
    }
    return writeIdx;
}

bool pbReadVarint(const uint8_t* buf, size_t len, size_t& pos, uint32_t& val) {
    val = 0; uint8_t shift = 0;
    while (pos < len) {
        uint8_t b = buf[pos++];
        val |= (uint32_t)(b & 0x7F) << shift;
        if (!(b & 0x80)) return true;
        shift += 7;
        if (shift > 28) return false;
    }
    return false;
}

bool pbSkipField(const uint8_t* buf, size_t len, size_t& pos, uint8_t wt) {
    if (wt == 0) { uint32_t dummy; return pbReadVarint(buf, len, pos, dummy); }
    if (wt == 1) { if (pos + 8 > len) return false; pos += 8; return true; }
    if (wt == 2) { uint32_t l; if (!pbReadVarint(buf, len, pos, l) || pos + l > len) return false; pos += l; return true; }
    if (wt == 5) { if (pos + 4 > len) return false; pos += 4; return true; }
    return false;
}

void parseCtControlFields(const uint8_t* buf, size_t start, size_t end, const char* tagLabel) {
    unsigned long now = millis();
    bool isTelem = (strcmp(tagLabel, "FMP TELEM") == 0);
    bool isEvent = (strcmp(tagLabel, "FMP EVENT") == 0);
    bool recentCtrl = (lastCtCtrlTxMs > 0 && elapsedMs(now, lastCtCtrlTxMs) < 800UL);
    size_t p = start;
    while (p < end) {
        uint32_t tag;
        if (!pbReadVarint(buf, end, p, tag)) break;
        uint32_t field = tag >> 3; uint8_t wt = tag & 0x07;
        if (field == 1 && wt == 0) {
            uint32_t pwr;
            if (pbReadVarint(buf, end, p, pwr) && (pwr == 1 || pwr == 2 || pwr == 3)) {
                if (isTelem && recentCtrl) {
                    LOGF("[%s] Ignored stale Vacuum Power = %s (%u)\n", tagLabel, (pwr == 1) ? "ON" : "OFF", (unsigned)pwr);
                } else {
                    currentPowerState = (uint8_t)pwr;
                    mqttVacStateVal = (uint8_t)pwr;
                    mqttVacStateDirty = true;
                    LOGF("[%s] Vacuum Power = %s (%u)\n", tagLabel, (pwr == 1) ? "ON" : "OFF", (unsigned)pwr);
                    if (isEvent && pwr != 1 && !recentCtrl) {
                        externalShutoffPending = true;
                    }
                }
            }
        } else if (field == 4 && wt == 2) {
            uint32_t vLen;
            if (!pbReadVarint(buf, end, p, vLen) || p + vLen > end) break;
            size_t subEnd = p + vLen;
            while (p < subEnd) {
                uint32_t stag;
                if (!pbReadVarint(buf, subEnd, p, stag)) break;
                uint32_t sf = stag >> 3; uint8_t swt = stag & 0x07; uint32_t sval;
                if (swt == 0 && pbReadVarint(buf, subEnd, p, sval)) {
                    if (sf == 1 && sval >= 20 && sval <= 100) {
                        if (isTelem && recentCtrl) LOGF("[%s] Ignored stale Vacuum Suction = %u%%\n", tagLabel, (unsigned)sval);
                        else {
                            currentSuctionPct = (uint8_t)sval;
                            mqttVacSpeedVal = (uint8_t)sval;
                            mqttVacSpeedDirty = true;
                            LOGF("[%s] Vacuum Suction = %u%%\n", tagLabel, (unsigned)sval);
                        }
                    }
                } else if (!pbSkipField(buf, subEnd, p, swt)) break;
            }
            p = subEnd;
        } else if (!pbSkipField(buf, end, p, wt)) break;
    }
}

void parseTelemetryBlock6A(const uint8_t* buf, size_t len) {
    size_t p = 0;
    while (p < len) {
        uint32_t tag; if (!pbReadVarint(buf, len, p, tag)) break;
        uint32_t f = tag >> 3; uint8_t wt = tag & 0x07;
        if (f == 2 && wt == 2) {
            uint32_t l; if (!pbReadVarint(buf, len, p, l) || p + l > len) break;
            size_t end = p + l;
            while (p < end) {
                uint32_t st; if (!pbReadVarint(buf, end, p, st)) break;
                uint32_t sf = st >> 3; uint8_t swt = st & 0x07;
                if (sf == 1 && swt == 0) { uint32_t cyc; if (pbReadVarint(buf, end, p, cyc) && cyc > 0) { portENTER_CRITICAL(&telemMux); extTelem.operatingCycles = cyc; portEXIT_CRITICAL(&telemMux); mqttTelemDirty = true; } }
                else if (!pbSkipField(buf, end, p, swt)) break;
            }
            p = end;
        } else if (!pbSkipField(buf, len, p, wt)) break;
    }
}

void parseTelemetryBlock72(const uint8_t* buf, size_t len) {
    size_t p = 0;
    while (p < len) {
        uint32_t tag; if (!pbReadVarint(buf, len, p, tag)) break;
        uint32_t f = tag >> 3; uint8_t wt = tag & 0x07;
        if (wt == 2) {
            uint32_t l; if (!pbReadVarint(buf, len, p, l) || p + l > len) break;
            size_t end = p + l;
            while (p < end) {
                uint32_t st; if (!pbReadVarint(buf, end, p, st)) break;
                uint32_t sf = st >> 3; uint8_t swt = st & 0x07; uint32_t sval;
                if (sf == 1 && swt == 0 && pbReadVarint(buf, end, p, sval)) {
                    portENTER_CRITICAL(&telemMux);
                    if (f == 8) { extTelem.motorRunSec = sval; if (extTelem.filterRunSec == 0) extTelem.filterRunSec = sval; }
                    else if (f == 10 && sval > 0 && sval < 250) extTelem.temp1F = (int)sval;
                    else if (f == 12 && sval > 0 && sval < 250) extTelem.temp2F = (int)sval;
                    portEXIT_CRITICAL(&telemMux);
                    mqttTelemDirty = true;
                } else if (!pbSkipField(buf, end, p, swt)) break;
            }
            p = end;
        } else if (!pbSkipField(buf, len, p, wt)) break;
    }
}

void parseTelemetryResponse33(const uint8_t* buf, size_t len) {
    size_t p = 0;
    while (p < len) {
        uint32_t tag; if (!pbReadVarint(buf, len, p, tag)) break;
        uint32_t f = tag >> 3; uint8_t wt = tag & 0x07;
        if (wt == 2) {
            uint32_t l; if (!pbReadVarint(buf, len, p, l) || p + l > len) break;
            if (f == 13) parseTelemetryBlock6A(buf + p, l);
            else if (f == 14) parseTelemetryBlock72(buf + p, l);
            p += l;
        } else if (!pbSkipField(buf, len, p, wt)) break;
    }
}

void parseSettingsResponse12(const uint8_t* buf, size_t len) {
    size_t p = 0;
    while (p < len) {
        uint32_t tag; if (!pbReadVarint(buf, len, p, tag)) break;
        uint32_t f = tag >> 3; uint8_t wt = tag & 0x07;
        if (wt == 2) {
            uint32_t l; if (!pbReadVarint(buf, len, p, l) || p + l > len) break;
            size_t end = p + l;
            if (f == 3) {
                while (p < end) {
                    uint32_t st; if (!pbReadVarint(buf, end, p, st)) break;
                    uint32_t sf = st >> 3; uint8_t swt = st & 0x07; uint32_t sval;
                    if (sf == 1 && swt == 0 && pbReadVarint(buf, end, p, sval)) {
                        portENTER_CRITICAL(&telemMux);
                        extTelem.filterRunSec = sval;
                        if (extTelem.motorRunSec == 0) extTelem.motorRunSec = sval;
                        portEXIT_CRITICAL(&telemMux);
                        mqttTelemDirty = true;
                    } else if (!pbSkipField(buf, end, p, swt)) break;
                }
            }
            p = end;
        } else if (!pbSkipField(buf, len, p, wt)) break;
    }
}

void parseFirmwareResponse13(const uint8_t* buf, size_t len, uint8_t srcNode) {
    size_t p = 0;
    while (p < len) {
        uint32_t tag; if (!pbReadVarint(buf, len, p, tag)) break;
        uint32_t f = tag >> 3; uint8_t wt = tag & 0x07;
        if (f == 2 && wt == 0) {
            uint32_t swMaj;
            if (pbReadVarint(buf, len, p, swMaj) && swMaj > 0) {
                portENTER_CRITICAL(&telemMux);
                if (srcNode == 0x12) extTelem.mainSwMajor = (uint8_t)swMaj;
                else if (srcNode == 0x14) extTelem.bleSwMajor = (uint8_t)swMaj;
                portEXIT_CRITICAL(&telemMux);
                mqttTelemDirty = true;
            }
        } else if (f == 10 && wt == 2) {
            uint32_t l; if (!pbReadVarint(buf, len, p, l) || p + l > len) break;
            size_t end = p + l;
            uint32_t maj = 0, minV = 0, patch = 0;
            char hashBuf[20] = {0}; size_t hLen = 0;
            while (p < end) {
                uint32_t st; if (!pbReadVarint(buf, end, p, st)) break;
                uint32_t sf = st >> 3; uint8_t swt = st & 0x07;
                if (swt == 0) {
                    uint32_t sv; if (!pbReadVarint(buf, end, p, sv)) break;
                    if (sf == 2) maj = sv; else if (sf == 3) minV = sv; else if (sf == 4) patch = sv;
                } else if (sf == 7 && swt == 2) {
                    uint32_t sl; if (!pbReadVarint(buf, end, p, sl) || p + sl > end) break;
                    hLen = 0;
                    for (uint32_t k = 0; k < sl && hLen + 1 < sizeof(hashBuf); k++) hashBuf[hLen++] = (char)buf[p + k];
                    hashBuf[hLen] = '\0';
                    p += sl;
                } else if (!pbSkipField(buf, end, p, swt)) break;
            }
            portENTER_CRITICAL(&telemMux);
            if (srcNode == 0x12 && maj > 0) snprintf(extTelem.mainFw, sizeof(extTelem.mainFw), "%u.%u.%u", (unsigned)maj, (unsigned)minV, (unsigned)patch);
            else if (srcNode == 0x14 && hLen > 0) strncpy(extTelem.bleFw, hashBuf, sizeof(extTelem.bleFw));
            portEXIT_CRITICAL(&telemMux);
            mqttTelemDirty = true;
            p = end;
        } else if (!pbSkipField(buf, len, p, wt)) break;
    }
}

void parseDeviceInfoResponse5(const uint8_t* buf, size_t len) {
    size_t p = 0;
    while (p < len) {
        uint32_t tag; if (!pbReadVarint(buf, len, p, tag)) break;
        uint32_t f = tag >> 3; uint8_t wt = tag & 0x07;
        if (f == 25 && wt == 2) {
            uint32_t l; if (!pbReadVarint(buf, len, p, l) || p + l > len) break;
            char mdl[32] = {0}; size_t mLen = 0;
            for (uint32_t k = 0; k < l && mLen + 1 < sizeof(mdl); k++) { if (buf[p + k] >= 32 && buf[p + k] < 127) mdl[mLen++] = (char)buf[p + k]; }
            mdl[mLen] = '\0';
            if (mLen > 0) { portENTER_CRITICAL(&telemMux); strncpy(extTelem.modelName, mdl, sizeof(extTelem.modelName)); portEXIT_CRITICAL(&telemMux); mqttTelemDirty = true; }
            p += l;
        } else if (!pbSkipField(buf, len, p, wt)) break;
    }
}

void parseIncomingFmpFrame(const uint8_t* dec, size_t len) {
    if (len < 6) return;
    uint8_t routeByte = dec[1];
    size_t payloadEnd = len - 2, p = 2;
    while (p < payloadEnd) {
        uint32_t topTag; if (!pbReadVarint(dec, payloadEnd, p, topTag)) break;
        uint32_t topField = topTag >> 3; uint8_t topWt = topTag & 0x07;
        if (topWt != 2) { if (!pbSkipField(dec, payloadEnd, p, topWt)) break; continue; }
        uint32_t msgLen; if (!pbReadVarint(dec, payloadEnd, p, msgLen) || p + msgLen > payloadEnd) break;
        size_t msgEnd = p + msgLen;
        if (topField == 4) {
            telemAwaitingReply = false;
            while (p < msgEnd) {
                uint32_t rTag; if (!pbReadVarint(dec, msgEnd, p, rTag)) break;
                uint32_t rField = rTag >> 3; uint8_t rWt = rTag & 0x07;
                if (rWt == 2) {
                    uint32_t subLen; if (!pbReadVarint(dec, msgEnd, p, subLen) || p + subLen > msgEnd) break;
                    if (rField == 21) parseCtControlFields(dec, p, p + subLen, "FMP TELEM");
                    else if (rField == 37) { if (subLen >= 2 && dec[p] == 0x08) { portENTER_CRITICAL(&telemMux); extTelem.waterLevelActive = (dec[p + 1] == 2); portEXIT_CRITICAL(&telemMux); mqttTelemDirty = true; } }
                    else if (rField == 33) parseTelemetryResponse33(dec + p, subLen);
                    else if (rField == 12) parseSettingsResponse12(dec + p, subLen);
                    else if (rField == 34) { portENTER_CRITICAL(&telemMux); if (subLen == 0) strncpy(extTelem.faultText, "Healthy", sizeof(extTelem.faultText)); else snprintf(extTelem.faultText, sizeof(extTelem.faultText), "Warning (Code %u)", (unsigned)dec[p]); portEXIT_CRITICAL(&telemMux); mqttTelemDirty = true; }
                    else if (rField == 13) parseFirmwareResponse13(dec + p, subLen, routeByte);
                    else if (rField == 5) parseDeviceInfoResponse5(dec + p, subLen);
                    p += subLen;
                } else if (!pbSkipField(dec, msgEnd, p, rWt)) break;
            }
        } else if (topField == 5) {
            while (p < msgEnd) {
                uint32_t eTag; if (!pbReadVarint(dec, msgEnd, p, eTag)) break;
                uint32_t eField = eTag >> 3; uint8_t eWt = eTag & 0x07;
                if (eWt == 2) {
                    uint32_t subLen; if (!pbReadVarint(dec, msgEnd, p, subLen) || p + subLen > msgEnd) break;
                    if (eField == 7) parseCtControlFields(dec, p, p + subLen, "FMP EVENT");
                    else if (eField == 16 && subLen >= 2) { if (dec[p] == 0x08 && dec[p + 1] == 0x02) { portENTER_CRITICAL(&telemMux); extTelem.waterLevelActive = true; portEXIT_CRITICAL(&telemMux); mqttTelemDirty = true; } }
                    p += subLen;
                } else if (!pbSkipField(dec, msgEnd, p, eWt)) break;
            }
        }
        p = msgEnd;
    }
}

void onFe02Notify(NimBLERemoteCharacteristic* pChr, uint8_t* pData, size_t length, bool isNotify) {
    (void)pChr; (void)isNotify;
    for (size_t i = 0; i < length; i++) {
        uint8_t b = pData[i];
        if (b == 0x00) {
            if (rxCobsLen > 0) {
                uint8_t decoded[256];
                size_t decLen = cobsDecode(rxCobsBuf, rxCobsLen, decoded);
                if (decLen >= 4) {
                    uint16_t calcCrc = fmpCrc16(decoded, decLen - 2);
                    uint16_t pktCrc  = ((uint16_t)decoded[decLen - 2] << 8) | decoded[decLen - 1];
                    if (calcCrc == pktCrc) { lastBleActivityMs = millis(); parseIncomingFmpFrame(decoded, decLen); }
                }
                rxCobsLen = 0;
            }
        } else if (rxCobsLen < sizeof(rxCobsBuf)) rxCobsBuf[rxCobsLen++] = b;
        else rxCobsLen = 0;
    }
}

bool sendFmpRawPayloadTo(uint8_t routeByte, const uint8_t* protoBytes, size_t protoLen) {
    if (connState != STATE_CONNECTED || !pClient || !pClient->isConnected() || !pWriteChar) return false;
    uint8_t raw[64]; size_t idx = 0;
    raw[idx++] = 0x02; raw[idx++] = routeByte;
    memcpy(raw + idx, protoBytes, protoLen); idx += protoLen;
    uint16_t crc = fmpCrc16(raw, idx);
    raw[idx++] = (crc >> 8) & 0xFF; raw[idx++] = crc & 0xFF;
    uint8_t frame[72]; size_t frameLen = cobsEncode(raw, idx, frame);
    bool useResp = !pWriteChar->canWriteNoResponse();
    for (size_t off = 0; off < frameLen; off += 20) {
        size_t chunkLen = (frameLen - off > 20) ? 20 : (frameLen - off);
        if (!pWriteChar->writeValue(frame + off, chunkLen, useResp)) return false;
        if (off + 20 < frameLen) delay(15);
    }
    lastBleActivityMs = millis();
    return true;
}

bool sendFmpRawPayload(const uint8_t* protoBytes, size_t protoLen) {
    return sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, protoBytes, protoLen);
}

bool sendFmpCtControl(uint8_t powerState, uint8_t suctionPct = 0, uint8_t origin = 1) {
    uint8_t ct[16]; size_t c = 0;
    if (powerState > 0) { ct[c++] = 0x08; ct[c++] = powerState; }
    if (suctionPct >= 20 && suctionPct <= 100) { ct[c++] = 0x22; ct[c++] = 0x02; ct[c++] = 0x08; ct[c++] = suctionPct; }
    if (origin > 0) { ct[c++] = 0x30; ct[c++] = origin; }
    uint8_t reqId = fmpReqId++; if (fmpReqId == 0 || fmpReqId > 127) fmpReqId = 1;
    uint8_t proto[32]; size_t p = 0;
    proto[p++] = 0x1A; proto[p++] = (uint8_t)(5 + c); proto[p++] = 0x08; proto[p++] = reqId;
    proto[p++] = 0xF2; proto[p++] = 0x03; proto[p++] = (uint8_t)c;
    memcpy(proto + p, ct, c); p += c;
    unsigned long txNow = millis(); lastControlTxMs = txNow; lastCtCtrlTxMs = txNow;
    return sendFmpRawPayload(proto, p);
}

bool sendFmpIdentify(bool enable = true) {
    uint8_t reqId = fmpReqId++; if (fmpReqId == 0 || fmpReqId > 127) fmpReqId = 1;
    lastControlTxMs = millis();
    if (enable) {
        identifyActive = true; identifyStartMs = millis();
        uint8_t proto[] = { 0x1A, 0x09, 0x08, reqId, 0xD2, 0x02, 0x04, 0x08, 0x01, 0x10, 0x0A };
        return sendFmpRawPayload(proto, sizeof(proto));
    } else {
        identifyActive = false;
        uint8_t proto[] = { 0x1A, 0x05, 0x08, reqId, 0xD2, 0x02, 0x00 };
        return sendFmpRawPayload(proto, sizeof(proto));
    }
}

void sendFmpHandshake() {
    uint8_t reqId = fmpReqId++; if (fmpReqId == 0 || fmpReqId > 127) fmpReqId = 1;
    uint8_t proto[] = { 0x1A, 0x05, 0x08, reqId, 0xAA, 0x01, 0x00 };
    sendFmpRawPayload(proto, sizeof(proto));
}

void startTelemetryPoll(bool fullRefresh = true) {
    if (connState != STATE_CONNECTED) return;
    telemPollRequested = true; telemAwaitingReply = false;
    telemPollStep = fullRefresh ? 1 : 4; lastTelemStepMs = 0;
}

void serviceTelemetryPoll(unsigned long now) {
    if (!telemPollRequested) return;
    if (isAnyPrimaryDemandActive() || hoseClearActive || demandDirty || isAnyButtonGestureBusy()) return;
    if (!telemPollRequested || connState != STATE_CONNECTED) { telemPollRequested = false; telemAwaitingReply = false; return; }
    if (demandDirty || hoseClearActive || (elapsedMs(now, lastControlTxMs) < 1500UL)) return;
    if (telemAwaitingReply) { if (elapsedMs(now, lastTelemStepMs) < 1200UL) return; }
    else { if (elapsedMs(now, lastTelemStepMs) < 450UL) return; }
    lastTelemStepMs = now; telemAwaitingReply = true;
    uint8_t reqId = fmpReqId++; if (fmpReqId == 0 || fmpReqId > 127) fmpReqId = 1;
    switch (telemPollStep) {
        case 1: { uint8_t p[] = { 0x1A, 0x04, 0x08, reqId, 0x6A, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, p, sizeof(p)); break; }
        case 2: { uint8_t p[] = { 0x1A, 0x04, 0x08, reqId, 0x6A, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_BLE, p, sizeof(p)); break; }
        case 3: { uint8_t p[] = { 0x1A, 0x04, 0x08, reqId, 0x2A, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_BLE, p, sizeof(p)); break; }
        case 4: { uint8_t p[] = { 0x1A, 0x09, 0x08, reqId, 0x8A, 0x02, 0x04, 0x0A, 0x00, 0x72, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, p, sizeof(p)); break; }
        case 5: { uint8_t p[] = { 0x1A, 0x09, 0x08, reqId, 0x8A, 0x02, 0x04, 0x0A, 0x00, 0x6A, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, p, sizeof(p)); break; }
        case 6: { uint8_t p[] = { 0x1A, 0x04, 0x08, reqId, 0x62, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, p, sizeof(p)); break; }
        case 7: { uint8_t p[] = { 0x1A, 0x05, 0x08, reqId, 0xAA, 0x02, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, p, sizeof(p)); break; }
        case 8: { uint8_t p[] = { 0x1A, 0x05, 0x08, reqId, 0x92, 0x02, 0x00 }; sendFmpRawPayloadTo(FMP_ROUTE_APP_TO_MAIN, p, sizeof(p)); break; }
        default: telemPollRequested = false; telemAwaitingReply = false; return;
    }
    telemPollStep++;
}

void stopExtractorMotor(bool forceSend = false) {
    webUiSpeedOverride = 0;
    if (connState != STATE_CONNECTED) return;
    if (currentPowerState == 1 || forceSend) {
        if (sendFmpCtControl(3, 0, 1)) {
            currentPowerState = 3;
            publishExtractorTelemetry(millis());
            LOGLN("[EXTRACT] Motor OFF sent.");
        }
    }
}

void saveMonitoredToNvs() {
    needSaveMonitored = false;
    needSaveMonitoredAtMs = 0;
    DynamicJsonDocument doc(4096);
    JsonArray arr = doc.to<JsonArray>();
    for (const auto& m : monitoredList) {
        JsonObject o = arr.createNestedObject();
        o["mac"] = m.address;
        if (m.addrType == 0 || m.addrType == 1) o["at"] = m.addrType;
        o["nm"] = m.name;
        o["advnm"] = m.advName;
        o["spd"] = m.speed;
        o["bt"] = m.btnType;
        o["raw"] = m.activeRaw;
        o["cn"] = m.customNamed;
        o["gatt"] = m.isGatt;
        o["grdy"] = m.gattReady;
        o["hose"] = (m.isHose && m.isGatt);
        o["adv"] = m.canAdv;
        o["cg"] = m.canGatt;
        o["mat"] = m.matNum;
        o["cat"] = m.devCat;
        o["wthr"] = m.wattsThr;
        if (m.periodicBeacon && !m.canAdv) o["bcn"] = true;
    }
    if (doc.overflowed()) {
        LOGLN("[NVS] Warning: monitored_list JSON overflowed 4096B buffer; skipping save.");
        return;
    }
    String jsonStr;
    serializeJson(doc, jsonStr);
    prefs.putString("mon_json", jsonStr);
    refreshMonMacCache();
    mqttDevicesDirty = true;
}

void loadMonitoredFromNvs() {
    String jsonStr = prefs.isKey("mon_json") ? prefs.getString("mon_json", "[]") : "[]";
    DynamicJsonDocument doc(4096);
    if (deserializeJson(doc, jsonStr) != DeserializationError::Ok || !doc.is<JsonArray>()) {
        refreshMonMacCache();
        return;
    }
    monitoredList.clear();
    for (JsonObject o : doc.as<JsonArray>()) {
        String mac = o["mac"] | "";
        if (mac.length() == 0) continue;
        if (pairedMac.length() > 0 && mac.equalsIgnoreCase(pairedMac)) continue;
        String nm = o["nm"] | "Device";
        String advNm = o["advnm"] | "";
        uint8_t spd = o["spd"] | 20;
        uint8_t bt = o["bt"] | 0;
        String raw = o["raw"] | "";
        bool cn = o["cn"] | false;
        bool gatt = o["gatt"] | false;
        bool gReady = o.containsKey("grdy") ? (bool)(o["grdy"] | false) : (!gatt);
        if (!gatt) gReady = true;
        bool hose = (o["hose"] | false) && gatt;
        bool cAdv = o["adv"] | (!gatt);
        bool cGatt = o["cg"] | gatt;
        uint32_t mat = o["mat"] | 0;
        uint8_t cat = o["cat"] | 0;
        uint16_t wThr = o["wthr"] | 60;
        uint8_t aType = o.containsKey("at") ? (uint8_t)(o["at"] | 255) : inferRandomAddrType(mac, 255);
        bool pBcn = cAdv ? false : (o["bcn"] | false);
        if (bt > 0) {
            cat = CAT_BUTTON;
            String upNm = nm; upNm.toUpperCase();
            String upAdv = advNm; upAdv.toUpperCase();
            bool isCtfRemote = (raw == "ADV:FESTOOL_REMOTE" || mat == 202097 || mat == 204842 ||
                                mat == 10029918 || mat == 10030046 ||
                                upNm.indexOf("CT-F") >= 0 || upNm.indexOf("CTF") >= 0 ||
                                upAdv.indexOf("CT-F") >= 0 || upAdv.indexOf("CTF") >= 0);
            if (isCtfRemote) {
                raw = "ADV:STREAM";
                cAdv = true;
                cGatt = false;
                gatt = false;
                gReady = true;
                hose = false;
            }
        }
        monitoredList.push_back({mac, nm, advNm, spd, bt, raw, cn, false, 0, gatt, gReady, false, 0, hose, cAdv, mat, cat, wThr, -1, cGatt, aType, pBcn});
    }
    refreshMonMacCache();
}

void saveWifiListToNvs() {
    DynamicJsonDocument doc(2048);
    JsonArray arr = doc.to<JsonArray>();
    for (const auto& w : wifiList) {
        if (w.ssid.length() == 0) continue;
        JsonObject o = arr.createNestedObject();
        o["ssid"] = w.ssid;
        o["pass"] = w.pass;
    }
    String jsonStr;
    serializeJson(doc, jsonStr);
    prefs.putString("wifi_json", jsonStr);
}

void loadSettingsFromNvs() {
    String wifiJson = prefs.isKey("wifi_json") ? prefs.getString("wifi_json", "[]") : "[]";
    DynamicJsonDocument doc(2048);
    if (deserializeJson(doc, wifiJson) == DeserializationError::Ok && doc.is<JsonArray>()) {
        wifiList.clear();
        for (JsonObject o : doc.as<JsonArray>()) {
            String ssid = o["ssid"] | "";
            String pass = o["pass"] | "";
            if (ssid.length() > 0) wifiList.push_back({ssid, pass});
        }
    }

    mqtt_en = prefs.getBool("mqtt_en", false);
    mqtt_ip = prefs.isKey("mqtt_ip") ? prefs.getString("mqtt_ip", "") : "";
    mqtt_port = prefs.getInt("mqtt_port", 1883);
    if (mqtt_port <= 0 || mqtt_port > 65535) mqtt_port = 1883;
    mqtt_user = prefs.isKey("mqtt_user") ? prefs.getString("mqtt_user", "") : "";
    mqtt_pass = prefs.isKey("mqtt_pass") ? prefs.getString("mqtt_pass", "") : "";

    bool authInit = prefs.getBool("auth_init", false);
    if (!authInit) {
        auth_en = (DEFAULT_AUTH_EN != 0);
        auth_user = DEFAULT_AUTH_USER;
        auth_salt = generateRandomHex(16);
        auth_hash = sha256Hex(auth_salt + ":" + auth_user + ":" + String(DEFAULT_AUTH_PASS));
        prefs.putBool("auth_init", true);
        prefs.putBool("auth_en", auth_en);
        prefs.putString("auth_user", auth_user);
        prefs.putString("auth_salt", auth_salt);
        prefs.putString("auth_hash", auth_hash);
    } else {
        auth_en = prefs.getBool("auth_en", (DEFAULT_AUTH_EN != 0));
        auth_user = prefs.isKey("auth_user") ? prefs.getString("auth_user", DEFAULT_AUTH_USER) : DEFAULT_AUTH_USER;
        auth_salt = prefs.isKey("auth_salt") ? prefs.getString("auth_salt", "") : "";
        auth_hash = prefs.isKey("auth_hash") ? prefs.getString("auth_hash", "") : "";
        if (auth_salt.length() != 32 || auth_hash.length() != 64) {
            auth_salt = generateRandomHex(16);
            auth_hash = sha256Hex(auth_salt + ":" + auth_user + ":" + String(DEFAULT_AUTH_PASS));
            prefs.putString("auth_salt", auth_salt);
            prefs.putString("auth_hash", auth_hash);
        }
    }
}

uint8_t quantizeSpeed(uint8_t pct) {
    if (pct <= 20) return 20;
    if (pct <= 40) return 40;
    if (pct <= 60) return 60;
    if (pct <= 80) return 80;
    return 100;
}

bool isAnyPrimaryDemandActive() {
    return hoseMomentaryActive || hoseToggleDemandActive || webUiDemandActive || btnToggleDemandActive || toolBattDemandActive;
}

MonitoredDevice* getWinningStandardDevice(bool* isWebUiWon = nullptr) {
    if (isWebUiWon) *isWebUiWon = false;
    uint8_t bestSpd = 0;
    MonitoredDevice* bestDev = nullptr;
    bool webWon = false;

    if (toolBattDemandActive) {
        MonitoredDevice* s = findMonitoredByMac(activeToolBattMac);
        uint8_t eff = (s && s->liveSpeedOverride > 0) ? s->liveSpeedOverride : toolBattTargetSpeed;
        if (eff >= bestSpd) { bestSpd = eff; bestDev = s; webWon = false; }
    }
    if (btnToggleDemandActive) {
        MonitoredDevice* s = findMonitoredByMac(activeBtnToggleMac);
        uint8_t eff = (s && s->liveSpeedOverride > 0) ? s->liveSpeedOverride : btnToggleTargetSpeed;
        if (eff >= bestSpd) { bestSpd = eff; bestDev = s; webWon = false; }
    }
    if (webUiDemandActive) {
        uint8_t eff = (webUiSpeedOverride > 0) ? webUiSpeedOverride : userManualSpeed;
        if (eff >= bestSpd) { bestSpd = eff; bestDev = nullptr; webWon = true; }
    }
    if (isWebUiWon) *isWebUiWon = webWon;
    return bestDev;
}

uint8_t getActiveLiveSpeedOverride() {
    if (hoseMomentaryActive) { MonitoredDevice* s = findMonitoredByMac(activeHoseMomMac); return s ? s->liveSpeedOverride : 0; }
    if (hoseToggleDemandActive) { MonitoredDevice* s = findMonitoredByMac(activeHoseToggleMac); return s ? s->liveSpeedOverride : 0; }
    bool webWon = false;
    MonitoredDevice* stdDev = getWinningStandardDevice(&webWon);
    if (webWon) return webUiSpeedOverride;
    return stdDev ? stdDev->liveSpeedOverride : 0;
}

void setActiveLiveSpeedOverride(uint8_t spd) {
    uint8_t q = quantizeSpeed(spd);
    if (hoseMomentaryActive) { MonitoredDevice* s = findMonitoredByMac(activeHoseMomMac); if (s) s->liveSpeedOverride = q; }
    else if (hoseToggleDemandActive) { MonitoredDevice* s = findMonitoredByMac(activeHoseToggleMac); if (s) s->liveSpeedOverride = q; }
    else {
        bool webWon = false;
        MonitoredDevice* stdDev = getWinningStandardDevice(&webWon);
        if (webWon) webUiSpeedOverride = q;
        else if (stdDev) stdDev->liveSpeedOverride = q;
    }
}

void adjustLiveSpeed(int delta) {
    uint8_t base = getActiveLiveSpeedOverride();
    if (base == 0) base = currentSuctionPct;
    int next = (int)base + delta;
    uint8_t q = quantizeSpeed((uint8_t)(next < 20 ? 20 : (next > 100 ? 100 : next)));
    setActiveLiveSpeedOverride(q);
    LOGF("[LIVE SPEED] %s -> %u%%\n", delta > 0 ? "+20%" : "-20%", q);
    demandDirty = true;
}

void evaluateMotorDemand() {
    bool wantOn = false;
    uint8_t targetSpeed = 20;

    if (hoseMomentaryActive) {
        wantOn = true;
        activePresetSpeed = hoseMomTargetSpeed;
        MonitoredDevice* s = findMonitoredByMac(activeHoseMomMac);
        targetSpeed = (s && s->liveSpeedOverride > 0) ? s->liveSpeedOverride : hoseMomTargetSpeed;
    } else if (hoseToggleDemandActive) {
        wantOn = true;
        activePresetSpeed = hoseToggleTargetSpeed;
        MonitoredDevice* s = findMonitoredByMac(activeHoseToggleMac);
        targetSpeed = (s && s->liveSpeedOverride > 0) ? s->liveSpeedOverride : hoseToggleTargetSpeed;
    } else if (webUiDemandActive || btnToggleDemandActive || toolBattDemandActive) {
        wantOn = true;
        uint8_t bestSpd = 0;
        uint8_t bestPreset = 20;
        if (toolBattDemandActive) {
            MonitoredDevice* s = findMonitoredByMac(activeToolBattMac);
            uint8_t eff = (s && s->liveSpeedOverride > 0) ? s->liveSpeedOverride : toolBattTargetSpeed;
            if (eff >= bestSpd) { bestSpd = eff; bestPreset = toolBattTargetSpeed; }
        }
        if (btnToggleDemandActive) {
            MonitoredDevice* s = findMonitoredByMac(activeBtnToggleMac);
            uint8_t eff = (s && s->liveSpeedOverride > 0) ? s->liveSpeedOverride : btnToggleTargetSpeed;
            if (eff >= bestSpd) { bestSpd = eff; bestPreset = btnToggleTargetSpeed; }
        }
        if (webUiDemandActive) {
            uint8_t eff = (webUiSpeedOverride > 0) ? webUiSpeedOverride : userManualSpeed;
            if (eff >= bestSpd) { bestSpd = eff; bestPreset = userManualSpeed; }
        }
        activePresetSpeed = bestPreset;
        targetSpeed = bestSpd;
    } else if (hoseClearActive) {
        wantOn = true;
        targetSpeed = 20;
    }

    if (!wantOn) {
        bool fStop = forceStopNow;
        forceStopNow = false;
        stopExtractorMotor(fStop);
        return;
    }

    forceStopNow = false;
    targetSpeed = quantizeSpeed(targetSpeed);
    if (connState == STATE_CONNECTED) {
        if (currentPowerState != 1 || currentSuctionPct != targetSpeed) {
            if (sendFmpCtControl(1, targetSpeed, 1)) {
                currentPowerState = 1;
                currentSuctionPct = targetSpeed;
                publishExtractorTelemetry(millis());
                LOGF("[EXTRACT] Motor ON -> %u%%\n", targetSpeed);
            }
        }
    }
}

extern std::atomic<bool> gattBtnTaskRunning;

void setCoexScanner() {
    if (extConnTaskRunning.load() || gattBtnTaskRunning.load() || wifiScanInProgress || Update.isRunning()) return;
    NimBLEDevice::setOwnAddrType(BLE_OWN_ADDR_PUBLIC);
    NimBLEScan* pScan = NimBLEDevice::getScan();
    static bool scannerConfigured = false;
    if (scannerConfigured && pScan->isScanning()) {
        return;
    }
    if (pScan->isScanning()) {
        pScan->stop();
    }
    pScan->setDuplicateFilter(false);
    pScan->setActiveScan(false);
    pScan->setInterval(160);
    pScan->setWindow(80);
    pScan->setMaxResults(0);
    scannerConfigured = true;
    pScan->start(0, false);
}

uint8_t getCurrentStandardDemandSpeed() {
    uint8_t maxSpd = 0;
    if (webUiDemandActive) {
        uint8_t s = (webUiSpeedOverride > 0) ? webUiSpeedOverride : userManualSpeed;
        if (s > maxSpd) maxSpd = s;
    }
    if (btnToggleDemandActive) {
        MonitoredDevice* m = findMonitoredByMac(activeBtnToggleMac);
        uint8_t s = (m && m->liveSpeedOverride > 0) ? m->liveSpeedOverride : btnToggleTargetSpeed;
        if (s > maxSpd) maxSpd = s;
    }
    if (toolBattDemandActive) {
        MonitoredDevice* m = findMonitoredByMac(activeToolBattMac);
        uint8_t s = (m && m->liveSpeedOverride > 0) ? m->liveSpeedOverride : toolBattTargetSpeed;
        if (s > maxSpd) maxSpd = s;
    }
    return maxSpd;
}

bool isBlockedByActiveRun(const String& mac, uint8_t reqSpd) {
    if (hoseMomentaryActive || hoseToggleDemandActive) return true;
    uint8_t activeStdSpd = getCurrentStandardDemandSpeed();
    if (activeStdSpd > 0) {
        return (reqSpd < activeStdSpd);
    }
    for (const auto& other : monitoredList) {
        if (other.address.equalsIgnoreCase(mac)) continue;
        if (other.btnType > 0 && (other.toggleActive || other.momActive)) return true;
    }
    return false;
}

void executeToggleTapAction(const String& mac, uint8_t presetSpd, uint8_t taps, unsigned long now) {
    MonitoredDevice* targetMon = findMonitoredByMac(mac);
    if (!targetMon) return;

    bool isHoseGatt = (targetMon->isHose && targetMon->isGatt);
    const char* roleTag = isHoseGatt ? "PRIMARY TOGGLE" : "BTN TOGGLE";

    if (taps == 1) {
        if (!targetMon->toggleActive) {
            if (!isHoseGatt && isBlockedByActiveRun(mac, presetSpd)) {
                LOGF("[%s] Ignored press -> higher/equal speed run or Primary switch is already active (%s)\n", roleTag, mac.c_str());
                return;
            }
            if (!isHoseGatt && hoseClearActive) {
                LOGF("[%s] 1x Tap -> OFF (cleared evac run) (%s)\n", roleTag, mac.c_str());
                hoseClearActive = false;
                targetMon->liveSpeedOverride = 0;
                forceStopNow = true;
                demandDirty = true;
                return;
            }
            LOGF("[%s] 1x Tap -> %s at %u%% (%s)\n",
                 roleTag,
                 isHoseGatt ? "Takeover ON" : "ON",
                 presetSpd, mac.c_str());
            if (isHoseGatt) {
                clearOtherHoseButtonStates(mac);
                webUiDemandActive = false;
                webUiSpeedOverride = 0;
            }
            targetMon->toggleActive = true;
            targetMon->toggleActivatedMs = now;
            targetMon->liveSpeedOverride = 0;
            syncButtonDemandsFromMonitored();
            hoseClearActive = false;
            demandDirty = true;
        } else {
            LOGF("[%s] 1x Tap -> %s (%s)\n",
                 roleTag,
                 isHoseGatt ? "Release OFF" : "OFF",
                 mac.c_str());
            targetMon->toggleActive = false;
            targetMon->toggleActivatedMs = 0;
            targetMon->liveSpeedOverride = 0;
            syncButtonDemandsFromMonitored();
            if (!isAnyPrimaryDemandActive()) {
                if (evacSeconds > 0) { LOGF("[%s] Entering %us debris evacuation at 20%%\n", roleTag, evacSeconds); hoseClearActive = true; hoseClearTimer = now; }
                else forceStopNow = true;
            }
            demandDirty = true;
        }
    } else if (taps == 2 && isHoseGatt) {
        if (isAnyPrimaryDemandActive() && !hoseClearActive && !hoseMomentaryActive) {
            LOGF("[%s] 2x Tap -> Speed +20%% (%s)\n", roleTag, mac.c_str());
            adjustLiveSpeed(+20);
        } else {
            LOGF("[%s] Ignored 2x Tap -> extractor is idle or in momentary mode (%s)\n", roleTag, mac.c_str());
        }
    } else if (taps >= 3 && isHoseGatt) {
        if (isAnyPrimaryDemandActive() && !hoseClearActive && !hoseMomentaryActive) {
            LOGF("[%s] 3x Tap -> Speed -20%% (%s)\n", roleTag, mac.c_str());
            adjustLiveSpeed(-20);
        } else {
            LOGF("[%s] Ignored 3x Tap -> extractor is idle or in momentary mode (%s)\n", roleTag, mac.c_str());
        }
    }
}

void onButtonRelease(const String& mac, unsigned long now) {
    MonitoredDevice* m = findMonitoredByMac(mac);
    if (!m || m->btnPhase == BTN_IDLE) return;

    bool isHoseBtn = (m->isHose && m->isGatt);
    if (isHoseBtn && m->hoseHoldActivated) {
        m->hoseHoldActivated = false;
        m->momActive = false;
        m->liveSpeedOverride = 0;
        m->btnPhase = BTN_IDLE;
        m->btnTapCount = 0;
        syncButtonDemandsFromMonitored();
        if (!isAnyPrimaryDemandActive()) {
            LOGF("[PRIMARY AUTO] Hold release -> OFF (%s)\n", mac.c_str());
            if (evacSeconds > 0) {
                LOGF("[PRIMARY AUTO] Entering %us debris evacuation at 20%%\n", evacSeconds);
                hoseClearActive = true;
                hoseClearTimer = now;
            } else {
                forceStopNow = true;
            }
        } else {
            LOGF("[PRIMARY AUTO] Hold release -> returning to underlying run (%s)\n", mac.c_str());
        }
        demandDirty = true;
        return;
    }

    if (m->isGatt) {
        if (m->btnTapCount == 0) m->btnTapCount = 1;
        m->btnPhase = BTN_WAIT_TAP;
        m->btnReleaseMs = now;
    } else {
        m->btnPhase = BTN_IDLE;
        m->btnTapCount = 0;
        m->hoseHoldActivated = false;
    }
}

void onButtonPacket(const String& mac, uint8_t presetSpd, unsigned long now, bool isGatt, int16_t seqByte) {
    MonitoredDevice* m = findMonitoredByMac(mac);
    if (!m || pairedMac.length() == 0) return;

    if (!isGatt && seqByte >= 0) {
        if (m->btnLastSeqByte >= 0 && seqByte != m->btnLastSeqByte && m->btnPhase == BTN_HELD) {
            onButtonRelease(mac, now);
        }
        m->btnLastSeqByte = seqByte;
    }

    bool isHoseBtn = (m->isHose && m->isGatt);

    if (m->btnPhase == BTN_IDLE) {
        m->btnPhase = BTN_HELD;
        m->btnPressStartMs = now;
        m->btnLastPacketMs = now;
        m->btnTapCount = 1;
        m->hoseHoldActivated = false;

        if (!isGatt) {
            executeToggleTapAction(mac, presetSpd, 1, now);
        } else if (isHoseBtn) {
            bool underlyingRunning = (webUiDemandActive || btnToggleDemandActive || toolBattDemandActive ||
                                      hoseToggleDemandActive || (hoseMomentaryActive && !activeHoseMomMac.equalsIgnoreCase(mac)));
            if (!underlyingRunning && !m->toggleActive) {
                m->momActive = true;
                m->momSpeed = presetSpd;
                m->liveSpeedOverride = 0;
                hoseClearActive = false;
                syncButtonDemandsFromMonitored();
                demandDirty = true;
            }
        }
        return;
    }

    if (m->btnPhase == BTN_WAIT_TAP) {
        m->btnPhase = BTN_HELD;
        m->btnPressStartMs = now;
        m->btnLastPacketMs = now;
        m->btnTapCount++;
        if (isHoseBtn && m->momActive) {
            m->momActive = false;
            m->liveSpeedOverride = 0;
            syncButtonDemandsFromMonitored();
            if (!isAnyPrimaryDemandActive() && !hoseClearActive) {
                forceStopNow = true;
                demandDirty = true;
            }
        }
        return;
    }

    if (m->btnPhase == BTN_HELD) {
        m->btnLastPacketMs = now;
        if (isHoseBtn && !m->hoseHoldActivated && elapsedMs(now, m->btnPressStartMs) >= BTN_MOMENTARY_TAP_MAX_MS) {
            m->hoseHoldActivated = true;
            m->btnTapCount = 0;
            if (m->toggleActive) {
                m->toggleActive = false;
                m->toggleActivatedMs = 0;
            }
            clearOtherHoseButtonStates(mac);
            m->momActive = true;
            m->momSpeed = presetSpd;
            m->liveSpeedOverride = 0;
            hoseClearActive = false;
            syncButtonDemandsFromMonitored();
            demandDirty = true;
            LOGF("[PRIMARY AUTO] Hold confirmed -> Momentary at %u%% (%s)\n", presetSpd, mac.c_str());
        }
    }
}

void serviceButtonGestures(unsigned long now) {
    for (auto& m : monitoredList) {
        if (m.btnType == 0 || m.btnPhase == BTN_IDLE) continue;

        if (m.btnPhase == BTN_WAIT_TAP) {
            if (elapsedMs(now, m.btnReleaseMs) >= BTN_GATT_TAP_WINDOW_MS) {
                if (m.isHose && m.isGatt) {
                    uint8_t taps = m.btnTapCount;
                    m.btnTapCount = 0;
                    m.btnPhase = BTN_IDLE;
                    if (taps == 1) {
                        if (!m.toggleActive) {
                            clearOtherHoseButtonStates(m.address);
                            m.momActive = false;
                            m.toggleActive = true;
                            m.toggleActivatedMs = now;
                            m.liveSpeedOverride = 0;
                            syncButtonDemandsFromMonitored();
                            hoseClearActive = false;
                            demandDirty = true;
                            LOGF("[PRIMARY AUTO] 1x Tap -> Primary Override ON at %u%% (%s)\n", m.speed, m.address.c_str());
                        } else {
                            m.momActive = false;
                            m.toggleActive = false;
                            m.toggleActivatedMs = 0;
                            m.liveSpeedOverride = 0;
                            syncButtonDemandsFromMonitored();
                            if (!isAnyPrimaryDemandActive()) {
                                if (evacSeconds > 0) { LOGF("[PRIMARY AUTO] Entering %us debris evacuation at 20%%\n", evacSeconds); hoseClearActive = true; hoseClearTimer = now; }
                                else forceStopNow = true;
                                LOGF("[PRIMARY AUTO] 1x Tap -> OFF (%s)\n", m.address.c_str());
                            } else {
                                LOGF("[PRIMARY AUTO] 1x Tap -> Released Primary Override, returning to underlying run (%s)\n", m.address.c_str());
                            }
                            demandDirty = true;
                        }
                    } else if (taps >= 2) {
                        if (m.momActive) {
                            m.momActive = false;
                            m.liveSpeedOverride = 0;
                            syncButtonDemandsFromMonitored();
                            if (!isAnyPrimaryDemandActive() && !hoseClearActive) {
                                forceStopNow = true;
                                demandDirty = true;
                            }
                        }
                        if (isAnyPrimaryDemandActive() && !hoseClearActive && !hoseMomentaryActive) {
                            if (taps == 2) {
                                LOGF("[PRIMARY AUTO] 2x Tap -> Speed +20%% (%s)\n", m.address.c_str());
                                adjustLiveSpeed(+20);
                            } else {
                                LOGF("[PRIMARY AUTO] 3x Tap -> Speed -20%% (%s)\n", m.address.c_str());
                                adjustLiveSpeed(-20);
                            }
                        } else {
                            LOGF("[PRIMARY AUTO] Ignored %ux Tap -> extractor is idle or in momentary mode (%s)\n", taps, m.address.c_str());
                        }
                    }
                    continue;
                }
                if (m.btnTapCount > 0) executeToggleTapAction(m.address, m.speed, m.btnTapCount, now);
                m.btnTapCount = 0;
                m.btnPhase = BTN_IDLE;
            }
            continue;
        }
        if (m.btnPhase == BTN_HELD && !m.isGatt) {
            if (elapsedMs(now, m.btnLastPacketMs) > ADV_TOGGLE_TAP_RELEASE_MS) onButtonRelease(m.address, now);
        }
    }
}

class ClientCallbacks : public NimBLEClientCallbacks {
    void onConnect(NimBLEClient* client) override { (void)client; connState = STATE_CONNECTING; extLinkConnectedLog.store(true); }
    void onDisconnect(NimBLEClient* client, int reason) override {
        (void)client; (void)reason; connState = STATE_DISCONNECTED; currentPowerState = 3;
        pairedRssi = 0;
        pWriteChar = nullptr; pNotifyChar = nullptr; rxCobsLen = 0;
        initialTelemDone = false;
        postConnectActionPending = false;
        telemPollRequested = false; telemAwaitingReply = false; extLinkDisconnectedFlag.store(true);
    }
};

static const int MAX_GATT_BTN_SLOTS = 2;
struct GattBtnSlot {
    NimBLEClient* client = nullptr;
    bool inUse = false;
    volatile bool connected = false;
    bool connecting = false;
    volatile uint32_t connGen = 0;
    char mac[18] = {0};
    volatile bool pressed = false;
    volatile uint8_t pendingPressEdges = 0;
    volatile bool gotAnyNotify = false;
    volatile bool releaseNow = false;
    bool wakePreTriggered = false;
    volatile unsigned long lastActivityMs = 0;
    volatile unsigned long lastPressEdgeMs = 0;
    unsigned long connectedAtMs = 0;
    unsigned long lastRssiMs = 0;
    char lastHex[48] = {0};
    volatile bool rxLogPending = false;
    volatile bool rxLogPressed = false;
    volatile bool sleepDiscLogPending = false;
};
portMUX_TYPE gattSlotMux = portMUX_INITIALIZER_UNLOCKED;
uint32_t globalGattConnGen = 1;
GattBtnSlot gattSlots[MAX_GATT_BTN_SLOTS];

struct GattConnTaskParams {
    int slotIdx;
    uint32_t connGen;
    NimBLEClient* client;
    char mac[18];
    uint8_t addrType;
};
std::atomic<bool> gattBtnTaskRunning{false};
std::atomic<bool> gattBtnTaskDone{false};
std::atomic<bool> gattBtnTaskOk{false};
int gattBtnTaskSlotIdx = -1;
uint32_t gattBtnTaskConnGen = 0;

static const int MAX_GATT_PENDING = 4;
struct GattPendingReq { bool active; String mac; uint8_t addrType; uint8_t btnType; uint8_t speed; bool wakePreTrig; };
GattPendingReq gattPending[MAX_GATT_PENDING];

struct GattBackoffEntry { String mac; unsigned long untilMs; };
std::vector<GattBackoffEntry> gattBackoffs;
unsigned long gattBtnLastTryMs = 0;

void setGattBackoff(const String& macStr, unsigned long untilMs) {
    for (auto& b : gattBackoffs) if (b.mac.equalsIgnoreCase(macStr)) { b.untilMs = untilMs; return; }
    gattBackoffs.push_back({macStr, untilMs});
}
void clearGattBackoff(const String& macStr) {
    for (auto it = gattBackoffs.begin(); it != gattBackoffs.end(); ) { if (it->mac.equalsIgnoreCase(macStr)) it = gattBackoffs.erase(it); else ++it; }
}
bool isGattBackedOff(const String& macStr, unsigned long now) {
    for (auto it = gattBackoffs.begin(); it != gattBackoffs.end(); ) {
        if (now >= it->untilMs) it = gattBackoffs.erase(it);
        else if (it->mac.equalsIgnoreCase(macStr)) return true;
        else ++it;
    }
    return false;
}
int findGattSlotByClient(NimBLEClient* pC) { for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) if (gattSlots[i].client == pC) return i; return -1; }
int findGattSlotByMac(const String& macStr) {
    int found = -1;
    portENTER_CRITICAL(&gattSlotMux);
    for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) {
        if (gattSlots[i].inUse && strcasecmp(gattSlots[i].mac, macStr.c_str()) == 0) {
            found = i;
            break;
        }
    }
    portEXIT_CRITICAL(&gattSlotMux);
    return found;
}
bool isGattMacConnectedOrBusy(const String& macStr) { int idx = findGattSlotByMac(macStr); return (idx >= 0) && (gattSlots[idx].connected || gattSlots[idx].connecting); }
bool isGattPending(const String& macStr) {
    for (int i = 0; i < MAX_GATT_PENDING; i++) {
        if (gattPending[i].active && gattPending[i].mac.equalsIgnoreCase(macStr)) return true;
    }
    return false;
}

void enqueueGattConnect(const String& macStr, uint8_t addrType, uint8_t bType, uint8_t bSpd, bool forceImmediate = false, bool wakePreTrig = false) {
    unsigned long now = millis();
    if (forceImmediate) clearGattBackoff(macStr);
    else if (isGattBackedOff(macStr, now)) return;
    if (isGattMacConnectedOrBusy(macStr)) return;
    for (int i = 0; i < MAX_GATT_PENDING; i++) {
        if (gattPending[i].active && gattPending[i].mac.equalsIgnoreCase(macStr)) {
            gattPending[i].addrType = addrType; gattPending[i].btnType = bType; gattPending[i].speed = bSpd;
            if (wakePreTrig) gattPending[i].wakePreTrig = true;
            return;
        }
    }
    for (int i = 0; i < MAX_GATT_PENDING; i++) if (!gattPending[i].active) { gattPending[i] = {true, macStr, addrType, bType, bSpd, wakePreTrig}; return; }
}

void handleGattSlotNotify(int idx, NimBLERemoteCharacteristic* pChr, uint8_t* pData, size_t length) {
    (void)pChr;
    if (idx < 0 || idx >= MAX_GATT_BTN_SLOTS || !pData || length == 0) return;
    GattBtnSlot& s = gattSlots[idx];
    unsigned long now = millis();
    char hexTmp[48];
    size_t pos = 0;
    for (size_t i = 0; i < length && pos + 4 < sizeof(hexTmp); i++) pos += snprintf(hexTmp + pos, sizeof(hexTmp) - pos, "%02X ", pData[i]);
    if (pos > 0 && hexTmp[pos - 1] == ' ') hexTmp[pos - 1] = '\0'; else hexTmp[pos] = '\0';
    bool pressed = false;
    for (size_t i = 0; i < length; i++) if (pData[i] != 0x00) { pressed = true; break; }
    if (length == 1 && pData[0] == '0') pressed = false;

    portENTER_CRITICAL(&gattSlotMux);
    s.lastActivityMs = now;
    s.gotAnyNotify = true;
    memcpy(s.lastHex, hexTmp, sizeof(s.lastHex));
    s.rxLogPressed = pressed;
    s.rxLogPending = true;
    if (pressed) {
        bool isNewPhysicalPress = (!s.pressed && (s.lastPressEdgeMs == 0 || elapsedMs(now, s.lastPressEdgeMs) >= 55UL));
        s.pressed = true;
        if (isNewPhysicalPress) {
            s.lastPressEdgeMs = now;
            if (s.pendingPressEdges < 8) s.pendingPressEdges = s.pendingPressEdges + 1;
        }
    } else {
        if (s.pressed) {
            s.pressed = false;
            s.releaseNow = true;
        }
    }
    portEXIT_CRITICAL(&gattSlotMux);
}

void gattSlot0NotifyCB(NimBLERemoteCharacteristic* pChr, uint8_t* pData, size_t length, bool isNotify) { (void)isNotify; handleGattSlotNotify(0, pChr, pData, length); }
void gattSlot1NotifyCB(NimBLERemoteCharacteristic* pChr, uint8_t* pData, size_t length, bool isNotify) { (void)isNotify; handleGattSlotNotify(1, pChr, pData, length); }

class GattBtnClientCallbacks : public NimBLEClientCallbacks {
    void onConnect(NimBLEClient* pC) override {
        int idx = findGattSlotByClient(pC);
        if (idx >= 0 && pC) {
            std::string peerStr = pC->getPeerAddress().toString();
            portENTER_CRITICAL(&gattSlotMux);
            if (gattSlots[idx].inUse && gattSlots[idx].mac[0] != '\0' &&
                strcasecmp(gattSlots[idx].mac, peerStr.c_str()) == 0) {
                gattSlots[idx].connected = true;
            }
            portEXIT_CRITICAL(&gattSlotMux);
        }
    }
    void onDisconnect(NimBLEClient* pC, int reason) override {
        (void)reason;
        int idx = findGattSlotByClient(pC);
        if (idx >= 0 && pC) {
            GattBtnSlot& s = gattSlots[idx];
            std::string peerStr = pC->getPeerAddress().toString();
            portENTER_CRITICAL(&gattSlotMux);
            if (s.inUse && s.mac[0] != '\0' && strcasecmp(s.mac, peerStr.c_str()) == 0) {
                s.connected = false;
                s.connecting = false;
                if (s.pressed) { s.pressed = false; s.releaseNow = true; }
                s.sleepDiscLogPending = true;
            }
            portEXIT_CRITICAL(&gattSlotMux);
        }
    }
};
static GattBtnClientCallbacks gattBtnClientCB;

void gattBtnConnectWorkerTask(void* param) {
    GattConnTaskParams* p = static_cast<GattConnTaskParams*>(param);
    bool ok = false;
    if (p && p->client) {
        if (p->client->isConnected()) {
            p->client->disconnect();
            for (int w = 0; w < 20 && p->client->isConnected(); w++) {
                delay(10);
            }
        }
        NimBLEAddress targetAddr(p->mac, p->addrType);
        ok = p->client->connect(targetAddr, true);
    }
    delete p;
    gattBtnTaskOk.store(ok);
    gattBtnTaskRunning.store(false);
    gattBtnTaskDone.store(true);
    vTaskDelete(nullptr);
}

void startGattButtonConnect(const String& macStr, uint8_t addrType, uint8_t bType, uint8_t bSpd, bool wakePreTrig = false) {
    if (gattBtnTaskRunning.load() || extConnTaskRunning.load()) return;
    gattBtnLastTryMs = millis();
    int existing = findGattSlotByMac(macStr);
    if (existing >= 0) {
        GattBtnSlot& s = gattSlots[existing];
        if (s.connecting) return;
        if (s.connected && s.client && s.client->isConnected()) return;
    }
    int slotIdx = existing;
    if (slotIdx < 0) for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) if (!gattSlots[i].connected && !gattSlots[i].connecting) { slotIdx = i; break; }
    if (slotIdx < 0) {
        unsigned long oldestMs = ULONG_MAX;
        for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) if (!gattSlots[i].connecting && !gattSlots[i].pressed && gattSlots[i].lastActivityMs < oldestMs) { oldestMs = gattSlots[i].lastActivityMs; slotIdx = i; }
        if (slotIdx >= 0) {
            char evictedMac[18] = {0};
            portENTER_CRITICAL(&gattSlotMux);
            if (gattSlots[slotIdx].inUse && gattSlots[slotIdx].mac[0] != '\0' &&
                strcasecmp(gattSlots[slotIdx].mac, macStr.c_str()) != 0) {
                strncpy(evictedMac, gattSlots[slotIdx].mac, sizeof(evictedMac) - 1);
            }
            portEXIT_CRITICAL(&gattSlotMux);
            if (evictedMac[0] != '\0') {
                MonitoredDevice* evictedMon = findMonitoredByMac(String(evictedMac));
                if (evictedMon) {
                    bool wasActive = evictedMon->toggleActive || evictedMon->momActive;
                    resetMonitoredButtonGesture(*evictedMon, true);
                    syncButtonDemandsFromMonitored();
                    if (wasActive && !isAnyPrimaryDemandActive() && !hoseClearActive) {
                        forceStopNow = true;
                        demandDirty = true;
                    }
                    LOGF("[GATT BTN] Evicted %s from Slot %d -> toggled OFF.\n", evictedMac, slotIdx);
                }
            }
        }
    }
    if (slotIdx < 0) return;

    addrType = inferRandomAddrType(macStr, addrType);

    // Pause continuous BLE scanning so the single 2.4 GHz radio can establish the GATT link cleanly
    NimBLEDevice::getScan()->stop();

    GattBtnSlot& s = gattSlots[slotIdx];
    uint32_t gen = ++globalGattConnGen;
    portENTER_CRITICAL(&gattSlotMux);
    s.inUse = true; s.connecting = true; s.connected = false; s.connGen = gen;
    s.connectedAtMs = 0;
    strncpy(s.mac, macStr.c_str(), sizeof(s.mac) - 1);
    s.mac[sizeof(s.mac) - 1] = '\0';
    s.pressed = false; s.pendingPressEdges = 0; s.gotAnyNotify = false; s.releaseNow = false;
    s.wakePreTriggered = wakePreTrig;
    s.lastPressEdgeMs = 0; s.rxLogPending = false; s.sleepDiscLogPending = false;
    portEXIT_CRITICAL(&gattSlotMux);

    if (s.client && s.client->isConnected()) {
        s.client->disconnect();
    }

    if (!s.client) {
        s.client = NimBLEDevice::createClient();
        s.client->setClientCallbacks(&gattBtnClientCB, false);
        // Allow 4-event peripheral latency so idle GATT switches free ~80% of radio slots for the extractor & scanner
        s.client->setConnectionParams(24, 40, 4, 400);
        s.client->setConnectTimeout(1800);
    }

    LOGF("[GATT BTN] [Slot %d] Connecting to %s (addrType=%u)...\n", slotIdx, macStr.c_str(), addrType);

    GattConnTaskParams* taskParams = new GattConnTaskParams();
    taskParams->slotIdx = slotIdx;
    taskParams->connGen = gen;
    taskParams->client = s.client;
    strncpy(taskParams->mac, macStr.c_str(), sizeof(taskParams->mac) - 1);
    taskParams->mac[sizeof(taskParams->mac) - 1] = '\0';
    taskParams->addrType = addrType;

    gattBtnTaskSlotIdx = slotIdx;
    gattBtnTaskConnGen = gen;
    gattBtnTaskOk.store(false);
    gattBtnTaskDone.store(false);
    gattBtnTaskRunning.store(true);
    if (xTaskCreatePinnedToCore(gattBtnConnectWorkerTask, "gattBtnConn", 6144, taskParams, 1, nullptr, 1) != pdPASS) {
        delete taskParams;
        gattBtnTaskRunning.store(false);
        portENTER_CRITICAL(&gattSlotMux);
        s.connecting = false;
        s.connected = false;
        portEXIT_CRITICAL(&gattSlotMux);
        setCoexScanner();
    }
}

void finishGattButtonConnect(unsigned long now) {
    int slotIdx = gattBtnTaskSlotIdx;
    uint32_t expectedGen = gattBtnTaskConnGen;
    bool ok = gattBtnTaskOk.load();
    if (slotIdx < 0 || slotIdx >= MAX_GATT_BTN_SLOTS) {
        setCoexScanner();
        return;
    }

    GattBtnSlot& s = gattSlots[slotIdx];
    char macBuf[18] = {0};
    portENTER_CRITICAL(&gattSlotMux);
    bool slotInUse = s.inUse && (s.connGen == expectedGen);
    strncpy(macBuf, s.mac, sizeof(macBuf) - 1);
    macBuf[sizeof(macBuf) - 1] = '\0';
    portEXIT_CRITICAL(&gattSlotMux);
    String macStr(macBuf);

    if (!slotInUse) {
        if (s.client && s.client->isConnected() && !s.inUse) s.client->disconnect();
        setCoexScanner();
        return;
    }

    if (!ok) {
        LOGF("[GATT BTN] [Slot %d] Connect failed for %s\n", slotIdx, macStr.c_str());
        bool wasWakePre = s.wakePreTriggered;
        portENTER_CRITICAL(&gattSlotMux);
        s.connecting = false; s.connected = false; s.wakePreTriggered = false;
        portEXIT_CRITICAL(&gattSlotMux);
        if (wasWakePre) {
            MonitoredDevice* monPtr = findMonitoredByMac(macStr);
            if (monPtr && monPtr->wakePreTriggered) {
                monPtr->wakePreTriggered = false;
                if (monPtr->btnPhase == BTN_HELD) {
                    unsigned long relTs = monPtr->isHose ? (monPtr->btnPressStartMs + 100UL) : now;
                    onButtonRelease(macStr, relTs);
                }
            }
        }
        gattBtnLastTryMs = now;
        setGattBackoff(macStr, now + 1200UL);
        setCoexScanner();
        return;
    }

    NimBLERemoteCharacteristic::notify_callback cb = (slotIdx == 0) ? gattSlot0NotifyCB : gattSlot1NotifyCB;
    int subCount = 0;
    NimBLERemoteService* pFfe0 = s.client->getService(NimBLEUUID((uint16_t)0xFFE0));
    if (pFfe0) {
        const auto& chars = pFfe0->getCharacteristics(true);
        for (auto* c : chars) if (c && (c->canNotify() || c->canIndicate()) && c->subscribe(c->canNotify(), cb)) { subCount++; LOGF("[GATT BTN] [Slot %d] Subscribed 0xFFE0 chr=%s\n", slotIdx, c->getUUID().toString().c_str()); }
    }
    if (subCount == 0) {
        NimBLERemoteService* pHid = s.client->getService(NimBLEUUID((uint16_t)0x1812));
        if (pHid) {
            const auto& chars = pHid->getCharacteristics(true);
            for (auto* c : chars) if (c && (c->canNotify() || c->canIndicate()) && c->subscribe(c->canNotify(), cb)) { subCount++; LOGF("[GATT BTN] [Slot %d] Subscribed HID chr=%s\n", slotIdx, c->getUUID().toString().c_str()); }
        }
    }
    if (subCount == 0) {
        const auto& svcs = s.client->getServices(true);
        for (auto* svc : svcs) {
            if (!svc) continue;
            NimBLEUUID u = svc->getUUID();
            if (u == NimBLEUUID((uint16_t)0x1800) || u == NimBLEUUID((uint16_t)0x1801) ||
                u == NimBLEUUID((uint16_t)0x180A) || u == NimBLEUUID((uint16_t)0x180F)) continue;
            const auto& chars = svc->getCharacteristics(true);
            for (auto* c : chars) {
                if (c && (c->canNotify() || c->canIndicate()) && c->subscribe(c->canNotify(), cb)) {
                    subCount++;
                    LOGF("[GATT BTN] [Slot %d] Subscribed svc=%s chr=%s\n", slotIdx, u.toString().c_str(), c->getUUID().toString().c_str());
                }
            }
        }
    }

    if (subCount == 0) {
        LOGF("[GATT BTN] [Slot %d] No notify/indicate characteristic found on %s; disconnecting.\n", slotIdx, macStr.c_str());
        s.client->disconnect();
        bool wasWakePre = s.wakePreTriggered;
        portENTER_CRITICAL(&gattSlotMux);
        s.connecting = false; s.connected = false; s.wakePreTriggered = false;
        portEXIT_CRITICAL(&gattSlotMux);
        if (wasWakePre) {
            MonitoredDevice* monPtr = findMonitoredByMac(macStr);
            if (monPtr && monPtr->wakePreTriggered) {
                monPtr->wakePreTriggered = false;
                if (monPtr->btnPhase == BTN_HELD) {
                    unsigned long relTs = monPtr->isHose ? (monPtr->btnPressStartMs + 100UL) : now;
                    onButtonRelease(macStr, relTs);
                }
            }
        }
        gattBtnLastTryMs = now;
        setGattBackoff(macStr, now + 1200UL);
        setCoexScanner();
        return;
    }

    clearGattBackoff(macStr);
    bool handedOffImmediately = false;
    bool wakeTapAlreadyReleased = false;
    portENTER_CRITICAL(&gattSlotMux);
    s.connected = true; s.connecting = false; s.connectedAtMs = now; s.lastRssiMs = now; s.lastActivityMs = now;
    if (s.wakePreTriggered) {
        if (s.pendingPressEdges > 0) {
            s.pendingPressEdges = s.pendingPressEdges - 1;
            handedOffImmediately = true;
        } else {
            // Tap #1 already pressed and released before GATT subscribed; close Tap #1 now so Tap #2 is never swallowed
            wakeTapAlreadyReleased = true;
        }
        s.wakePreTriggered = false;
    }
    bool alreadyPressed = (s.pendingPressEdges > 0) || s.pressed;
    portEXIT_CRITICAL(&gattSlotMux);
    mqttDevicesDirty = true;
    for (auto& b : bleList) {
        if (b.address.equalsIgnoreCase(macStr)) {
            b.lastSeen = now;
            break;
        }
    }
    bool saveNvsNeeded = false;
    for (auto& m : monitoredList) {
        if (m.address.equalsIgnoreCase(macStr)) {
            bool wasInitialPair = !m.gattReady;
            m.isGatt = true;
            m.canGatt = true;
            m.gattReady = true;
            if (wasInitialPair) {
                saveNvsNeeded = true;
                m.waitReleaseAfterPair = alreadyPressed;
                m.pairHoldGuardUntilMs = alreadyPressed ? 0UL : (now + 350UL);
                if (alreadyPressed) {
                    LOGF("[GATT BTN] %s paired while held -> release button before arming.\n", macStr.c_str());
                }
            } else if (m.wakePreTriggered) {
                m.wakePreTriggered = false;
                if (handedOffImmediately) {
                    LOGF("[GATT BTN] %s wake pre-trigger handed off to live GATT link.\n", macStr.c_str());
                } else if (wakeTapAlreadyReleased) {
                    if (m.btnPhase == BTN_HELD) {
                        unsigned long relTs = m.isHose ? (m.btnPressStartMs + 100UL) : now;
                        onButtonRelease(macStr, relTs);
                    }
                    LOGF("[GATT BTN] %s quick wake tap completed on GATT connect.\n", macStr.c_str());
                }
            }
            break;
        }
    }
    if (saveNvsNeeded) {
        saveMonitoredToNvs();
    }
    setCoexScanner();
    LOGF("[GATT BTN] %s configured & ready.\n", macStr.c_str());
}

void disconnectGattButtonMac(const String& macStr) {
    for (int i = 0; i < MAX_GATT_PENDING; i++) if (gattPending[i].active && gattPending[i].mac.equalsIgnoreCase(macStr)) gattPending[i].active = false;
    clearGattBackoff(macStr);
    for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) {
        bool match = false;
        portENTER_CRITICAL(&gattSlotMux);
        match = (gattSlots[i].inUse && strcasecmp(gattSlots[i].mac, macStr.c_str()) == 0);
        portEXIT_CRITICAL(&gattSlotMux);
        if (match) {
            bool workerActiveOnSlot = (gattBtnTaskRunning.load() && gattBtnTaskSlotIdx == i);
            if (!workerActiveOnSlot && gattSlots[i].client && gattSlots[i].client->isConnected()) {
                gattSlots[i].client->disconnect();
            }
            portENTER_CRITICAL(&gattSlotMux);
            gattSlots[i].connGen = ++globalGattConnGen;
            gattSlots[i].connected = false;
            gattSlots[i].connecting = false;
            gattSlots[i].pressed = false;
            gattSlots[i].pendingPressEdges = 0;
            gattSlots[i].releaseNow = false;
            gattSlots[i].wakePreTriggered = false;
            gattSlots[i].lastPressEdgeMs = 0;
            gattSlots[i].inUse = false;
            gattSlots[i].mac[0] = '\0';
            portEXIT_CRITICAL(&gattSlotMux);
        }
    }
}

void serviceGattButton(unsigned long now) {
    if (gattBtnTaskDone.exchange(false)) {
        finishGattButtonConnect(now);
    }
    if (!requestConnect && !wifiScanInProgress && connState != STATE_CONNECTING && !extConnTaskRunning.load() && !gattBtnTaskRunning.load() && elapsedMs(now, gattBtnLastTryMs) >= 150UL) {
        for (int i = 0; i < MAX_GATT_PENDING; i++) {
            if (gattPending[i].active) {
                GattPendingReq req = gattPending[i]; gattPending[i].active = false;
                startGattButtonConnect(req.mac, req.addrType, req.btnType, req.speed, req.wakePreTrig);
                break;
            }
        }
    }
    for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) {
        GattBtnSlot& s = gattSlots[i];
        char hexCopy[48];
        char slotMacBuf[18] = {0};
        portENTER_CRITICAL(&gattSlotMux);
        strncpy(slotMacBuf, s.mac, sizeof(slotMacBuf) - 1);
        slotMacBuf[sizeof(slotMacBuf) - 1] = '\0';
        bool sleepDisc = s.sleepDiscLogPending;
        s.sleepDiscLogPending = false;
        bool rxLog = s.rxLogPending;
        s.rxLogPending = false;
        bool rxPressed = s.rxLogPressed;
        memcpy(hexCopy, s.lastHex, sizeof(hexCopy));
        uint8_t edges = s.pendingPressEdges;
        s.pendingPressEdges = 0;
        bool relNow = s.releaseNow;
        s.releaseNow = false;
        bool isPressedNow = s.pressed;
        bool isSlotConnected = (s.connected && !s.connecting && s.connectedAtMs > 0);
        unsigned long slotConnAtMs = s.connectedAtMs;
        bool slotGotAnyNotify = s.gotAnyNotify;
        portEXIT_CRITICAL(&gattSlotMux);
        String slotMac(slotMacBuf);
        if (sleepDisc) {
            mqttDevicesDirty = true;
        }

        MonitoredDevice* monPtr = findMonitoredByMac(slotMac);
        if (monPtr && !monPtr->canAdv && isSlotConnected && !slotGotAnyNotify && elapsedMs(now, slotConnAtMs) >= 600UL) {
            if (!monPtr->periodicBeacon) {
                monPtr->periodicBeacon = true;
                if (!needSaveMonitored) needSaveMonitoredAtMs = now;
                needSaveMonitored = true;
                LOGF("[GATT BTN] %s connected via idle beacon (no button press) -> wake pre-trigger disabled.\n", slotMac.c_str());
            }
        }
        if (isSlotConnected && elapsedMs(now, s.lastRssiMs) >= 5000UL) {
            s.lastRssiMs = now;
            for (auto& b : bleList) {
                if (b.address.equalsIgnoreCase(slotMac)) {
                    b.lastSeen = now;
                    break;
                }
            }
        }
        bool cfg = monPtr ? isMonitoredConfiguring(*monPtr, now) : false;
        if (rxLog) {
            if (cfg) LOGF("[GATT BTN %s] Ignored RX while Configuring: hex=[%s]\n", slotMac.c_str(), hexCopy);
            else LOGF("[GATT BTN %s] hex=[%s] -> %s\n", slotMac.c_str(), hexCopy, rxPressed ? "PRESSED (1)" : "RELEASED (0)");
        }
        if (cfg || !monPtr) {
            portENTER_CRITICAL(&gattSlotMux);
            s.pressed = false;
            s.pendingPressEdges = 0;
            s.releaseNow = false;
            portEXIT_CRITICAL(&gattSlotMux);
            continue;
        }

        if (rxLog && rxPressed && monPtr->periodicBeacon && isSlotConnected && elapsedMs(now, slotConnAtMs) < 600UL) {
            monPtr->periodicBeacon = false;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }

        if (monPtr->pairHoldGuardUntilMs > 0) {
            if (isPressedNow || edges > 0) {
                monPtr->waitReleaseAfterPair = true;
                monPtr->pairHoldGuardUntilMs = 0;
                LOGF("[GATT BTN] %s paired while held -> release button before arming.\n", slotMac.c_str());
            } else if (now >= monPtr->pairHoldGuardUntilMs) {
                monPtr->pairHoldGuardUntilMs = 0;
            }
        }

        if (monPtr->waitReleaseAfterPair) {
            if (relNow || (!isPressedNow && edges == 0 && monPtr->pairHoldGuardUntilMs == 0)) {
                monPtr->waitReleaseAfterPair = false;
                LOGF("[GATT BTN] %s released -> armed & ready.\n", slotMac.c_str());
            }
            continue;
        }

        uint8_t liveSpeed = monPtr->speed;
        if (s.wakePreTriggered && edges > 0) {
            edges--;
            s.wakePreTriggered = false;
            monPtr->wakePreTriggered = false;
            LOGF("[GATT BTN] %s wake pre-trigger handed off to live GATT link.\n", slotMac.c_str());
        }
        while (edges > 0) {
            edges--;
            if (pairedMac.length() > 0) {
                onButtonPacket(slotMac, liveSpeed, now, true);
            }
        }
        if (relNow) {
            s.wakePreTriggered = false;
            monPtr->wakePreTriggered = false;
            onButtonRelease(slotMac, now);
        } else if (isSlotConnected && s.wakePreTriggered && !isPressedNow && edges == 0 &&
                   elapsedMs(now, slotConnAtMs) >= 120UL) {
            s.wakePreTriggered = false;
            monPtr->wakePreTriggered = false;
            if (monPtr->btnPhase == BTN_HELD) {
                unsigned long relTs = monPtr->isHose ? (monPtr->btnPressStartMs + 100UL) : now;
                onButtonRelease(slotMac, relTs);
            }
            LOGF("[GATT BTN] %s quick wake tap completed before GATT link settled.\n", slotMac.c_str());
        }
        if (isSlotConnected && isPressedNow && pairedMac.length() > 0) {
            onButtonPacket(slotMac, liveSpeed, now, true);
        }
    }
}

// ============================================================================
// Core 0 BLE Scan Callback (Zero Heap Allocation on Hot Path)
// ============================================================================
class ScanCallbacks : public NimBLEScanCallbacks {
    static bool strStartsWithCI(const char* str, const char* prefix) {
        if (!str || !prefix) return false;
        while (*prefix) {
            char a = *str++;
            char b = *prefix++;
            if (a >= 'a' && a <= 'z') a -= 32;
            if (b >= 'a' && b <= 'z') b -= 32;
            if (a != b) return false;
        }
        return true;
    }

    static bool strContainsCI(const char* str, const char* needle) {
        if (!str || !needle || !*needle) return false;
        for (const char* p = str; *p; p++) {
            if (strStartsWithCI(p, needle)) return true;
        }
        return false;
    }

    void onResult(const NimBLEAdvertisedDevice* dev) override {
        unsigned long now = millis();
        const uint8_t* macVal = dev->getAddress().getVal();
        uint8_t aType = dev->getAddressType();
        int rssi = dev->getRSSI();
        uint8_t advType = dev->getAdvType();
        bool isScanRsp = (advType == 4);

        ScanEvent ev;
        memset(&ev, 0, sizeof(ev));
        ev.watts = -1;
        snprintf(ev.mac, sizeof(ev.mac), "%02x:%02x:%02x:%02x:%02x:%02x",
                 macVal[5], macVal[4], macVal[3], macVal[2], macVal[1], macVal[0]);
        ev.addrType = aType;
        ev.rssi = (int8_t)(rssi < -127 ? -127 : (rssi > 0 ? 0 : rssi));
        ev.advType = advType;
        ev.ts = now;

        bool isPairedHit = false;
        portENTER_CRITICAL(&pairedMux);
        if (pairedMacBuf[0] != '\0' && strcasecmp(ev.mac, pairedMacBuf) == 0) isPairedHit = true;
        portEXIT_CRITICAL(&pairedMux);

        if (isPairedHit) {
            pairedLastSeenMs = now; pairedRssi = rssi; pairedAddrType = aType;
            if (connState == STATE_DISCONNECTED && !requestConnect && !extConnTaskRunning.load()) pairedAdvSeenFlag.store(true);
        }

        bool isFestoolSvc = dev->isAdvertisingService(DUST_SVC_UUID);
        bool isFestoolMfg = false, isShellyPlug = false, isBurstBtnAdv = false, isGattBtnAdv = false;
        bool hasBtnSvc = false, hasFe3aSvc = false, hasFe39SvcData = false, hasFlags05 = false;
        bool isConnectable = (advType == 0 || advType == 1);
        bool hasFlags06 = false;
        if (advType == 1) {
            // Connectable directed reconnect packet (ADV_DIRECT_IND) emitted by HID switches (e.g. PTT-Z01) on wakeup
            isGattBtnAdv = true;
        }

        int parsedSoc = -1, parsedState = -1;
        int16_t parsedBtnSeq = -1;
        uint32_t parsedMatNum = 0;
        int32_t parsedWatts = -1;

        const std::vector<uint8_t>& payVec = dev->getPayload();
        const uint8_t* payPtr = payVec.data();
        size_t payLen = payVec.size();
        if (payPtr && payLen > 0) {
            if (!isScanRsp) {
                size_t pos = 0;
                for (size_t i = 0; i < payLen && pos + 4 < sizeof(ev.raw); i++) {
                    pos += snprintf(ev.raw + pos, sizeof(ev.raw) - pos, "%02X ", payPtr[i]);
                }
                if (pos > 0 && ev.raw[pos - 1] == ' ') ev.raw[pos - 1] = '\0';
            }
            size_t idx = 0;
            size_t namePos = 0;
            while (idx + 1 < payLen) {
                uint8_t fieldLen = payPtr[idx];
                if (fieldLen == 0 || idx + 1 + fieldLen > payLen) break;
                uint8_t adType = payPtr[idx + 1];
                const uint8_t* fData = payPtr + idx + 2;
                size_t fDataLen = (size_t)(fieldLen - 1);

                if (adType == 0x01 && fDataLen >= 1) {
                    uint8_t flags = fData[0];
                    if (flags == 0x05) { isBurstBtnAdv = true; hasFlags05 = true; }
                    else if (flags == 0x06) hasFlags06 = true;
                } else if ((adType == 0x02 || adType == 0x03) && fDataLen >= 2) {
                    for (size_t k = 0; k + 1 < fDataLen; k += 2) {
                        uint16_t u16 = (uint16_t)fData[k] | ((uint16_t)fData[k + 1] << 8);
                        if (u16 == 0x1812) { isGattBtnAdv = true; isConnectable = true; hasBtnSvc = true; }
                        else if (u16 == 0xFFE0) { isConnectable = true; hasBtnSvc = true; }
                        else if (u16 == 0xFE39) isFestoolSvc = true;
                        else if (u16 == 0xFE3A) { isFestoolSvc = true; hasFe3aSvc = true; isBurstBtnAdv = true; isConnectable = true; }
                    }
                } else if (adType == 0x19 && fDataLen >= 2) {
                    uint16_t app = (uint16_t)fData[0] | ((uint16_t)fData[1] << 8);
                    if (app == 0x0180) isBurstBtnAdv = true;
                    else if (app == 0x03C1 || app == 0x03C0 || app == 0x03C2) isGattBtnAdv = true;
                } else if ((adType == 0x09 || adType == 0x08) && fDataLen > 0) {
                    if (adType == 0x09 || namePos == 0) {
                        namePos = 0;
                        for (size_t k = 0; k < fDataLen && namePos + 1 < sizeof(ev.name); k++) {
                            char ch = (char)fData[k];
                            if (ch >= 32 && ch < 127) ev.name[namePos++] = ch;
                        }
                        ev.name[namePos] = '\0';
                    }
                } else if (adType == 0x16 && fDataLen >= 2) {
                    uint16_t svcUuid16 = (uint16_t)fData[0] | ((uint16_t)fData[1] << 8);
                    if (svcUuid16 == 0xFE39) {
                        isFestoolSvc = true;
                        hasFe39SvcData = true;
                        const uint8_t* sData = fData + 2;
                        size_t sLen = fDataLen - 2;
                        if (sLen >= 5) {
                            uint32_t tnr = (uint32_t)sData[2] | ((uint32_t)sData[3] << 8) | ((uint32_t)sData[4] << 16);
                            if (tnr >= 100000 && tnr <= 16777215) parsedMatNum = tnr;
                        }
                        if (sLen >= 8) {
                            uint8_t fType = sData[0];
                            bool isRemoteTnr = (parsedMatNum == 202097 || parsedMatNum == 204842 || parsedMatNum == 10029918 || parsedMatNum == 10030046);
                            if (isRemoteTnr) {
                                parsedState = (sData[7] != 0) ? 1 : 0;
                            } else if (fType == 0x01 || fType == 0x02 || fType == 0x11 || fType == 0x12) {
                                uint8_t rawSoc = sData[6];
                                if (rawSoc <= 100) parsedSoc = (int)rawSoc;
                                parsedState = ((sData[7] & 0x01) != 0) ? 1 : 0;
                            }
                        }
                    } else if (svcUuid16 == 0xFE3A) {
                        // Festool CT-F I remote button press burst (e.g. MAN button: 05 16 3a fe 03 00)
                        isFestoolSvc = true;
                        hasFe3aSvc = true;
                        isBurstBtnAdv = true;
                        isConnectable = true;
                        parsedState = 1;
                    } else if (svcUuid16 == 0xFFE0) {
                        hasBtnSvc = true;
                        isConnectable = true;
                    } else if (svcUuid16 == 0xFCD2) {
                        // BTHome v2: only classify as a button if object ID 0x3A (button event) is present
                        for (size_t k = 3; k + 1 < fDataLen; k++) {
                            if (fData[k] == 0x3A) {
                                isBurstBtnAdv = true;
                                parsedBtnSeq = (uint8_t)fData[k + 1];
                                break;
                            }
                        }
                    }
                } else if (adType == 0xFF && fDataLen >= 2) {
                    if ((fData[0] == 0x4F || fData[0] == 0x1F) && fData[1] == 0x04) {
                        isFestoolMfg = true;
                        if (fData[0] == 0x4F && fDataLen >= 6 && parsedMatNum == 0) {
                            uint32_t mfgTnr = (uint32_t)fData[3] | ((uint32_t)fData[4] << 8) | ((uint32_t)fData[5] << 16);
                            if (mfgTnr >= 100000 && mfgTnr <= 16777215) parsedMatNum = mfgTnr;
                        }
                    } else if (fDataLen >= 5 && fData[0] == 0xA9 && fData[1] == 0x0B && fData[2] == 'S' && fData[3] == 'C') {
                        isShellyPlug = true;
                        uint8_t flagsByte = fData[4];
                        bool relayOn = ((flagsByte & 0x01) != 0);
                        if (fDataLen >= 7) {
                            uint16_t wVal = (uint16_t)fData[5] | ((uint16_t)fData[6] << 8);
                            parsedWatts = relayOn ? (int32_t)wVal : 0;
                            parsedState = (relayOn && wVal > 0) ? 1 : 0;
                        } else {
                            parsedState = relayOn ? 1 : 0;
                        }
                    } else if (!isFestoolMfg && !isShellyPlug && fDataLen >= 3) {
                        uint16_t mfgId = (uint16_t)fData[0] | ((uint16_t)fData[1] << 8);
                        if (mfgId == 0x000D && fDataLen >= 4 && fDataLen <= 6) {
                            // Texas Instruments CC254x/CC2640 momentary PTT burst payload
                            isBurstBtnAdv = true;
                        }
                        parsedBtnSeq = (uint8_t)fData[fDataLen - 1];
                    }
                }
                idx += 1 + fieldLen;
            }
        }

        const char* rawNameC = ev.name;
        if (strContainsCI(rawNameC, "SHUTTER") || strContainsCI(rawNameC, "ITAG") || strContainsCI(rawNameC, "PTT-Z01")) isGattBtnAdv = true;

        bool nameIsRemote = (parsedMatNum == 202097 || parsedMatNum == 204842 || parsedMatNum == 10029918 || parsedMatNum == 10030046 ||
                             strContainsCI(rawNameC, "CT-F") || strContainsCI(rawNameC, "CTF"));
        bool nameIsExtractor = !nameIsRemote && (
                               parsedMatNum == 574830 || parsedMatNum == 574832 || parsedMatNum == 574833 ||
                               parsedMatNum == 576936 || parsedMatNum == 576944 || parsedMatNum == 577065 ||
                               parsedMatNum == 575267 || parsedMatNum == 575279 || parsedMatNum == 574947 ||
                               parsedMatNum == 574955 || parsedMatNum == 574963 ||
                               strStartsWithCI(rawNameC, "CT") || strContainsCI(rawNameC, "CTL") ||
                               strContainsCI(rawNameC, "CTM") || strContainsCI(rawNameC, "CTH") ||
                               strContainsCI(rawNameC, "CLEANTEC") || strContainsCI(rawNameC, "MIDI") ||
                               strContainsCI(rawNameC, "MINI"));
        bool nameIsPlug = isShellyPlug || strStartsWithCI(rawNameC, "SHELLY-DUST") || strStartsWithCI(rawNameC, "SCC");
        bool nameIsSwitch = strStartsWithCI(rawNameC, "PTT") || strContainsCI(rawNameC, "SHUTTER") ||
                            strContainsCI(rawNameC, "ITAG") || strContainsCI(rawNameC, "CLICKER") ||
                            strContainsCI(rawNameC, "KEYFOB");

        bool isFestoolRemote = hasFe3aSvc || nameIsRemote || (isFestoolSvc && hasFlags05 && !hasFe39SvcData && !nameIsExtractor);
        if (isFestoolRemote) {
            isBurstBtnAdv = true;
            isConnectable = false;
            if (!hasFe3aSvc && parsedState == -1) parsedState = -2;
        }

        if (isPairedHit || ((isFestoolSvc || isFestoolMfg) && !isFestoolRemote && (nameIsExtractor || (isConnectable && parsedSoc < 0)))) ev.devCat = CAT_EXTRACTOR;
        else if (nameIsPlug) ev.devCat = CAT_TOOL_PLUG;
        else if (isFestoolRemote || isGattBtnAdv || isBurstBtnAdv || hasBtnSvc || nameIsSwitch) ev.devCat = CAT_BUTTON;
        else if ((isFestoolSvc || isFestoolMfg) && parsedSoc >= 0) ev.devCat = CAT_BATTERY;
        else if (isFestoolSvc || isFestoolMfg) ev.devCat = CAT_FESTOOL;
        else ev.devCat = CAT_OTHER;

        ev.isKnown = (ev.devCat != CAT_OTHER);
        ev.soc = (int8_t)parsedSoc;
        ev.state = (int8_t)parsedState;
        ev.matNum = parsedMatNum;
        ev.watts = parsedWatts;
        ev.isGattBtnAdv = isGattBtnAdv;
        ev.isBurstBtnAdv = isBurstBtnAdv;
        ev.isShellyPlug = isShellyPlug;
        ev.isFestoolRemote = isFestoolRemote;
        ev.isConnectable = isConnectable;
        ev.hasFlags06 = hasFlags06;
        ev.btnSeq = parsedBtnSeq;

        bool isMonHit = false;
        portENTER_CRITICAL(&monMacMux);
        for (uint8_t mi = 0; mi < monMacCacheCount; mi++) {
            if (strcasecmp(ev.mac, monMacCache[mi]) == 0) { isMonHit = true; break; }
        }
        portEXIT_CRITICAL(&monMacMux);
        if (!ev.isKnown && !isPairedHit && !isMonHit && !(isScanRsp && nameIsExtractor)) {
            return;
        }

        pushScanEvent(ev);
    }
};

const char* devCatToTypeStr(uint8_t cat) {
    switch (cat) {
        case CAT_EXTRACTOR: return "Extractor";
        case CAT_BATTERY:   return "Battery";
        case CAT_FESTOOL:   return "Festool";
        case CAT_TOOL_PLUG: return "Tool Plug";
        case CAT_BUTTON:    return "Button";
        default:            return "Other";
    }
}

void processSingleScanEvent(const ScanEvent& ev, unsigned long now) {
    String addr = ev.mac;
    uint8_t aType = ev.addrType;
    String name = ev.name;
    int rssi = ev.rssi;
    uint8_t advType = ev.advType;
    bool isScanRsp = (advType == 4);
    int parsedSoc = ev.soc;
    int parsedState = ev.state;
    uint32_t parsedMatNum = ev.matNum;
    int32_t parsedWatts = ev.watts;
    bool isKnown = ev.isKnown;
    bool isGattBtnAdv = ev.isGattBtnAdv;
    bool isBurstBtnAdv = ev.isBurstBtnAdv;
    bool isShellyPlug = ev.isShellyPlug;
    String parsedRaw = ev.raw;
    String festoolMatch = (parsedMatNum > 0) ? lookupFestoolModelByTnr(parsedMatNum) : String("");
    String devType = devCatToTypeStr(ev.devCat);

    BleEntry* blePtr = nullptr;
    for (auto& b : bleList) {
        if (b.address.equalsIgnoreCase(addr)) { blePtr = &b; break; }
    }
    if (blePtr) {
        if (ev.isConnectable) blePtr->canGatt = true;
        if (isBurstBtnAdv) blePtr->canAdv = true;
        if (!isScanRsp) {
            if (blePtr->lastPrimaryAdvMs > 0) {
                unsigned long dt = elapsedMs(ev.ts, blePtr->lastPrimaryAdvMs);
                if (dt > 0 && dt < 250UL) {
                    if (blePtr->fastWakeHits < 10) blePtr->fastWakeHits++;
                    if (dt < 130UL) {
                        if (blePtr->fastCadenceHits < 10) blePtr->fastCadenceHits++;
                        blePtr->canAdv = true;
                    }
                } else if (dt >= 350UL) {
                    blePtr->fastWakeHits = 0;
                    if (!blePtr->canAdv && (isGattBtnAdv || ev.hasFlags06 || ev.devCat == CAT_BUTTON)) {
                        if (blePtr->slowCadenceHits < 10) blePtr->slowCadenceHits++;
                    }
                }
            }
            blePtr->lastPrimaryAdvMs = ev.ts;
        }
    }

    bool knownCanAdv = isBurstBtnAdv || (blePtr && blePtr->canAdv);
    bool knownGattOnly = !knownCanAdv && (isGattBtnAdv || (blePtr && blePtr->slowCadenceHits >= 1));

    if (knownCanAdv) {
        parsedRaw = "ADV:STREAM";
    } else if (knownGattOnly && (parsedRaw.length() == 0 || !parsedRaw.startsWith("GATT"))) {
        parsedRaw = "GATT:FFE0/HID";
    }

    String friendlyName = "Unknown";
    if (festoolMatch.length() > 0) friendlyName = festoolMatch;
    else if (pairedMac.length() > 0 && addr.equalsIgnoreCase(pairedMac)) friendlyName = extFriendlyName;
    else if (name.length() > 0) friendlyName = name;
    else if (isShellyPlug) friendlyName = "Shelly Tool Plug";
    else if (ev.isFestoolRemote) friendlyName = "CT-F I Remote";
    else if (ev.devCat == CAT_BATTERY) friendlyName = "Festool Battery";
    else if (ev.devCat == CAT_EXTRACTOR) friendlyName = "Festool Extractor";
    else if (ev.devCat == CAT_FESTOOL) friendlyName = "Festool";
    else if (ev.devCat == CAT_BUTTON && isGattBtnAdv) friendlyName = "HID Switch";
    MonitoredDevice* mon = findMonitoredByMac(addr);
    int monSpeed = -1;
    uint8_t monBtnType = 0;
    bool monIsGatt = false;
    bool monConfiguring = false;
    if (mon) {
        monSpeed = mon->speed;
        monBtnType = mon->btnType;
        if ((aType == 0 || aType == 1) && mon->addrType != aType) {
            mon->addrType = aType;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (name.length() > 0 && (mon->advName.length() == 0 || name.length() > mon->advName.length())) {
            mon->advName = name;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (parsedMatNum != 0 && mon->matNum != parsedMatNum) {
            mon->matNum = parsedMatNum;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (ev.devCat != CAT_OTHER && mon->devCat != ev.devCat) {
            mon->devCat = ev.devCat;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (mon->btnType > 0 && ev.isConnectable && !mon->canGatt) {
            mon->canGatt = true;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (mon->btnType > 0 && knownCanAdv && !mon->canAdv) {
            mon->canAdv = true;
            mon->periodicBeacon = false;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (mon->btnType > 0 && mon->canAdv && mon->periodicBeacon) {
            mon->periodicBeacon = false;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        if (mon->btnType > 0 && !mon->canAdv && blePtr && blePtr->slowCadenceHits >= 2 && !mon->periodicBeacon) {
            mon->periodicBeacon = true;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
        // GATT by exception: if an unbranded button was added passively on Packet #1
        // and subsequent packets prove it is GATT-only (no burst packets), promote automatically
        if (mon->btnType > 0 && !mon->isGatt && !mon->canAdv && knownGattOnly) {
            mon->isGatt = true;
            mon->canGatt = true;
            mon->activeRaw = "GATT:FFE0/HID";
            if (!isGattMacConnectedOrBusy(addr)) {
                mon->gattReady = false;
            }
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
            LOGF("[AUTO GATT] Exception triggered for %s -> promoted to GATT switch\n", addr.c_str());
        }
        monIsGatt = mon->isGatt;
        monConfiguring = isMonitoredConfiguring(*mon, now);
        if (!mon->customNamed && name.length() > 0 &&
            (mon->name.length() == 0 || name.length() > mon->name.length() || mon->name == "Device" || mon->name == "Button")) {
            mon->name = name;
            if (!needSaveMonitored) needSaveMonitoredAtMs = now;
            needSaveMonitored = true;
        }
    }

    if (mon) {
        if (monBtnType >= 1 && monBtnType <= 5) {
            devType = "Button";
            if (monIsGatt) {
                int gIdx = findGattSlotByMac(addr);
                bool busyOrConn = isGattMacConnectedOrBusy(addr);
                bool alreadyActiveBtn = (mon->btnPhase != BTN_IDLE);
                parsedState = ((gIdx >= 0 && gattSlots[gIdx].pressed) || alreadyActiveBtn) ? 1 : 0;
                if (!busyOrConn) {
                    bool isDirectedWake = (advType == 1);
                    bool allowWakePreTrig = isDirectedWake || (mon->canAdv && !mon->periodicBeacon);
                    bool canPreTrig = (!isScanRsp &&
                                       allowWakePreTrig &&
                                       mon->gattReady &&
                                       !monConfiguring &&
                                       !mon->waitReleaseAfterPair &&
                                       mon->pairHoldGuardUntilMs == 0 &&
                                       !alreadyActiveBtn &&
                                       !isGattPending(addr) &&
                                       !isGattBackedOff(addr, ev.ts) &&
                                       pairedMac.length() > 0);
                    if (canPreTrig) {
                        mon->wakePreTriggered = true;
                        mon->wakePreTriggerMs = ev.ts;
                        parsedState = 1;
                        LOGF("[GATT BTN] Wake packet pre-trigger -> %s at %u%%\n", addr.c_str(), (unsigned)monSpeed);
                        onButtonPacket(addr, (uint8_t)monSpeed, ev.ts, true);
                    }
                    enqueueGattConnect(addr, aType, monBtnType, (uint8_t)monSpeed, false, canPreTrig);
                }
            } else if (!monConfiguring && !isScanRsp) {
                if (parsedState == -2) {
                    // CT-F I remotes are strictly ON/OFF via MAN button; ignore Bluetooth pairing button packets
                } else if (parsedState == 0) {
                    if (mon->btnPhase == BTN_HELD) onButtonRelease(addr, ev.ts);
                } else {
                    parsedState = 1;
                    onButtonPacket(addr, (uint8_t)monSpeed, ev.ts, false, ev.btnSeq);
                }
            }
        } else if (monBtnType == 0 && (parsedWatts >= 0 || parsedState != -1)) {
            int effState = parsedState;
            if (parsedWatts >= 0) {
                if (mon->lastWatts < 0 || abs(parsedWatts - mon->lastWatts) >= 5) {
                    mqttDevicesDirty = true;
                }
                mon->lastWatts = parsedWatts;
                uint16_t onThr = (mon->wattsThr >= 5) ? mon->wattsThr : 60;
                effState = ((uint32_t)parsedWatts >= onThr) ? 1 : 0;
                parsedState = effState;
            }
            if (effState == 1) {
                bool wasOff = !mon->toolActive;
                mon->toolActive = true;
                mon->toolLastSeen = ev.ts;
                if (wasOff) {
                    mon->liveSpeedOverride = 0;
                    mqttDevicesDirty = true;
                    if (parsedWatts >= 0) LOGF("[TOOL PLUG] Load ON (%ldW >= %uW) -> %u%% (%s)\n", (long)parsedWatts, (unsigned)mon->wattsThr, (unsigned)monSpeed, addr.c_str());
                    else LOGF("[AUTO TOOL] Load ON -> %u%% (%s)\n", (unsigned)monSpeed, addr.c_str());
                    hoseClearActive = false;
                }
                syncToolBattDemandFromMonitored(ev.ts);
            } else if (effState == 0 && mon->toolActive) {
                mon->toolActive = false;
                mon->liveSpeedOverride = 0;
                mqttDevicesDirty = true;
                if (parsedWatts >= 0) LOGF("[TOOL PLUG] Load OFF (%ldW < %uW) -> %s\n", (long)parsedWatts, (unsigned)mon->wattsThr, addr.c_str());
                else LOGF("[AUTO TOOL] Load OFF -> %s\n", addr.c_str());
                syncToolBattDemandFromMonitored(ev.ts);
                if (!toolBattDemandActive && !isAnyPrimaryDemandActive()) {
                    if (evacSeconds > 0) {
                        LOGF("[AUTO TOOL] Entering %us debris evacuation at 20%%\n", evacSeconds);
                        hoseClearActive = true;
                        hoseClearTimer = ev.ts;
                    } else {
                        forceStopNow = true;
                    }
                    demandDirty = true;
                }
            }
        }
    }

    if (blePtr) {
        if (name.length() > 0) blePtr->advName = name;
        if (friendlyName != "Unknown" && (blePtr->name == "Unknown" || blePtr->name == "Festool" || blePtr->name == "HID Switch" || festoolMatch.length() > 0 || name.length() > 0)) {
            if (!(blePtr->name.startsWith("CT-F I") && friendlyName == "CT-F I Remote")) {
                blePtr->name = friendlyName;
            }
        }
        if (aType == 0 || aType == 1) blePtr->addrType = aType;
        blePtr->rssi = rssi;
        if (isKnown) blePtr->isKnownDevice = true;
        if (devType != "Other") blePtr->type = devType;
        blePtr->lastSeen = ev.ts;
        if (parsedSoc >= 0) {
            if (blePtr->soc != parsedSoc) mqttDevicesDirty = true;
            blePtr->soc = parsedSoc;
        }
        if (parsedState != -1) {
            if (blePtr->state != parsedState) mqttDevicesDirty = true;
            blePtr->state = parsedState;
        }
        if (parsedMatNum > 0) blePtr->matNum = parsedMatNum;
        if (parsedWatts >= 0) blePtr->watts = parsedWatts;
        if (blePtr->canAdv) {
            blePtr->rawData = "ADV:STREAM";
        } else if (parsedRaw.length() > 0) {
            blePtr->rawData = parsedRaw;
        }
    } else if (isKnown || monSpeed != -1 || (pairedMac.length() > 0 && addr.equalsIgnoreCase(pairedMac))) {
        if (bleList.size() >= MAX_BLE_LIST_ENTRIES) {
            pruneStaleBleEntries(now);
            if (bleList.size() >= MAX_BLE_LIST_ENTRIES) {
                for (auto it = bleList.begin(); it != bleList.end(); ++it) {
                    bool isPinned = (pairedMac.length() > 0 && it->address.equalsIgnoreCase(pairedMac));
                    if (!isPinned && findMonitoredByMac(it->address) == nullptr) {
                        bleList.erase(it);
                        break;
                    }
                }
            }
        }
        BleEntry newEntry = {friendlyName, name, addr, aType, rssi, isKnown, devType, ev.ts, parsedSoc, parsedState, parsedMatNum, parsedWatts, parsedRaw, isBurstBtnAdv, ev.isConnectable, isScanRsp ? 0UL : ev.ts, 0, 0, 0};
        bleList.push_back(newEntry);
        mqttDevicesDirty = true;
    }
}

void drainScanEvents(unsigned long now) {
    ScanEvent ev; int processed = 0;
    while (processed < 32 && popScanEvent(ev)) { processSingleScanEvent(ev, now); processed++; }
}

void extConnectWorkerTask(void* param) {
    ExtConnTaskParams* p = static_cast<ExtConnTaskParams*>(param);
    bool ok = false;
    if (p && p->client) {
        NimBLEAddress addr(p->mac, p->addrType);
        if (p->client->connect(addr)) {
            ok = p->client->secureConnection();
            if (!ok && p->client->isConnected()) {
                p->client->disconnect();
            }
        }
    }
    delete p;
    extConnTaskSuccess.store(ok);
    extConnTaskRunning.store(false);
    extConnTaskDone.store(true);
    vTaskDelete(nullptr);
}

void startBleConnect(const String& macStr, uint8_t forcedType = 255) {
    if (extConnTaskRunning.load() || gattBtnTaskRunning.load() || macStr.length() == 0) return;
    NimBLEDevice::setOwnAddrType(BLE_OWN_ADDR_PUBLIC);
    connState = STATE_CONNECTING;
    NimBLEDevice::getScan()->stop();
    LOGF("[BLE] >>> Connecting to Extractor (GATT App): %s ...\n", macStr.c_str());

    uint8_t addrType = 0;
    if (forcedType != 255) addrType = forcedType;
    else for (const auto& item : bleList) if (item.address.equalsIgnoreCase(macStr)) { addrType = item.addrType; break; }
    addrType = inferRandomAddrType(macStr, addrType);

    if (!pClient) { pClient = NimBLEDevice::createClient(); pClient->setClientCallbacks(new ClientCallbacks(), false); }
    pClient->setConnectTimeout((forcedType == 255) ? 2000 : 1200);

    ExtConnTaskParams* taskParams = new ExtConnTaskParams();
    taskParams->client = pClient;
    strncpy(taskParams->mac, macStr.c_str(), sizeof(taskParams->mac) - 1);
    taskParams->mac[sizeof(taskParams->mac) - 1] = '\0';
    taskParams->addrType = addrType;

    extConnTaskMac = macStr;
    extConnTaskAddrType = addrType;
    extConnTaskForcedType = forcedType;
    extConnTaskSuccess.store(false);
    extConnTaskDone.store(false);
    extConnTaskRunning.store(true);
    if (xTaskCreatePinnedToCore(extConnectWorkerTask, "extBleConn", 6144, taskParams, 1, nullptr, 1) != pdPASS) {
        delete taskParams;
        extConnTaskRunning.store(false);
        connState = STATE_DISCONNECTED;
        setCoexScanner();
    }
}

void finishBleConnect(unsigned long now) {
    bool ok = extConnTaskSuccess.load();
    String macStr = extConnTaskMac;
    uint8_t addrType = extConnTaskAddrType;
    uint8_t forcedType = extConnTaskForcedType;

    if (extUnpairPending.exchange(false) || (forcedType != 255 && pairedMac.length() == 0)) {
        if (pClient && pClient->isConnected()) pClient->disconnect();
        connState = STATE_DISCONNECTED;
        setCoexScanner();
        return;
    }

    if (!ok || !pClient || !pClient->isConnected()) {
        LOGLN("[BLE] Connect or security handshake failed. Resuming scanner.");
        if (pClient && pClient->isConnected()) pClient->disconnect();
        lastExtConnectFailMs = now;
        connState = STATE_DISCONNECTED; setCoexScanner();
        for (auto& m : monitoredList) {
            if (m.btnType > 0 && m.btnPhase == BTN_HELD) {
                resetMonitoredButtonGesture(m, false);
            }
        }
        syncButtonDemandsFromMonitored();
        return;
    }

    LOGLN("[BLE] Security complete -> discovering GATT...");
    pWriteChar = nullptr; pNotifyChar = nullptr;

    NimBLERemoteService* pSvc = pClient->getService(DUST_SVC_UUID);
    if (pSvc) {
        pNotifyChar = pSvc->getCharacteristic(CHAR_NOTIFY_UUID);
        pWriteChar  = pSvc->getCharacteristic(CHAR_WRITE_UUID);
        if (pNotifyChar && pNotifyChar->canNotify()) { pNotifyChar->subscribe(true, onFe02Notify); LOGLN("[BLE] Subscribed to 3734fe02 notifications"); }
        if (pWriteChar) LOGLN("[BLE] Bound 3734fe03 FMP V2 command characteristic");
    }

    if (!pWriteChar || !pNotifyChar || !pClient->isConnected()) {
        LOGLN("[BLE] Missing FMP V2 GATT characteristics or link dropped -> disconnecting.");
        if (pClient && pClient->isConnected()) pClient->disconnect();
        lastExtConnectFailMs = now;
        connState = STATE_DISCONNECTED; setCoexScanner();
        return;
    }

    lastExtConnectFailMs = 0;
    connState = STATE_CONNECTED;
    LOGLN("[BLE] GATT connection complete & FMP V2 ready!");

    setPairedMacState(macStr, addrType);
    prefs.putString("paired_mac", pairedMac);
    prefs.putUChar("paired_type", pairedAddrType);
    publishExtractorTelemetry(now);

    bool removedStaleMon = false;
    for (auto it = monitoredList.begin(); it != monitoredList.end(); ) {
        if (it->address.equalsIgnoreCase(macStr)) {
            disconnectGattButtonMac(macStr);
            it = monitoredList.erase(it);
            removedStaleMon = true;
        } else {
            ++it;
        }
    }
    if (removedStaleMon) {
        saveMonitoredToNvs();
        LOGF("[BLE] Removed paired extractor %s from Monitored Devices.\n", macStr.c_str());
    }

    setCoexScanner();
    for (auto& m : monitoredList) {
        if (m.btnType > 0 && m.btnPhase == BTN_HELD) {
            resetMonitoredButtonGesture(m, false);
        }
    }
    syncButtonDemandsFromMonitored();
    connectedAtMs = now; lastBleActivityMs = connectedAtMs;
    postConnectActionPending = true;
    postConnectActionAtMs = now + 60UL;
    initialTelemDone = false; telemPollRequested = false; telemAwaitingReply = false;
}

// ============================================================================
// USB Serial Console & Improv Wi-Fi Serial Provisioning (ESP Web Tools)
// ============================================================================
uint8_t improvRxBuf[260];
size_t improvRxLen = 0;
size_t improvExpectedLen = 0;
char serialLineBuf[192];
size_t serialLineLen = 0;
bool improvProvPending = false;
unsigned long improvProvStartMs = 0;
String improvProvSsid = "";
String improvProvPass = "";

void improvSendPacket(uint8_t type, const uint8_t* data, uint8_t len) {
    uint8_t pkt[264];
    size_t idx = 0;
    pkt[idx++] = 'I'; pkt[idx++] = 'M'; pkt[idx++] = 'P';
    pkt[idx++] = 'R'; pkt[idx++] = 'O'; pkt[idx++] = 'V';
    pkt[idx++] = 0x01;
    pkt[idx++] = type;
    pkt[idx++] = len;
    if (len > 0 && data) {
        memcpy(pkt + idx, data, len);
        idx += len;
    }
    uint8_t csum = 0;
    for (size_t i = 0; i < idx; i++) csum = (uint8_t)(csum + pkt[i]);
    pkt[idx++] = csum;
    pkt[idx++] = 0x0A;
    if (logMutex && xSemaphoreTake(logMutex, pdMS_TO_TICKS(50)) == pdTRUE) {
        Serial.write(pkt, idx);
        xSemaphoreGive(logMutex);
    } else {
        Serial.write(pkt, idx);
    }
}

void improvSendState(uint8_t state) {
    improvSendPacket(0x01, &state, 1);
}

void improvSendError(uint8_t err) {
    improvSendPacket(0x02, &err, 1);
}

void improvSendRpcResult(uint8_t cmd, const std::vector<String>& strings) {
    uint8_t buf[240];
    size_t pos = 2;
    for (const auto& s : strings) {
        uint8_t sl = (uint8_t)(s.length() > 64 ? 64 : s.length());
        if (pos + 1 + sl >= sizeof(buf)) break;
        buf[pos++] = sl;
        memcpy(buf + pos, s.c_str(), sl);
        pos += sl;
    }
    buf[0] = cmd;
    buf[1] = (uint8_t)(pos - 2);
    improvSendPacket(0x04, buf, (uint8_t)pos);
}

String getDeviceWebUrl() {
    if (WiFi.status() == WL_CONNECTED) {
        return "http://" + WiFi.localIP().toString() + "/";
    }
    return "http://192.168.4.1/";
}

void handleImprovRpcCommand(const uint8_t* data, uint8_t len, unsigned long now) {
    if (len < 1) return;
    uint8_t cmd = data[0];
    if (cmd == 0x02) { // GET_CURRENT_STATE
        if (improvProvPending) {
            improvSendState(0x03);
        } else if (WiFi.status() == WL_CONNECTED) {
            improvSendState(0x04);
            improvSendRpcResult(0x02, { getDeviceWebUrl() });
        } else {
            improvSendState(0x02);
        }
    } else if (cmd == 0x03) { // GET_DEVICE_INFO
        improvSendRpcResult(0x03, { "BLE Dust Bridge", "1.0.0", "ESP32-S3", "BLE-Dust-Bridge" });
    } else if (cmd == 0x04) { // GET_WIFI_NETWORKS
        if (extConnTaskRunning.load() || gattBtnTaskRunning.load() || connState == STATE_CONNECTING) {
            improvSendRpcResult(0x04, {});
            return;
        }
        wifiScanInProgress = true;
        NimBLEDevice::getScan()->stop();
        if (WiFi.status() != WL_CONNECTED) {
            WiFi.disconnect(false);
        }
        delay(20);
        int n = WiFi.scanNetworks(false, true);
        struct ScanNet { String ssid; int rssi; bool enc; };
        std::vector<ScanNet> nets;
        for (int i = 0; i < n; i++) {
            String ssid = WiFi.SSID(i);
            if (ssid.length() == 0) continue;
            int rssi = WiFi.RSSI(i);
            bool enc = (WiFi.encryptionType(i) != WIFI_AUTH_OPEN);
            bool found = false;
            for (auto& u : nets) {
                if (u.ssid == ssid) {
                    if (rssi > u.rssi) { u.rssi = rssi; u.enc = enc; }
                    found = true;
                    break;
                }
            }
            if (!found) nets.push_back({ssid, rssi, enc});
        }
        std::sort(nets.begin(), nets.end(), [](const ScanNet& a, const ScanNet& b) { return a.rssi > b.rssi; });
        for (const auto& u : nets) {
            improvSendRpcResult(0x04, { u.ssid, String(u.rssi), u.enc ? "YES" : "NO" });
        }
        improvSendRpcResult(0x04, {});
        WiFi.scanDelete();
        wifiScanInProgress = false;
        setCoexScanner();
    } else if (cmd == 0x01) { // SEND_WIFI_SETTINGS
        if (len < 4) {
            improvSendError(0x02);
            return;
        }
        uint8_t ssidLen = data[2];
        if (3 + ssidLen >= len) {
            improvSendError(0x02);
            return;
        }
        String ssid = "";
        for (uint8_t i = 0; i < ssidLen; i++) ssid += (char)data[3 + i];
        uint8_t passLen = data[3 + ssidLen];
        if (4 + ssidLen + passLen > len) {
            improvSendError(0x02);
            return;
        }
        String pass = "";
        for (uint8_t i = 0; i < passLen; i++) pass += (char)data[4 + ssidLen + i];
        ssid.trim();
        if (ssid.length() == 0) {
            improvSendError(0x02);
            return;
        }

        for (auto it = wifiList.begin(); it != wifiList.end(); ) {
            if (it->ssid.equalsIgnoreCase(ssid)) it = wifiList.erase(it);
            else ++it;
        }
        wifiList.insert(wifiList.begin(), {ssid, pass});
        if (wifiList.size() > 5) wifiList.resize(5);
        bgWifiIdx = 0;
        saveWifiListToNvs();

        improvProvSsid = ssid;
        improvProvPass = pass;
        improvProvPending = true;
        improvProvStartMs = now;
        improvSendState(0x03);
        LOGF("[IMPROV] Provisioning Wi-Fi SSID: %s...\n", ssid.c_str());

        if (WiFi.getMode() == WIFI_AP) {
            WiFi.mode(WIFI_AP_STA);
        }
        WiFi.disconnect(false);
        delay(30);
        WiFi.begin(ssid.c_str(), pass.c_str());
    }
}

void printSerialStatusBanner() {
    String ipStr = (WiFi.status() == WL_CONNECTED) ? WiFi.localIP().toString() : WiFi.softAPIP().toString();
    const char* modeStr = (WiFi.status() == WL_CONNECTED) ? "STA" : "AP (BLE_Dust_Bridge)";
    LOGF("[BLDB] Console Ready | Wi-Fi: %s (%s) | BLE MAC: %s | Extractor: %s\n",
         modeStr,
         ipStr.c_str(),
         NimBLEDevice::getAddress().toString().c_str(),
         pairedMac.length() > 0 ? pairedMac.c_str() : "UNPAIRED");
}

void serviceSerialAndImprov(unsigned long now) {
    static bool prevSerialConnected = false;
    bool serialConnected = (bool)Serial;
    if (serialConnected && !prevSerialConnected) {
        printSerialStatusBanner();
    }
    prevSerialConnected = serialConnected;

    while (Serial.available() > 0) {
        uint8_t b = (uint8_t)Serial.read();
        if (improvRxLen == 0 && b != 'I') {
            if (b == '\r' || b == '\n') {
                if (serialLineLen > 0) {
                    serialLineBuf[serialLineLen] = '\0';
                    String rawLine(serialLineBuf);
                    String cmd = rawLine;
                    cmd.trim();
                    cmd.toLowerCase();
                    if (cmd == "status" || cmd == "help" || cmd == "info") {
                        printSerialStatusBanner();
                    } else if (cmd.startsWith("bldb_set_auth ")) {
                        String jsonPart = rawLine;
                        jsonPart.trim();
                        jsonPart = jsonPart.substring(14);
                        jsonPart.trim();
                        StaticJsonDocument<256> doc;
                        if (deserializeJson(doc, jsonPart) == DeserializationError::Ok) {
                            bool en = doc["en"] | false;
                            if (!en) {
                                auth_en = false;
                                clearAllAuthSessions();
                                prefs.putBool("auth_init", true);
                                prefs.putBool("auth_en", false);
                                LOGLN("[SERIAL] Web UI login disabled (None) via Web Installer.");
                            } else {
                                String u = doc["user"] | "";
                                String p = doc["pass"] | "";
                                u.trim();
                                if (u.length() > 0 && p.length() > 0) {
                                    auth_en = true;
                                    auth_user = u;
                                    auth_salt = generateRandomHex(16);
                                    auth_hash = sha256Hex(auth_salt + ":" + auth_user + ":" + p);
                                    clearAllAuthSessions();
                                    prefs.putBool("auth_init", true);
                                    prefs.putBool("auth_en", true);
                                    prefs.putString("auth_user", auth_user);
                                    prefs.putString("auth_salt", auth_salt);
                                    prefs.putString("auth_hash", auth_hash);
                                    LOGF("[SERIAL] Web UI login configured for '%s' via Web Installer.\n", auth_user.c_str());
                                }
                            }
                        }
                    }
                    serialLineLen = 0;
                } else if (b == '\n') {
                    printSerialStatusBanner();
                }
            } else if (b >= 32 && b < 127 && serialLineLen + 1 < sizeof(serialLineBuf)) {
                serialLineBuf[serialLineLen++] = (char)b;
            }
            continue;
        }

        const char magic[6] = {'I', 'M', 'P', 'R', 'O', 'V'};
        if (improvRxLen < 6) {
            if (b == (uint8_t)magic[improvRxLen]) {
                improvRxBuf[improvRxLen++] = b;
            } else {
                improvRxLen = 0;
            }
            continue;
        }

        improvRxBuf[improvRxLen++] = b;
        if (improvRxLen == 9) {
            improvExpectedLen = 10 + (size_t)improvRxBuf[8];
            if (improvExpectedLen > sizeof(improvRxBuf)) {
                improvRxLen = 0;
                improvExpectedLen = 0;
            }
        }
        if (improvExpectedLen > 0 && improvRxLen >= improvExpectedLen) {
            uint8_t csum = 0;
            for (size_t i = 0; i < improvExpectedLen - 1; i++) {
                csum = (uint8_t)(csum + improvRxBuf[i]);
            }
            if (csum == improvRxBuf[improvExpectedLen - 1] && improvRxBuf[6] == 0x01 && improvRxBuf[7] == 0x03) {
                handleImprovRpcCommand(improvRxBuf + 9, improvRxBuf[8], now);
            } else if (csum != improvRxBuf[improvExpectedLen - 1]) {
                improvSendError(0x01);
            }
            improvRxLen = 0;
            improvExpectedLen = 0;
        }
    }

    if (improvProvPending) {
        if (WiFi.status() == WL_CONNECTED && WiFi.SSID() == improvProvSsid) {
            improvProvPending = false;
            improvSendState(0x04);
            improvSendRpcResult(0x01, { getDeviceWebUrl() });
            LOGF("[IMPROV] Wi-Fi connected! URL: %s\n", getDeviceWebUrl().c_str());
        } else if (elapsedMs(now, improvProvStartMs) >= 15000UL) {
            improvProvPending = false;
            improvSendError(0x03);
            improvSendState(0x02);
            LOGLN("[IMPROV] Wi-Fi connection timed out.");
        }
    }
}

void buildStatusJson(String& out) {
    static DynamicJsonDocument doc(8192);
    doc.clear();
    unsigned long now = millis();
    unsigned long evacRemMs = 0;
    if (hoseClearActive && evacSeconds > 0) {
        unsigned long totalMs = (unsigned long)evacSeconds * 1000UL;
        unsigned long elapsed = elapsedMs(now, hoseClearTimer);
        if (elapsed < totalMs) evacRemMs = totalMs - elapsed;
    }

    uint8_t gattSlotsUsed = 0;
    for (int i = 0; i < MAX_GATT_BTN_SLOTS; i++) {
        if (gattSlots[i].connected || gattSlots[i].connecting) gattSlotsUsed++;
    }
    uint8_t gattSwitchesCfg = 0;
    for (const auto& m : monitoredList) {
        if (m.btnType > 0 && m.isGatt) gattSwitchesCfg++;
    }

    doc["state"] = (connState == STATE_CONNECTED ? "CONNECTED" : (connState == STATE_CONNECTING ? "CONNECTING" : "DISCONNECTED"));
    doc["auth_en"] = auth_en;
    doc["power"] = currentPowerState; doc["speed"] = currentSuctionPct;
    doc["preset_speed"] = activePresetSpeed; doc["override_speed"] = getActiveLiveSpeedOverride();
    doc["paired_mac"] = pairedMac; doc["paired_rssi"] = pairedRssi;
    doc["ext_name"] = extFriendlyName; doc["evac_sec"] = evacSeconds; doc["evac_rem_ms"] = evacRemMs;
    doc["gatt_slots_used"] = gattSlotsUsed;
    doc["gatt_slots_max"] = MAX_GATT_BTN_SLOTS;
    doc["gatt_switches_cfg"] = gattSwitchesCfg;

    ExtractorTelemetry tSnap;
    portENTER_CRITICAL(&telemMux); tSnap = extTelem; portEXIT_CRITICAL(&telemMux);
    JsonObject tObj = doc.createNestedObject("telem");
    tObj["motor_sec"] = tSnap.motorRunSec; tObj["cycles"] = tSnap.operatingCycles; tObj["filter_sec"] = tSnap.filterRunSec;
    tObj["water_active"] = tSnap.waterLevelActive; tObj["temp1_f"] = tSnap.temp1F; tObj["temp2_f"] = tSnap.temp2F;
    tObj["faults"] = tSnap.faultText; tObj["model"] = tSnap.modelName;
    tObj["sw_ver"] = "V " + String(tSnap.mainSwMajor) + "/" + String(tSnap.bleSwMajor);
    tObj["main_fw"] = tSnap.mainFw; tObj["ble_fw"] = tSnap.bleFw;

    JsonArray monArr = doc.createNestedArray("monitored");
    for (auto& m : monitoredList) {
        JsonObject o = monArr.createNestedObject();
        int gSlot = m.isGatt ? findGattSlotByMac(m.address) : -1;
        bool gattLinked = (gSlot >= 0) && (gattSlots[gSlot].connected || gattSlots[gSlot].connecting);
        bool btnLive = false;
        if (m.btnType > 0 && !m.waitReleaseAfterPair) {
            if (m.isGatt) {
                bool gattPressed = (gSlot >= 0 && gattSlots[gSlot].connected && gattSlots[gSlot].pressed);
                bool gestureHeld = (m.btnPhase == BTN_HELD);
                btnLive = gattPressed || gestureHeld;
            } else {
                btnLive = (m.btnPhase == BTN_HELD) || (m.toolActive && (m.toolLastSeen > 0 && elapsedMs(now, m.toolLastSeen) < ADV_TOGGLE_TAP_RELEASE_MS));
            }
        }
        const BleEntry* liveBle = nullptr;
        for (const auto& b : bleList) {
            if (b.address.equalsIgnoreCase(m.address)) { liveBle = &b; break; }
        }
        uint32_t effMat = (m.matNum > 0) ? m.matNum : (liveBle ? liveBle->matNum : 0);
        String effAdvName = m.advName;
        if (effAdvName.length() == 0 && liveBle && liveBle->advName.length() > 0) effAdvName = liveBle->advName;
        String effModel = lookupFestoolModelByTnr(effMat);
        String effDevType = (m.btnType > 0) ? "Button" : devCatToTypeStr(m.devCat);
        if (effDevType == "Other" && liveBle && liveBle->type.length() > 0 && liveBle->type != "Other") {
            effDevType = liveBle->type;
        }
        if (effDevType == "Other") {
            String lowRaw = m.activeRaw; lowRaw.toLowerCase();
            String lowAdv = effAdvName; lowAdv.toLowerCase();
            if (effMat > 0) effDevType = "Battery";
            else if (lowAdv.startsWith("shelly") || lowAdv.startsWith("scc") || lowRaw.indexOf("a9 0b 53 43") != -1) effDevType = "Tool Plug";
            else effDevType = "Auto Tool";
        }
        o["mac"] = m.address; o["name"] = m.name; o["adv_name"] = effAdvName; o["model_name"] = effModel;
        o["dev_type"] = effDevType; o["mat_num"] = effMat;
        bool hasFreshRssi = (liveBle && liveBle->rssi < 0 && (liveBle->lastSeen == 0 || elapsedMs(now, liveBle->lastSeen) <= 300000UL));
        o["rssi"] = hasFreshRssi ? liveBle->rssi : 0;
        o["rssi_age"] = (liveBle && liveBle->lastSeen > 0) ? elapsedMs(now, liveBle->lastSeen) : 999999UL;
        o["soc"] = liveBle ? liveBle->soc : -1;
        o["watts_thr"] = m.wattsThr;
        o["watts"] = (liveBle && liveBle->watts >= 0) ? liveBle->watts : m.lastWatts;
        o["speed"] = m.speed; o["btnType"] = m.btnType;
        o["is_gatt"] = m.isGatt; o["can_adv"] = m.canAdv; o["can_gatt"] = m.canGatt;
        o["is_hose"] = (m.isGatt && m.isHose); o["gatt_linked"] = gattLinked; o["btn_live"] = btnLive;
        o["cfg"] = isMonitoredConfiguring(m, now);
        o["await_rel"] = m.waitReleaseAfterPair;
    }

    pruneStaleBleEntries(now);
    auto appendBleDeviceObj = [&](JsonArray& arr, const BleEntry& it, bool isMon) {
        JsonObject o = arr.createNestedObject();
        o["name"] = it.name; o["adv_name"] = it.advName; o["address"] = it.address; o["addr_type"] = it.addrType; o["rssi"] = it.rssi;
        o["isKnownDevice"] = it.isKnownDevice; o["type"] = it.type; o["soc"] = it.soc; o["state"] = it.state;
        o["can_adv"] = it.canAdv; o["can_gatt"] = it.canGatt;
        o["age"] = elapsedMs(now, it.lastSeen);
        if (it.matNum > 0) {
            o["mat_num"] = it.matNum;
            String mdl = lookupFestoolModelByTnr(it.matNum);
            if (mdl.length() > 0) o["model_name"] = mdl;
        }
        if (it.watts >= 0) o["watts"] = it.watts;
        if (isMon || it.canAdv || it.rawData.startsWith("GATT")) o["raw"] = it.rawData;
    };

    JsonArray devArr = doc.createNestedArray("devices");
    std::vector<size_t> unpinnedIndices;
    unpinnedIndices.reserve(bleList.size());
    for (size_t idx = 0; idx < bleList.size(); idx++) {
        const auto& it = bleList[idx];
        bool isPinned = (pairedMac.length() > 0 && it.address.equalsIgnoreCase(pairedMac));
        bool isMon = (findMonitoredByMac(it.address) != nullptr);
        if (isPinned || isMon) {
            appendBleDeviceObj(devArr, it, isMon);
        } else {
            unpinnedIndices.push_back(idx);
        }
    }
    static const size_t MAX_DISCOVERED_JSON = 16;
    if (unpinnedIndices.size() > MAX_DISCOVERED_JSON) {
        std::sort(unpinnedIndices.begin(), unpinnedIndices.end(), [&](size_t a, size_t b) {
            return bleList[a].lastSeen > bleList[b].lastSeen;
        });
        unpinnedIndices.resize(MAX_DISCOVERED_JSON);
        // Restore stable discovery order so rows never jump as packets arrive
        std::sort(unpinnedIndices.begin(), unpinnedIndices.end());
    }
    for (size_t idx : unpinnedIndices) {
        appendBleDeviceObj(devArr, bleList[idx], false);
    }
    if (doc.overflowed()) {
        LOGLN("[API] Warning: /api/status JSON buffer overflowed 8192B capacity.");
    }
    out.clear();
    out.reserve(8192);
    serializeJson(doc, out);
}

void sendJsonStatus() {
    static String out;
    buildStatusJson(out);
    server.send(200, "application/json", out);
}

const char INDEX_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>BLE Dust Bridge</title>
<style>
  :root {
    --bg: #283b31;
    --cream: #f7f3e3;
    --subcard: #fbf9f1;
    --input: #ffffff;
    --btn-idle: #eef0eb;
    --accent: #283b31;
    --accent-soft: #e3ece6;
    --danger: #b83232;
    --danger-soft: #f8e6e6;
    --warn: #c27803;
    --warn-soft: #fbf0dc;
    --border: #dfd9c5;
    --text: #1f2e26;
    --sub: #5c6b63;
  }
  * { box-sizing: border-box; }
  body { margin: 0; padding: 0 0 28px 0; background: var(--bg); color: var(--text); font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; }
  .topbar { background: var(--cream); border-bottom: 1px solid var(--border); padding: 12px 20px; display: flex; justify-content: space-between; align-items: center; }
  .topbar-inner { max-width: 660px; width: 100%; margin: 0 auto; display: flex; justify-content: space-between; align-items: center; }
  .title { font-size: 1.3rem; font-weight: 600; color: var(--accent); letter-spacing: 0.01em; }
  .gear-btn { background: var(--subcard); border: 1px solid var(--border); color: var(--accent); width: 36px; height: 36px; border-radius: 8px; display: flex; align-items: center; justify-content: center; cursor: pointer; padding: 0; }
  .gear-btn svg { width: 19px; height: 19px; }
  .container { max-width: 660px; margin: 20px auto 0 auto; padding: 0 16px; }
  .badge { padding: 4px 11px; border-radius: 20px; font-size: 0.74rem; font-weight: 700; text-transform: uppercase; letter-spacing: 0.03em; }
  .badge.small { font-size: 0.65rem; padding: 3px 8px; background: #efece0; color: var(--sub); border: 1px solid var(--border); text-transform: none; display: inline-flex; align-items: center; line-height: 1; }
  .badge.pill-role-gatt { font-size: 0.65rem; padding: 3px 8px; background: var(--accent-soft); color: var(--accent); border: 1px solid #9eb8a8; text-transform: none; display: inline-flex; align-items: center; line-height: 1; }
  .badge.pill-role-hybrid { font-size: 0.65rem; padding: 3px 8px; background: #e8efe8; color: var(--accent); border: 1px solid #b5c7ba; text-transform: none; display: inline-flex; align-items: center; line-height: 1; }
  .role-pill { height: 22px; padding: 0 7px; cursor: pointer; user-select: none; -webkit-tap-highlight-color: transparent; }
  .ui-tip { position: fixed; z-index: 300; background: #1f2e26; color: #f7f3e3; font-size: 0.72rem; font-weight: 700; letter-spacing: 0.02em; padding: 4px 9px; border-radius: 6px; box-shadow: 0 4px 12px rgba(0,0,0,0.24); pointer-events: none; opacity: 0; transform: translateY(3px); transition: opacity 0.12s ease, transform 0.12s ease; white-space: nowrap; }
  .ui-tip.show { opacity: 1; transform: translateY(0); }
  .badge.pill-warn { font-size: 0.65rem; padding: 0 8px; background: var(--danger-soft); color: var(--danger); border: 1px solid #dfb0b0; text-transform: none; }
  .badge.pill-conn { font-size: 0.65rem; padding: 0 8px; gap: 5px; background: var(--accent-soft); color: var(--accent); border: 1px solid #9eb8a8; text-transform: none; }
  .badge.pill-disc { font-size: 0.65rem; padding: 0 8px; gap: 5px; background: var(--danger-soft); color: var(--danger); border: 1px solid #dfb0b0; text-transform: none; }
  .badge.pill-pair { font-size: 0.65rem; padding: 0 8px; gap: 5px; background: var(--warn-soft); color: #9a5b00; border: 1px solid #e5c687; text-transform: none; }
  .rssi-pill { gap: 4px; font-family: monospace; }
  .slot-warn-banner { display: none; background: var(--warn-soft); color: #9a5b00; border: 1px solid #e5c687; border-radius: 8px; padding: 7px 11px; font-size: 0.78rem; font-weight: 600; margin-bottom: 10px; }
  @keyframes spin { to { transform: rotate(360deg); } }
  .spinner { display: inline-block; width: 13px; height: 13px; border: 2px solid var(--border); border-top-color: var(--accent); border-radius: 50%; animation: spin 0.75s linear infinite; vertical-align: -2px; margin-right: 6px; }
  .b-disc { background: var(--danger-soft); color: var(--danger); border: 1px solid #dfb0b0; }
  .card { background: var(--cream); border: 1px solid var(--border); border-radius: 14px; padding: 18px 20px; margin-bottom: 16px; }
  .card-head { display: flex; justify-content: space-between; align-items: center; margin-bottom: 14px; font-size: 0.92rem; font-weight: 600; color: var(--accent); gap: 8px; flex-wrap: wrap; }
  .controls-disabled { opacity: 0.45; pointer-events: none; }
  .ctrl-btn { flex: 1; padding: 13px 8px; background: var(--btn-idle); border: 1px solid #d5d0be; color: var(--text); border-radius: 8px; cursor: pointer; font-weight: 600; font-size: 1rem; white-space: nowrap; }
  .btn-pair { background: var(--accent); color: var(--cream); padding: 7px 14px; font-size: 0.82rem; border-radius: 7px; border: 1px solid var(--accent); cursor: pointer; font-weight: 600; transition: opacity 0.15s; }
  .btn-pair:disabled { opacity: 0.4; cursor: not-allowed; pointer-events: none; }
  .tog-wrap { display: inline-flex; align-items: center; gap: 5px; background: var(--input); border: 1px solid var(--border); border-radius: 7px; padding: 4px 8px; font-size: 0.76rem; font-weight: 600; color: var(--sub); cursor: pointer; user-select: none; }
  .tog-wrap.on { border-color: #9eb8a8; color: var(--accent); background: #f2f7f4; }
  .tog-track { position: relative; width: 26px; height: 15px; background: #cfc8b4; border-radius: 999px; transition: background 0.16s; flex-shrink: 0; }
  .tog-wrap.on .tog-track { background: var(--accent); }
  .tog-thumb { position: absolute; top: 2px; left: 2px; width: 11px; height: 11px; background: #ffffff; border-radius: 50%; transition: transform 0.16s; box-shadow: 0 1px 2px rgba(0,0,0,0.2); }
  .tog-wrap.on .tog-thumb { transform: translateX(11px); }
  .found-row { display: flex; flex-direction: column; align-items: stretch; gap: 10px; background: var(--subcard); border: 1px solid var(--border); border-radius: 10px; padding: 12px 14px; margin-bottom: 8px; }
  .vac-row { display: flex; flex-direction: column; align-items: stretch; background: var(--subcard); padding: 12px 14px; border-radius: 10px; border: 1px solid var(--border); margin-bottom: 8px; gap: 10px; }
  .vac-row.is-paired { border-color: #9eb8a8; }
  .vac-top { display: flex; justify-content: space-between; align-items: center; width: 100%; gap: 8px; }
  .top-right-icons { display: inline-flex; align-items: center; gap: 5px; flex-shrink: 0; }
  .top-right-icons .badge { height: 22px; display: inline-flex; align-items: center; justify-content: center; line-height: 1; padding-top: 0; padding-bottom: 0; }
  .vac-bottom { display: flex; justify-content: space-between; align-items: center; width: 100%; gap: 8px; flex-wrap: wrap; }
  .vac-pills { display: flex; align-items: center; gap: 6px; flex-wrap: wrap; }
  .vac-pills .badge { height: 22px; display: inline-flex; align-items: center; justify-content: center; line-height: 1; padding-top: 0; padding-bottom: 0; }
  .vac-actions { display: flex; align-items: center; gap: 6px; flex-shrink: 0; margin-left: auto; }
  .evac-wrap { display: flex; align-items: center; gap: 5px; background: var(--input); border: 1px solid var(--border); border-radius: 7px; padding: 4px 8px; font-size: 0.78rem; color: var(--sub); }
  .evac-input { width: 40px; background: transparent; border: none; color: var(--accent); font-weight: 700; font-size: 0.85rem; text-align: right; outline: none; }
  .monitored-row { display: flex; flex-direction: column; align-items: stretch; background: var(--subcard); padding: 12px 14px; border-radius: 10px; border: 1px solid var(--border); margin-bottom: 8px; gap: 10px; }
  .spd-select { background: var(--input); color: var(--accent); border: 1px solid var(--border); border-radius: 7px; padding: 5px 7px; font-weight: 600; font-size: 0.82rem; }
  .icon-btn { background: transparent; border: none; cursor: pointer; padding: 4px 6px; border-radius: 6px; display: inline-flex; align-items: center; justify-content: center; }
  .modal-overlay { position: fixed; inset: 0; background: rgba(24, 36, 30, 0.65); display: none; align-items: center; justify-content: center; z-index: 100; padding: 16px; overflow-y: auto; }
  .modal-box { background: var(--cream); border: 1px solid var(--border); border-radius: 14px; width: 100%; max-width: 500px; padding: 22px; margin: auto; color: var(--text); }
  .close-btn { background: transparent; border: none; color: var(--sub); font-size: 1.4rem; cursor: pointer; width: auto; padding: 0; }
  .name-edit { display: flex; align-items: center; gap: 6px; flex-wrap: wrap; }
  .inline-name-input { background: transparent; border: 1px solid transparent; border-radius: 6px; color: var(--text); font-family: inherit; font-weight: 700; padding: 3px 6px; margin-left: -6px; outline: none; min-width: 72px; max-width: 100%; transition: background 0.15s, border-color 0.15s; }
  .inline-name-input:hover { background: rgba(255, 255, 255, 0.65); border-color: var(--border); }
  .inline-name-input:focus { background: var(--input); border-color: var(--accent); box-shadow: 0 0 0 2px var(--accent-soft); }
  #saved-wifi-list { position: relative; }
  .wifi-saved-row { display: flex; justify-content: space-between; align-items: center; gap: 10px; background: var(--subcard); padding: 8px 12px; border: 1px solid var(--border); border-radius: 8px; margin-bottom: 8px; user-select: none; will-change: transform; }
  .wifi-saved-row.is-placeholder { background: var(--accent-soft); border: 1.5px dashed #9eb8a8; opacity: 0.65; }
  .wifi-saved-row.is-placeholder > * { visibility: hidden; }
  .wifi-floating-item { position: fixed; z-index: 250; pointer-events: none; margin: 0; background: var(--input); border: 1.5px solid var(--accent); border-radius: 8px; padding: 8px 12px; display: flex; justify-content: space-between; align-items: center; gap: 10px; box-shadow: 0 12px 28px rgba(31, 46, 38, 0.24), 0 2px 6px rgba(31, 46, 38, 0.12); transform: scale(1.02); transition: box-shadow 0.16s ease, transform 0.16s ease; user-select: none; }
  .drag-handle { display: inline-flex; align-items: center; justify-content: center; color: var(--sub); cursor: grab; padding: 6px 4px; margin-left: -4px; touch-action: none; flex-shrink: 0; border-radius: 5px; transition: color 0.15s, background 0.15s; }
  .drag-handle:hover { color: var(--accent); background: rgba(40, 59, 49, 0.06); }
  .drag-handle:active { cursor: grabbing; color: var(--accent); }
  .info-text { font-size: 0.78rem; color: var(--sub); margin-top: 3px; font-family: monospace; }
  .telem-grid { background: var(--subcard); border: 1px solid var(--border); border-radius: 10px; overflow: hidden; margin-top: 12px; }
  .telem-row { display: flex; justify-content: space-between; align-items: center; padding: 9px 14px; border-bottom: 1px solid #ebe6d5; font-size: 0.86rem; }
  .telem-row:last-child { border-bottom: none; }
  .telem-lbl { color: var(--sub); font-weight: 500; }
  .telem-val { color: var(--text); font-weight: 600; font-family: monospace; text-align: right; }
  .form-group { margin-bottom: 12px; }
  .form-group label { display: block; font-size: 0.78rem; color: var(--sub); margin-bottom: 5px; font-weight: 600; }
  .form-input { width: 100%; padding: 9px 11px; background: var(--input); border: 1px solid var(--border); color: var(--text); border-radius: 7px; font-size: 0.92rem; outline: none; }
  .form-input:focus { border-color: var(--accent); }
  .wifi-list { background: var(--input); border: 1px solid var(--border); border-radius: 7px; max-height: 140px; overflow-y: auto; margin-top: 8px; display: none; }
  .wifi-item { padding: 8px 12px; display: flex; justify-content: space-between; font-size: 0.85rem; cursor: pointer; border-bottom: 1px solid #ebe6d5; }
</style>
</head>
<body>
<div class="topbar">
  <div class="topbar-inner">
    <div class="title">BLE Dust Bridge</div>
    <div style="display:flex; align-items:center; gap:8px;">
      <button class="gear-btn" onclick="openSettings()" title="Settings">
        <svg viewBox="0 0 24 24"><path fill="currentColor" d="M19.14 12.94c.04-.3.06-.61.06-.94 0-.32-.02-.64-.07-.94l2.03-1.58c.18-.14.23-.41.12-.61l-1.92-3.32c-.12-.22-.37-.29-.59-.22l-2.39.96c-.5-.38-1.03-.7-1.62-.94l-.36-2.54c-.04-.24-.24-.41-.48-.41h-3.84c-.24 0-.43.17-.47.41l-.36 2.54c-.59.24-1.13.57-1.62.94l-2.39-.96c-.22-.08-.47 0-.59.22L2.74 8.87c-.12.21-.08.47.12.61l2.03 1.58c-.05.3-.09.63-.09.94s.02.64.07.94l-2.03 1.58c-.18.14-.23.41-.12.61l1.92 3.32c.12.22.37.29.59.22l2.39-.96c.5.38 1.03.7 1.62.94l.36 2.54c.05.24.24.41.48.41h3.84c.24 0 .44-.17.47-.41l.36-2.54c.59-.24 1.13-.56 1.62-.94l2.39.96c.22.08.47 0 .59-.22l1.92-3.32c.12-.22.07-.47-.12-.61l-2.01-1.58zM12 15.6c-1.98 0-3.6-1.62-3.6-3.6s1.62-3.6 3.6-3.6 3.6 1.62 3.6 3.6-1.62 3.6-3.6 3.6z"/></svg>
      </button>
      <button id="logout-btn" class="gear-btn" style="display:none;" onclick="logoutSession()" title="Log Out">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><polyline points="16 17 21 12 16 7"/><line x1="21" y1="12" x2="9" y2="12"/></svg>
      </button>
    </div>
  </div>
</div>

<div class="container">
  <div class="card">
    <div class="card-head">
      <span>Dust Extractor</span>
      <span id="unpaired-badge" class="badge b-disc" style="display:none;">Unpaired</span>
    </div>
    <div id="controls-wrap" class="controls-disabled" style="margin-bottom:14px;">
      <div style="display:flex; gap:6px;">
        <button id="btn-20" class="ctrl-btn" onclick="setSpeed(20)">20%</button>
        <button id="btn-40" class="ctrl-btn" onclick="setSpeed(40)">40%</button>
        <button id="btn-60" class="ctrl-btn" onclick="setSpeed(60)">60%</button>
        <button id="btn-80" class="ctrl-btn" onclick="setSpeed(80)">80%</button>
        <button id="btn-100" class="ctrl-btn" onclick="setSpeed(100)">100%</button>
      </div>
      <button id="btn-off" class="ctrl-btn" style="width:100%; margin-top:8px;" onclick="setPower(3)">OFF</button>
    </div>
    <div id="vac-section"></div>
  </div>

  <div class="card">
    <div class="card-head"><span>Monitored Devices</span></div>
    <div id="gatt-slot-warn" class="slot-warn-banner"></div>
    <div id="monitored-list"></div>
  </div>

  <div class="card">
    <div class="card-head"><span>Discovered Devices</span></div>
    <div id="discovered-list"></div>
  </div>
</div>

<div id="ext-info-modal" class="modal-overlay" onclick="if(event.target.id==='ext-info-modal') this.style.display='none';">
  <div class="modal-box">
    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:10px;">
      <div>
        <h3 id="info-modal-title" style="margin:0; color:var(--accent);">Extractor Info</h3>
        <div id="info-modal-mac" class="info-text">GATT MAC: --</div>
      </div>
      <button class="close-btn" onclick="document.getElementById('ext-info-modal').style.display='none'">&times;</button>
    </div>
    <div id="info-modal-body" class="telem-grid"></div>
    <div style="display:flex; gap:10px; margin-top:16px;">
      <button style="flex:1; background:var(--btn-idle); border:1px solid var(--border); color:var(--text); padding:10px; border-radius:8px; font-weight:600; cursor:pointer;" onclick="fetch('/api/telem/refresh').then(r=>r.json()).then(applyStatusResponse)">Refresh</button>
      <button style="flex:1; background:var(--btn-idle); border:1px solid var(--border); color:var(--text); padding:10px; border-radius:8px; font-weight:600; cursor:pointer;" onclick="fetch('/api/identify')">Identify</button>
      <button style="flex:1; background:var(--accent); color:var(--cream); padding:10px; border-radius:8px; border:none; font-weight:600; cursor:pointer;" onclick="document.getElementById('ext-info-modal').style.display='none'">Close</button>
    </div>
  </div>
</div>

<div id="mon-info-modal" class="modal-overlay" onclick="if(event.target.id==='mon-info-modal') { activeMonModalMac=''; activeDiscModalMac=''; this.style.display='none'; }">
  <div class="modal-box">
    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:10px;">
      <div>
        <h3 id="mon-modal-title" style="margin:0; color:var(--accent);">Device Info</h3>
        <div id="mon-modal-mac" class="info-text">MAC: --</div>
      </div>
      <button class="close-btn" onclick="activeMonModalMac=''; activeDiscModalMac=''; document.getElementById('mon-info-modal').style.display='none'">&times;</button>
    </div>
    <div id="mon-modal-body" class="telem-grid"></div>
    <div style="display:flex; gap:10px; margin-top:16px;">
      <button style="flex:1; background:var(--accent); color:var(--cream); padding:10px; border-radius:8px; border:none; font-weight:600; cursor:pointer;" onclick="activeMonModalMac=''; activeDiscModalMac=''; document.getElementById('mon-info-modal').style.display='none'">Close</button>
    </div>
  </div>
</div>

<div id="settings-modal" class="modal-overlay" onclick="if(event.target.id==='settings-modal' && !activeWifiDrag && (Date.now()-lastWifiDragEndMs)>250) { cleanupActiveWifiDrag(); this.style.display='none'; }">
  <div class="modal-box">
    <h3 style="margin-top:0; color:var(--accent);">Settings</h3>
    <div id="settings-msg" style="display:none; padding:8px 11px; border-radius:8px; font-size:0.83rem; font-weight:600; margin-bottom:10px;"></div>
    <div class="card-head" style="margin-bottom:8px;"><span>Wi-Fi Networks (Max 5 · Drag to Order)</span></div>
    <div id="saved-wifi-list"></div>
    <div style="background:var(--subcard); padding:12px; border-radius:10px; border:1px solid var(--border); margin-bottom:18px;">
        <div class="form-group"><label>Add / Edit SSID</label><input type="text" id="new-ssid" class="form-input"></div>
        <div class="form-group"><label>Password</label><input type="password" id="new-pass" class="form-input"></div>
        <div style="display:flex; gap:10px;">
            <button style="flex:1; background:var(--accent); color:var(--cream); border:none; padding:10px; border-radius:8px; cursor:pointer; font-weight:600;" onclick="addWifi()">+ Add Network</button>
            <button style="flex:1; background:var(--btn-idle); border:1px solid var(--border); color:var(--text); padding:10px; border-radius:8px; cursor:pointer; font-weight:600;" onclick="scanWifiNetworks()">Scan Nearby</button>
        </div>
        <div id="wifi-scan-list" class="wifi-list"></div>
    </div>

    <div class="card-head" style="margin-bottom:8px;"><span>MQTT Telemetry (BLE_DB/#)</span></div>
    <label style="display:flex; align-items:center; gap:10px; margin-bottom:12px; cursor:pointer; font-size:0.9rem;">
        <input type="checkbox" id="mqtt-en" onchange="toggleMqtt()" style="width:17px; height:17px; accent-color:var(--accent);">
        <strong>Enable MQTT Telemetry</strong>
    </label>
    <div id="mqtt-fields" style="display:none; background:var(--subcard); padding:12px; border-radius:10px; border:1px solid var(--border); margin-bottom:18px;">
        <div class="form-group"><label>Broker IP / Hostname</label><input type="text" id="mqtt-ip" class="form-input"></div>
        <div class="form-group"><label>Port</label><input type="number" id="mqtt-port" class="form-input"></div>
        <div class="form-group"><label>Username</label><input type="text" id="mqtt-user" class="form-input"></div>
        <div class="form-group"><label>Password</label><input type="password" id="mqtt-pass" class="form-input"></div>
    </div>

    <div class="card-head" style="margin-bottom:8px;"><span>Web UI Login</span></div>
    <label style="display:flex; align-items:center; gap:10px; margin-bottom:12px; cursor:pointer; font-size:0.9rem;">
        <input type="checkbox" id="auth-en" onchange="toggleAuthFields()" style="width:17px; height:17px; accent-color:var(--accent);">
        <strong>Require Login (Challenge-Response)</strong>
    </label>
    <div id="auth-fields" style="display:none; background:var(--subcard); padding:12px; border-radius:10px; border:1px solid var(--border); margin-bottom:18px;">
        <div class="form-group"><label>Username</label><input type="text" id="auth-user" class="form-input" autocomplete="username"></div>
        <div class="form-group" style="margin-bottom:0;"><label>New Password</label><input type="password" id="auth-pass" class="form-input" placeholder="Leave blank to keep current password" autocomplete="new-password"></div>
    </div>

    <button style="background:var(--subcard); border:1px solid var(--border); color:var(--accent); width:100%; padding:10px; border-radius:8px; cursor:pointer; font-weight:600;" onclick="window.location.href='/update'">Firmware Update (OTA)</button>
    <div style="display:flex; gap:10px; margin-top:16px;">
        <button style="flex:1; background:var(--accent); color:var(--cream); padding:11px; border-radius:8px; border:none; font-weight:600; cursor:pointer;" onclick="saveSettings()">Save Configuration</button>
        <button style="flex:1; background:var(--btn-idle); border:1px solid var(--border); color:var(--text); padding:11px; border-radius:8px; border:none; font-weight:600; cursor:pointer;" onclick="cleanupActiveWifiDrag(); document.getElementById('settings-modal').style.display='none'">Close</button>
    </div>
  </div>
</div>

<div id="confirm-modal" class="modal-overlay" style="z-index:200;" onclick="if(event.target.id==='confirm-modal') closeConfirmModal();">
  <div class="modal-box" style="max-width:390px;">
    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:10px;">
      <h3 id="confirm-modal-title" style="margin:0; color:var(--accent);">Confirm Action</h3>
      <button type="button" class="close-btn" onclick="closeConfirmModal()">&times;</button>
    </div>
    <p id="confirm-modal-msg" style="margin:0 0 18px 0; font-size:0.9rem; color:var(--text); line-height:1.45;"></p>
    <div style="display:flex; gap:10px;">
      <button type="button" style="flex:1; background:var(--btn-idle); border:1px solid var(--border); color:var(--text); padding:10px; border-radius:8px; font-weight:600; cursor:pointer;" onclick="closeConfirmModal()">Cancel</button>
      <button type="button" id="confirm-modal-ok" style="flex:1; background:var(--danger); border:none; color:#ffffff; padding:10px; border-radius:8px; font-weight:600; cursor:pointer;">Remove</button>
    </div>
  </div>
</div>

<div id="ui-tip" class="ui-tip" role="tooltip"></div>

<script>
let savedWifis = [];
let uiPower = 3;
let uiSpeed = 60;
let ignorePollUntil = 0;
let evacEndMs = 0;
let lastRenderedVacKey = '';
let lastRenderedMonKey = '';
let lastRenderedDiscKey = '';
let lastRenderedExtModalKey = '';
let latestStatusData = null;
let activeMonModalMac = '';
let activeDiscModalMac = '';
let monModalStaticLastSeen = '';
let lastRenderedMonModalKey = '';
let pollEpoch = 0;
let pollAbortCtrl = null;
let pairingMac = '';
let pairingStartedMs = 0;
let pairingSawConnecting = false;
const recentlyDeletedMacs = new Map();

const EDIT_SVG = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M17 3a2.828 2.828 0 1 1 4 4L7.5 20.5 2 22l1.5-5.5L17 3z"/></svg>';
const INFO_SVG = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><line x1="12" y1="16" x2="12" y2="12"/><line x1="12" y1="8" x2="12.01" y2="8"/></svg>';
const TRASH_SVG = '<svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polyline points="3 6 5 6 21 6"/><path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"/><line x1="10" y1="11" x2="10" y2="17"/><line x1="14" y1="11" x2="14" y2="17"/></svg>';
const LINK_SVG = '<svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71"/><path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"/></svg>';
const EYE_SVG = '<svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"/><circle cx="12" cy="12" r="3"/></svg>';
const GRIP_SVG = '<svg width="14" height="16" viewBox="0 0 14 16" fill="currentColor" aria-hidden="true"><circle cx="4.5" cy="3" r="1.3"/><circle cx="9.5" cy="3" r="1.3"/><circle cx="4.5" cy="8" r="1.3"/><circle cx="9.5" cy="8" r="1.3"/><circle cx="4.5" cy="13" r="1.3"/><circle cx="9.5" cy="13" r="1.3"/></svg>';

let pendingConfirmAction = null;

function openConfirmModal(title, message, confirmLabel, onConfirm) {
  const modal = document.getElementById('confirm-modal');
  const titleEl = document.getElementById('confirm-modal-title');
  const msgEl = document.getElementById('confirm-modal-msg');
  const okBtn = document.getElementById('confirm-modal-ok');
  if (!modal || !titleEl || !msgEl || !okBtn) return;
  titleEl.textContent = title;
  msgEl.textContent = message;
  okBtn.textContent = confirmLabel || 'Confirm';
  pendingConfirmAction = onConfirm;
  okBtn.onclick = () => {
    const fn = pendingConfirmAction;
    closeConfirmModal();
    if (typeof fn === 'function') fn();
  };
  modal.style.display = 'flex';
}

function closeConfirmModal() {
  pendingConfirmAction = null;
  const modal = document.getElementById('confirm-modal');
  if (modal) modal.style.display = 'none';
}

function confirmUnpairExtractor() {
  const extName = (latestStatusData && latestStatusData.ext_name) ? latestStatusData.ext_name : 'Dust Extractor';
  openConfirmModal(
    'Unpair Dust Extractor',
    `Unpair "${extName}"? You will need to put the extractor back into pairing mode to reconnect.`,
    'Unpair',
    () => unpairExtractor(null)
  );
}

function confirmDeleteMonitored(mac) {
  if (!mac) return;
  let devName = mac;
  if (latestStatusData && Array.isArray(latestStatusData.monitored)) {
    const found = latestStatusData.monitored.find(x => x.mac.toLowerCase() === mac.toLowerCase());
    if (found && found.name) devName = found.name;
  }
  openConfirmModal(
    'Remove Device',
    `Remove "${devName}" from Monitored Devices?`,
    'Remove',
    () => deleteMonitored(mac)
  );
}

document.addEventListener('keydown', (e) => {
  if (e.key === 'Escape') {
    const cm = document.getElementById('confirm-modal');
    if (cm && cm.style.display === 'flex') {
      closeConfirmModal();
    }
  }
});

let roleTipTimer = null;

function hideRoleTip() {
  if (roleTipTimer) {
    clearTimeout(roleTipTimer);
    roleTipTimer = null;
  }
  const tip = document.getElementById('ui-tip');
  if (tip) tip.classList.remove('show');
}

function showRoleTip(el, text, autoHideMs) {
  const tip = document.getElementById('ui-tip');
  if (!tip || !el) return;
  if (roleTipTimer) {
    clearTimeout(roleTipTimer);
    roleTipTimer = null;
  }
  tip.textContent = text || '';
  tip.classList.add('show');
  const r = el.getBoundingClientRect();
  const tw = tip.offsetWidth || 70;
  const th = tip.offsetHeight || 24;
  let left = r.left + (r.width / 2) - (tw / 2);
  left = Math.max(8, Math.min(window.innerWidth - tw - 8, left));
  let top = r.top - th - 6;
  if (top < 8) top = r.bottom + 6;
  tip.style.left = `${Math.round(left)}px`;
  tip.style.top = `${Math.round(top)}px`;
  if (autoHideMs && autoHideMs > 0) {
    roleTipTimer = setTimeout(hideRoleTip, autoHideMs);
  }
}

window.addEventListener('scroll', hideRoleTip, { passive: true });

function rolePillHtml(isPaired, isCfg = false) {
  const label = isPaired ? (isCfg ? 'Pairing...' : 'Paired') : 'Monitored';
  const cls = isPaired ? 'badge pill-role-gatt role-pill' : 'badge small role-pill';
  const svg = isPaired ? LINK_SVG : EYE_SVG;
  return `<span class="${cls}" role="button" tabindex="0" title="${label}" aria-label="${label}" onmouseenter="showRoleTip(this,'${label}',0)" onmouseleave="hideRoleTip()" onfocus="showRoleTip(this,'${label}',0)" onblur="hideRoleTip()" onclick="event.stopPropagation(); showRoleTip(this,'${label}',1800)">${svg}</span>`;
}

let activeWifiDrag = null;
let lastWifiDragEndMs = 0;

function cleanupActiveWifiDrag() {
  if (!activeWifiDrag) return;
  const drag = activeWifiDrag;
  activeWifiDrag = null;
  if (drag.onMove) window.removeEventListener('pointermove', drag.onMove);
  if (drag.onUp) {
    window.removeEventListener('pointerup', drag.onUp);
    window.removeEventListener('pointercancel', drag.onUp);
  }
  if (drag.onBlur) window.removeEventListener('blur', drag.onBlur);
  if (drag.handle && drag.pointerId !== undefined) {
    try { drag.handle.releasePointerCapture(drag.pointerId); } catch (_) {}
  }
  if (drag.floatingEl) drag.floatingEl.remove();
  if (drag.placeholderRow) drag.placeholderRow.classList.remove('is-placeholder');
  document.body.style.cursor = '';
}

function persistWifiOrder() {
  const orderPayload = { wifis: savedWifis.map(w => ({ ssid: w.ssid })) };
  fetch('/api/wifi/reorder', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(orderPayload)
  }).then(r => {
    if (r.ok) showSettingsMsg('Wi-Fi connection priority updated.');
  }).catch(() => {});
}

function escHtml(s) {
  return String(s || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

function abortInFlightPoll() {
  pollEpoch++;
  if (pollAbortCtrl) {
    try { pollAbortCtrl.abort(); } catch (e) {}
    pollAbortCtrl = null;
  }
}

function applyStatusResponse(data) {
  if (!data || typeof data !== 'object') return;
  abortInFlightPoll();
  latestStatusData = data;
  renderAllFromStatus(data, true);
}

function rssiBarsSvg(rssi, activeTone = false) {
  const val = (typeof rssi === 'number' && rssi < 0) ? rssi : null;
  const lvl = val === null ? 0 : (val >= -60 ? 4 : (val >= -72 ? 3 : (val >= -84 ? 2 : 1)));
  const activeColor = '#283b31';
  const dimColor = activeTone ? '#9eb8a8' : '#cfc8b4';
  const c = (n) => (lvl >= n ? activeColor : dimColor);
  return `<svg width="14" height="12" viewBox="0 0 14 12" aria-hidden="true">` +
    `<rect x="0" y="9" width="2.5" height="3" rx="0.6" fill="${c(1)}"/>` +
    `<rect x="3.8" y="6.5" width="2.5" height="5.5" rx="0.6" fill="${c(2)}"/>` +
    `<rect x="7.6" y="3.5" width="2.5" height="8.5" rx="0.6" fill="${c(3)}"/>` +
    `<rect x="11.4" y="0.5" width="2.5" height="11.5" rx="0.6" fill="${c(4)}"/>` +
    `</svg>`;
}

function rssiBarLevel(rssi) {
  if (typeof rssi !== 'number' || rssi >= 0) return 0;
  return rssi >= -60 ? 4 : (rssi >= -72 ? 3 : (rssi >= -84 ? 2 : 1));
}

function rssiPillHtml(rssi, ageMs = 0) {
  const hasVal = (typeof rssi === 'number' && rssi < 0 && ageMs <= 300000);
  const bars = hasVal ? rssiBarLevel(rssi) : 0;
  const title = hasVal ? `Signal: ${bars}/4 bars` : 'No signal';
  return `<span class="badge small rssi-pill" title="${title}">${rssiBarsSvg(hasVal ? rssi : null)}</span>`;
}

function discSwitchModeInfo(k) {
  const canAdv = !!k.can_adv;
  const canGatt = !!k.can_gatt;
  if (canAdv && canGatt) {
    return {
      label: 'Passive/GATT',
      cls: 'badge pill-role-hybrid',
      tip: 'Dual-mode switch: defaults to Passive (0 GATT slots), or supports GATT Primary Mode'
    };
  }
  if (canAdv) {
    return {
      label: 'Passive',
      cls: 'badge small',
      tip: 'Passive broadcast switch (0 GATT slots)'
    };
  }
  return {
    label: 'GATT',
    cls: 'badge pill-role-gatt',
    tip: 'GATT-required switch (pairs automatically on add)'
  };
}

function addFoundDevice(mac, name, btnType, raw, rssi, addrType, devTypeStr, canAdv, canGatt) {
  const macLow = mac.toLowerCase();
  recentlyDeletedMacs.delete(macLow);
  if (activeDiscModalMac && activeDiscModalMac.toLowerCase() === macLow) {
    activeDiscModalMac = '';
    document.getElementById('mon-info-modal').style.display = 'none';
  }
  abortInFlightPoll();
  lastRenderedMonKey = '';
  lastRenderedDiscKey = '';
  const url = `/api/monitored/add?mac=${encodeURIComponent(mac)}&name=${encodeURIComponent(name)}&speed=20&btnType=${btnType}&raw=${encodeURIComponent(raw || '')}&rssi=${encodeURIComponent(rssi || 0)}&addrType=${encodeURIComponent(addrType || 0)}&canAdv=${canAdv ? 1 : 0}&canGatt=${canGatt ? 1 : 0}`;
  fetch(url).then(r => r.json()).then(applyStatusResponse);
}

function deleteMonitored(mac) {
  if (document.activeElement && document.activeElement.blur) document.activeElement.blur();
  const macLow = mac.toLowerCase();
  recentlyDeletedMacs.set(macLow, Date.now() + 3000);
  if (activeMonModalMac && activeMonModalMac.toLowerCase() === macLow) {
    activeMonModalMac = '';
    document.getElementById('mon-info-modal').style.display = 'none';
  }
  if (latestStatusData && Array.isArray(latestStatusData.monitored)) {
    latestStatusData.monitored = latestStatusData.monitored.filter(m => m.mac.toLowerCase() !== macLow);
  }
  lastRenderedMonKey = '';
  lastRenderedDiscKey = '';
  abortInFlightPoll();
  if (latestStatusData) renderAllFromStatus(latestStatusData, true);
  fetch(`/api/monitored/delete?mac=${encodeURIComponent(mac)}`).then(r => r.json()).then(applyStatusResponse);
}

function fmtRunLong(sec) {
  return ((sec || 0) / 3600).toFixed(2) + ' hrs';
}

function fmtFilterRemShort(filterRunSec) {
  const remSec = Math.max(0, 180000 - (filterRunSec || 0));
  return 'Filter: ' + Math.floor(remSec / 3600) + 'hrs';
}

function fmtFilterRemLong(filterRunSec) {
  const remSec = Math.max(0, 180000 - (filterRunSec || 0));
  return (remSec / 3600).toFixed(2) + ' hrs';
}

function openExtInfoModal() {
  if (!latestStatusData) return;
  lastRenderedExtModalKey = '';
  renderExtInfoModal(latestStatusData);
  document.getElementById('ext-info-modal').style.display = 'flex';
}

function renderExtInfoModal(data) {
  const t = data.telem || {};
  document.getElementById('info-modal-title').innerText = data.ext_name || 'Festool Extractor';
  document.getElementById('info-modal-mac').innerText = 'GATT MAC: ' + (data.paired_mac || '--');

  const faultStr = t.faults || 'Healthy';
  const faultColor = faultStr === 'Healthy' ? 'var(--accent)' : 'var(--danger)';
  const waterStr = t.water_active ? 'Active' : 'Inactive';

  const highLimit = (t.temp2_f && t.temp2_f > 100) ? t.temp2_f : 185;
  const isHighTemp = (t.temp1_f > 0 && t.temp1_f >= highLimit);
  const tempStr = t.temp1_f > 0
    ? (isHighTemp ? `<span style="color:var(--danger);">High (${t.temp1_f}°F)</span>` : `OK (${t.temp1_f}°F)`)
    : 'OK';

  const extModalKey = `${data.ext_name}|${data.paired_mac}|${faultStr}|${waterStr}|${t.motor_sec}|${t.cycles}|${t.filter_sec}|${t.temp1_f}|${t.temp2_f}|${t.model}|${t.sw_ver}|${t.main_fw}|${t.ble_fw}`;
  if (extModalKey !== lastRenderedExtModalKey) {
    lastRenderedExtModalKey = extModalKey;
    const rows = [
      ['Status / Faults', `<span style="color:${faultColor};">${faultStr}</span>`],
      ['Water Level Protection', waterStr],
      ['Operating Time', fmtRunLong(t.motor_sec)],
      ['Operating Cycles', (t.cycles !== undefined ? t.cycles : '--')],
      ['Filter Hours Remaining', fmtFilterRemLong(t.filter_sec)],
      ['Temperature', tempStr],
      ['Model', t.model || 'CT MINI MIDI I'],
      ['Software Version', `${t.sw_ver || 'V 2/10'} (${t.main_fw || '--'} / ${t.ble_fw || '--'})`]
    ];
    document.getElementById('info-modal-body').innerHTML = rows.map(r =>
      `<div class="telem-row"><span class="telem-lbl">${r[0]}</span><span class="telem-val">${r[1]}</span></div>`
    ).join('');
  }
}

function openMonInfoModal(mac) {
  activeDiscModalMac = '';
  activeMonModalMac = mac;
  lastRenderedMonModalKey = '';
  const live = latestStatusData && (latestStatusData.devices || []).find(d => d.address.toLowerCase() === mac.toLowerCase());
  if (live && typeof live.age === 'number') {
    const seenAt = new Date(Date.now() - live.age);
    monModalStaticLastSeen = seenAt.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  } else {
    monModalStaticLastSeen = 'Not seen since boot';
  }
  if (latestStatusData) renderMonInfoModal(latestStatusData);
  document.getElementById('mon-info-modal').style.display = 'flex';
}

function openDiscInfoModal(mac) {
  activeMonModalMac = '';
  activeDiscModalMac = mac;
  lastRenderedMonModalKey = '';
  const live = latestStatusData && (latestStatusData.devices || []).find(d => d.address.toLowerCase() === mac.toLowerCase());
  if (live && typeof live.age === 'number') {
    const seenAt = new Date(Date.now() - live.age);
    monModalStaticLastSeen = seenAt.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  } else {
    monModalStaticLastSeen = 'Just discovered';
  }
  if (latestStatusData) renderDiscInfoModal(latestStatusData);
  document.getElementById('mon-info-modal').style.display = 'flex';
}

function renderDiscInfoModal(data) {
  if (!activeDiscModalMac) return;
  const k = (data.devices || []).find(d => d.address.toLowerCase() === activeDiscModalMac.toLowerCase());
  if (!k) return;

  document.getElementById('mon-modal-title').innerText = k.name || 'Discovered Device';
  document.getElementById('mon-modal-mac').innerText = 'MAC: ' + k.address;

  const lookupModel = (k.model_name || '').trim();
  const advName = (k.adv_name || '').trim();
  const modelLine = lookupModel || advName || 'Unknown';

  const baseType = k.type || 'Other';
  let typeLabel = baseType;
  if (baseType === 'Battery') typeLabel = 'Festool Battery';
  else if ((k.name || '').toUpperCase().includes('CT-F')) typeLabel = 'Festool Remote';
  else if (baseType === 'Button') typeLabel = 'Wireless Switch';

  const rawRssi = (typeof k.rssi === 'number' && k.rssi < 0 && (k.age === undefined || k.age <= 300000)) ? k.rssi : null;
  const barsCount = rssiBarLevel(rawRssi);
  const rssiQuality = rawRssi === null ? 'No Signal' : (barsCount === 4 ? 'Excellent (4/4 bars)' : (barsCount === 3 ? 'Good (3/4 bars)' : (barsCount === 2 ? 'Fair (2/4 bars)' : 'Weak (1/4 bars)')));
  const rssiHtml = `<span style="display:inline-flex;align-items:center;gap:6px;">${rssiBarsSvg(rawRssi)}<span>${rssiQuality}</span></span>`;

  let lastSeenStr = monModalStaticLastSeen || 'Just discovered';
  if (typeof k.age === 'number') {
    const seenAt = new Date(Date.now() - k.age);
    lastSeenStr = seenAt.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
    monModalStaticLastSeen = lastSeenStr;
  }

  const isFestoolBattery = (baseType === 'Battery');
  const socVal = (typeof k.soc === 'number' && k.soc >= 0) ? k.soc : -1;
  const isToolPlug = (baseType === 'Tool Plug');
  const wattsVal = (typeof k.watts === 'number' && k.watts >= 0) ? k.watts : -1;
  const swMode = (baseType === 'Button') ? discSwitchModeInfo(k).label : '';
  const statusText = (baseType === 'Button') ? `Detected Mode · ${swMode}` : 'Unconfigured (Discovered)';

  const modalKey = `disc|${k.name}|${k.address}|${modelLine}|${typeLabel}|${barsCount}|${lastSeenStr}|${socVal}|${wattsVal}|${statusText}`;
  if (modalKey !== lastRenderedMonModalKey) {
    lastRenderedMonModalKey = modalKey;
    const rows = [
      ['Model', modelLine],
      ['Device Type', typeLabel],
      ['Signal Strength', rssiHtml],
      ['Last Seen', lastSeenStr]
    ];
    if (isFestoolBattery) {
      rows.push(['Charge State', socVal >= 0 ? `${socVal}%` : '--']);
    }
    if (isToolPlug) {
      rows.push(['Live Power', rawRssi === null ? 'Off' : (wattsVal >= 0 ? `${wattsVal} W` : '--')]);
    }
    rows.push(['Status', statusText]);
    document.getElementById('mon-modal-body').innerHTML = rows.map(r =>
      `<div class="telem-row"><span class="telem-lbl">${r[0]}</span><span class="telem-val">${r[1]}</span></div>`
    ).join('');
  }
}

function renderMonInfoModal(data) {
  if (!activeMonModalMac) return;
  const modalBody = document.getElementById('mon-modal-body');
  if (modalBody && modalBody.contains(document.activeElement)) return;
  const m = (data.monitored || []).find(x => x.mac.toLowerCase() === activeMonModalMac.toLowerCase());
  if (!m) return;
  const live = (data.devices || []).find(d => d.address.toLowerCase() === m.mac.toLowerCase());
  const isCfg = !!m.cfg;
  const isAct = !isCfg
    ? (m.btnType > 0 ? !!m.btn_live : (live ? (live.state === 1 && live.age < 8000) : false))
    : false;

  document.getElementById('mon-modal-title').innerText = m.name;
  document.getElementById('mon-modal-mac').innerText = 'MAC: ' + m.mac;

  const lookupModel = (m.model_name || '').trim();
  const advName = (m.adv_name || (live && live.adv_name) || '').trim();
  const modelLine = lookupModel || advName || 'Unknown';

  const baseType = m.dev_type || (live ? live.type : '') || (m.btnType > 0 ? 'Button' : 'Auto Tool');
  let typeLabel = baseType;
  if (baseType === 'Battery') typeLabel = 'Festool Battery';
  else if (m.btnType > 0) {
    typeLabel = m.is_hose ? 'Primary Switch (GATT)' : (m.is_gatt ? 'Switch (GATT)' : 'Switch (ADV)');
  }

  const rawRssi = (live && typeof live.rssi === 'number' && live.rssi < 0 && (live.age === undefined || live.age <= 300000))
    ? live.rssi
    : ((typeof m.rssi === 'number' && m.rssi < 0 && (m.rssi_age === undefined || m.rssi_age <= 300000)) ? m.rssi : null);
  const barsCount = rssiBarLevel(rawRssi);
  const rssiQuality = rawRssi === null ? 'No Signal' : (barsCount === 4 ? 'Excellent (4/4 bars)' : (barsCount === 3 ? 'Good (3/4 bars)' : (barsCount === 2 ? 'Fair (2/4 bars)' : 'Weak (1/4 bars)')));
  const rssiHtml = `<span style="display:inline-flex;align-items:center;gap:6px;">${rssiBarsSvg(rawRssi)}<span>${rssiQuality}</span></span>`;

  let lastSeenStr = monModalStaticLastSeen || 'Not seen since boot';
  if (m.gatt_linked) {
    lastSeenStr = 'Connected now';
  } else if (live && typeof live.age === 'number') {
    const seenAt = new Date(Date.now() - live.age);
    lastSeenStr = seenAt.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
    monModalStaticLastSeen = lastSeenStr;
  }

  const isFestoolBattery = (baseType === 'Battery');
  const socVal = (live && typeof live.soc === 'number' && live.soc >= 0)
    ? live.soc
    : ((typeof m.soc === 'number' && m.soc >= 0) ? m.soc : -1);

  const statusHtml = isCfg
    ? '<span style="color:#9a5b00;">Configuring</span>'
    : (isAct ? '<span style="color:var(--accent);">Active</span>' : 'Idle');
  const modeLabel = m.is_hose ? 'Auto (Tap=Toggle / Hold=Momentary)' : (m.btnType > 0 ? 'Toggle' : 'Auto Tool');
  const isToolPlug = (baseType === 'Tool Plug');
  const wattsVal = (typeof m.watts === 'number' && m.watts >= 0) ? m.watts : -1;
  const thrVal = m.watts_thr || m.wattsThr || 60;

  const modalKey = `${m.name}|${m.mac}|${modelLine}|${typeLabel}|${barsCount}|${lastSeenStr}|${socVal}|${wattsVal}|${thrVal}|${isCfg?1:0}|${isAct?1:0}|${m.speed}|${modeLabel}`;
  if (modalKey !== lastRenderedMonModalKey) {
    lastRenderedMonModalKey = modalKey;
    const rows = [
      ['Model', modelLine],
      ['Device Type', typeLabel],
      ['Signal Strength', rssiHtml],
      ['Last Seen', lastSeenStr]
    ];
    if (isFestoolBattery) {
      rows.push(['Charge State', socVal >= 0 ? `${socVal}%` : '--']);
    }
    if (isToolPlug) {
      rows.push(['Live Power', rawRssi === null ? 'Off' : (wattsVal >= 0 ? `${wattsVal} W` : '--')]);
      rows.push(['Trigger Threshold', `${thrVal} W`]);
    }
    rows.push(['Status', statusHtml]);
    rows.push(['Preset & Mode', `${m.speed}% · ${modeLabel}`]);
    document.getElementById('mon-modal-body').innerHTML = rows.map(r =>
      `<div class="telem-row"><span class="telem-lbl">${r[0]}</span><span class="telem-val">${r[1]}</span></div>`
    ).join('');
  }
}

function showSettingsMsg(text, isError = false) {
  const el = document.getElementById('settings-msg');
  if (!el) return;
  el.textContent = text;
  el.style.display = 'block';
  el.style.background = isError ? 'var(--danger-soft)' : 'var(--accent-soft)';
  el.style.color = isError ? 'var(--danger)' : 'var(--accent)';
  el.style.border = isError ? '1px solid #dfb0b0' : '1px solid #9eb8a8';
}

function openSettings() {
  const msgEl = document.getElementById('settings-msg');
  if (msgEl) msgEl.style.display = 'none';
  fetch('/api/settings').then(r => { if (r.status === 401) { window.location.href = '/login'; throw new Error('401'); } return r.json(); }).then(data => {
     savedWifis = data.wifis || [];
     renderWifiList();
     document.getElementById('mqtt-en').checked = data.mqtt_en;
     document.getElementById('mqtt-ip').value = data.mqtt_ip || '';
     document.getElementById('mqtt-port').value = data.mqtt_port || 1883;
     document.getElementById('mqtt-user').value = data.mqtt_user || '';
     document.getElementById('mqtt-pass').value = data.mqtt_pass || '';
     toggleMqtt();
     document.getElementById('auth-en').checked = !!data.auth_en;
     document.getElementById('auth-user').value = data.auth_user || 'admin';
     document.getElementById('auth-pass').value = '';
     toggleAuthFields();
     document.getElementById('settings-modal').style.display='flex';
  }).catch(() => {});
}

function renderWifiList() {
  const list = document.getElementById('saved-wifi-list');
  cleanupActiveWifiDrag();
  list.innerHTML = '';
  if (savedWifis.length === 0) {
    list.innerHTML = '<div style="color:var(--sub); font-size:0.83rem; padding:8px 10px; background:var(--subcard); border:1px dashed var(--border); border-radius:8px; margin-bottom:8px; text-align:center;">No saved networks (using fallback AP)</div>';
    return;
  }
  savedWifis.forEach((w, i) => {
    const masked = w.pass ? '••••••••' : '(Open Network)';
    const row = document.createElement('div');
    row.className = 'wifi-saved-row';
    row.dataset.idx = String(i);
    row.innerHTML = `
      <span class="drag-handle" title="Drag to reorder Wi-Fi priority">${GRIP_SVG}</span>
      <div style="flex:1; min-width:0; overflow:hidden; text-overflow:ellipsis;"><strong>${escHtml(w.ssid)}</strong><br><span style="font-size:0.8rem; color:var(--sub);">${masked}</span></div>
      <button type="button" class="icon-btn wifi-del-btn" style="color:var(--danger); flex-shrink:0;" title="Remove Network" aria-label="Remove Network">${TRASH_SVG}</button>
    `;

    const delBtn = row.querySelector('.wifi-del-btn');
    if (delBtn) {
      delBtn.addEventListener('click', () => {
        const curIdx = parseInt(row.dataset.idx || '-1', 10);
        if (curIdx >= 0 && curIdx < savedWifis.length) {
          const ssidName = savedWifis[curIdx].ssid;
          openConfirmModal(
            'Remove Wi-Fi Network',
            `Remove "${ssidName}" from saved Wi-Fi networks?`,
            'Remove',
            () => {
              const liveIdx = savedWifis.findIndex(item => item.ssid === ssidName);
              if (liveIdx >= 0) {
                savedWifis.splice(liveIdx, 1);
                renderWifiList();
              }
            }
          );
        }
      });
    }

    const handle = row.querySelector('.drag-handle');
    if (handle) {
      handle.addEventListener('pointerdown', (e) => {
        if (e.pointerType === 'mouse' && e.button !== 0) return;
        e.preventDefault();
        cleanupActiveWifiDrag();

        const startIdx = parseInt(row.dataset.idx || '0', 10);
        const origRect = row.getBoundingClientRect();
        const offsetY = e.clientY - origRect.top;

        const floatingEl = document.createElement('div');
        floatingEl.className = 'wifi-floating-item';
        floatingEl.innerHTML = row.innerHTML;
        floatingEl.style.left = `${origRect.left}px`;
        floatingEl.style.top = `${origRect.top}px`;
        floatingEl.style.width = `${origRect.width}px`;
        floatingEl.style.height = `${origRect.height}px`;
        document.body.appendChild(floatingEl);

        row.classList.add('is-placeholder');
        document.body.style.cursor = 'grabbing';

        const onMove = (ev) => {
          if (!activeWifiDrag || activeWifiDrag.pointerId !== ev.pointerId) return;
          ev.preventDefault();

          const floatTop = ev.clientY - activeWifiDrag.offsetY;
          activeWifiDrag.floatingEl.style.top = `${floatTop}px`;
          const floatCenterY = floatTop + (activeWifiDrag.height / 2);

          const rows = Array.from(list.querySelectorAll('.wifi-saved-row'));
          let targetIdx = activeWifiDrag.currIdx;
          for (let idx = 0; idx < rows.length; idx++) {
            if (idx === activeWifiDrag.currIdx) continue;
            const r = rows[idx].getBoundingClientRect();
            const midY = r.top + (r.height / 2);
            if (idx > activeWifiDrag.currIdx && floatCenterY > midY) {
              targetIdx = idx;
            } else if (idx < activeWifiDrag.currIdx && floatCenterY < midY) {
              targetIdx = idx;
              break;
            }
          }

          if (targetIdx !== activeWifiDrag.currIdx) {
            const prevTops = new Map();
            rows.forEach((r) => {
              if (r !== activeWifiDrag.placeholderRow) {
                prevTops.set(r, r.getBoundingClientRect().top);
              }
            });

            const [moved] = savedWifis.splice(activeWifiDrag.currIdx, 1);
            savedWifis.splice(targetIdx, 0, moved);
            if (targetIdx > activeWifiDrag.currIdx) {
              list.insertBefore(activeWifiDrag.placeholderRow, rows[targetIdx].nextSibling);
            } else {
              list.insertBefore(activeWifiDrag.placeholderRow, rows[targetIdx]);
            }
            activeWifiDrag.currIdx = targetIdx;

            const updatedRows = Array.from(list.querySelectorAll('.wifi-saved-row'));
            updatedRows.forEach((r, newIdx) => {
              r.dataset.idx = String(newIdx);
              if (r === activeWifiDrag.placeholderRow) return;
              const oldTop = prevTops.get(r);
              if (oldTop === undefined) return;
              const newTop = r.getBoundingClientRect().top;
              const deltaY = oldTop - newTop;
              if (deltaY !== 0) {
                r.style.transition = 'none';
                r.style.transform = `translateY(${deltaY}px)`;
                void r.offsetHeight;
                r.style.transition = 'transform 180ms cubic-bezier(0.2, 0, 0, 1)';
                r.style.transform = '';
              }
            });
          }
        };

        const onUp = (ev) => {
          if (!activeWifiDrag) return;
          if (ev && ev.pointerId !== undefined && activeWifiDrag.pointerId !== ev.pointerId) return;
          const drag = activeWifiDrag;
          const orderChanged = (drag.currIdx !== drag.startIdx);
          activeWifiDrag = null;
          lastWifiDragEndMs = Date.now();

          window.removeEventListener('pointermove', drag.onMove);
          window.removeEventListener('pointerup', drag.onUp);
          window.removeEventListener('pointercancel', drag.onUp);
          window.removeEventListener('blur', drag.onBlur);
          try { drag.handle.releasePointerCapture(drag.pointerId); } catch (_) {}
          document.body.style.cursor = '';

          const destRect = drag.placeholderRow.getBoundingClientRect();
          drag.floatingEl.style.transition = 'top 160ms cubic-bezier(0.2, 0, 0, 1), left 160ms cubic-bezier(0.2, 0, 0, 1), transform 160ms ease, box-shadow 160ms ease';
          drag.floatingEl.style.top = `${destRect.top}px`;
          drag.floatingEl.style.left = `${destRect.left}px`;
          drag.floatingEl.style.transform = 'scale(1)';
          drag.floatingEl.style.boxShadow = 'none';

          if (orderChanged) {
            persistWifiOrder();
          }

          setTimeout(() => {
            drag.floatingEl.remove();
            drag.placeholderRow.classList.remove('is-placeholder');
          }, 165);
        };

        const onBlur = () => onUp(null);

        activeWifiDrag = {
          pointerId: e.pointerId,
          handle,
          placeholderRow: row,
          floatingEl,
          startIdx,
          currIdx: startIdx,
          offsetY,
          height: origRect.height,
          onMove,
          onUp,
          onBlur
        };

        window.addEventListener('pointermove', onMove, { passive: false });
        window.addEventListener('pointerup', onUp);
        window.addEventListener('pointercancel', onUp);
        window.addEventListener('blur', onBlur);
      });
    }

    list.appendChild(row);
  });
}

function addWifi() {
  const s = document.getElementById('new-ssid').value.trim();
  const p = document.getElementById('new-pass').value.trim();
  if (!s) return;
  const idx = savedWifis.findIndex(w => w.ssid.toLowerCase() === s.toLowerCase());
  if (idx >= 0) { savedWifis[idx] = {ssid: s, pass: p}; renderWifiList(); document.getElementById('new-ssid').value = ''; document.getElementById('new-pass').value = ''; }
  else if (savedWifis.length < 5) { savedWifis.push({ssid: s, pass: p}); renderWifiList(); document.getElementById('new-ssid').value = ''; document.getElementById('new-pass').value = ''; }
  else showSettingsMsg('Max 5 networks allowed.', true);
}

function toggleMqtt() { document.getElementById('mqtt-fields').style.display = document.getElementById('mqtt-en').checked ? 'block' : 'none'; }

function toggleAuthFields() { document.getElementById('auth-fields').style.display = document.getElementById('auth-en').checked ? 'block' : 'none'; }

function logoutSession() {
  fetch('/api/auth/logout', { method: 'POST' }).finally(() => { window.location.href = '/login'; });
}

function saveSettings() {
  const authEn = document.getElementById('auth-en').checked;
  const authUser = document.getElementById('auth-user').value.trim();
  const authPass = document.getElementById('auth-pass').value;
  if (authEn && !authUser) {
    showSettingsMsg('Username is required when login is enabled.', true);
    return;
  }
  const parsedPort = parseInt(document.getElementById('mqtt-port').value, 10);
  const safePort = (!isNaN(parsedPort) && parsedPort > 0 && parsedPort <= 65535) ? parsedPort : 1883;
  const payload = {
    wifis: savedWifis,
    mqtt_en: document.getElementById('mqtt-en').checked,
    mqtt_ip: document.getElementById('mqtt-ip').value,
    mqtt_port: safePort,
    mqtt_user: document.getElementById('mqtt-user').value,
    mqtt_pass: document.getElementById('mqtt-pass').value,
    auth_en: authEn,
    auth_user: authUser,
    auth_pass: authPass
  };
  fetch('/api/settings/save', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(payload) })
  .then(async r => {
    if (r.status === 401) { window.location.href = '/login'; return; }
    if (!r.ok) {
      const errData = await r.json().catch(() => ({}));
      showSettingsMsg(errData.error || 'Could not save settings.', true);
      return;
    }
    showSettingsMsg('Settings saved! Rebooting...');
    setTimeout(() => { document.getElementById('settings-modal').style.display='none'; }, 1200);
    setTimeout(() => { window.location.reload(); }, 3500);
  });
}

function setPower(p) {
  ignorePollUntil = Date.now() + 900;
  evacEndMs = 0;
  updateControlUI(p, uiSpeed);
  abortInFlightPoll();
  fetch(`/api/control?power=${p}`).then(r => r.json()).then(applyStatusResponse);
}

function setSpeed(val) {
  uiSpeed = val;
  ignorePollUntil = Date.now() + 900;
  evacEndMs = 0;
  updateControlUI(1, val);
  abortInFlightPoll();
  fetch(`/api/control?power=1&speed=${val}`).then(r => r.json()).then(applyStatusResponse);
}

function updateEvacSec(val) {
  let s = parseInt(val);
  if (isNaN(s) || s < 0) s = 0;
  if (s > 60) s = 60;
  lastRenderedVacKey = '';
  abortInFlightPoll();
  fetch(`/api/evac?sec=${s}`).then(r => r.json()).then(applyStatusResponse);
}

function styleBtnIdle(el) {
  el.style.background = '#eef0eb';
  el.style.borderColor = '#d5d0be';
  el.style.color = '#1f2e26';
}

function styleBtnActive(el) {
  el.style.background = '#283b31';
  el.style.borderColor = '#283b31';
  el.style.color = '#f7f3e3';
}

function updateControlUI(power, speed) {
    uiPower = power;
    if (speed) uiSpeed = speed;
    const btns = ['20', '40', '60', '80', '100'];
    const offBtn = document.getElementById('btn-off');
    const remMs = evacEndMs - Date.now();

    if (remMs > 0) {
        const secs = Math.ceil(remMs / 1000);
        offBtn.innerText = `EVAC ${secs}s`;
        offBtn.style.background = '#c27803';
        offBtn.style.borderColor = '#c27803';
        offBtn.style.color = '#ffffff';
        btns.forEach(b => {
            let el = document.getElementById('btn-' + b);
            if (parseInt(b) === 20) styleBtnActive(el);
            else styleBtnIdle(el);
        });
    } else if (power === 3) {
        offBtn.innerText = 'OFF';
        offBtn.style.background = '#b83232';
        offBtn.style.borderColor = '#b83232';
        offBtn.style.color = '#ffffff';
        btns.forEach(b => styleBtnIdle(document.getElementById('btn-' + b)));
    } else if (power === 1) {
        offBtn.innerText = 'OFF';
        offBtn.style.background = '#b83232';
        offBtn.style.borderColor = '#b83232';
        offBtn.style.color = '#ffffff';
        btns.forEach(b => {
            let el = document.getElementById('btn-' + b);
            if (parseInt(b) === speed) styleBtnActive(el);
            else styleBtnIdle(el);
        });
    }
}

setInterval(() => {
    if (evacEndMs > 0) {
        if (Date.now() >= evacEndMs) {
            evacEndMs = 0;
            updateControlUI(3, uiSpeed);
        } else {
            updateControlUI(uiPower, uiSpeed);
        }
    }
}, 200);

function pairExtractor(mac, btnEl) {
  pairingMac = mac.toLowerCase();
  pairingStartedMs = Date.now();
  pairingSawConnecting = false;
  if (btnEl) {
    btnEl.disabled = true;
    btnEl.innerText = 'PAIRING...';
  }
  lastRenderedVacKey = '';
  abortInFlightPoll();
  fetch(`/api/pair?mac=${encodeURIComponent(mac)}`).then(r => r.json()).then(applyStatusResponse);
}

function unpairExtractor(btnEl) {
  if (document.activeElement && document.activeElement.blur) document.activeElement.blur();
  if (btnEl) btnEl.disabled = true;
  lastRenderedVacKey = '';
  abortInFlightPoll();
  fetch('/api/forget').then(r => r.json()).then(applyStatusResponse);
}

function focusInlineName(btnEl) {
  if (btnEl && btnEl.dataset.wasFocused === '1') {
    btnEl.dataset.wasFocused = '';
    return;
  }
  const row = btnEl ? btnEl.closest('.vac-top') : null;
  const inp = row ? row.querySelector('.inline-name-input') : null;
  if (inp) {
    inp.focus();
    inp.select();
  }
}

function handleInlineNameKey(e, inp) {
  if (e.key === 'Enter') {
    e.preventDefault();
    inp.blur();
  } else if (e.key === 'Escape') {
    e.preventDefault();
    inp.value = inp.dataset.orig || '';
    inp.blur();
  }
}

function commitExtName(inp) {
  const orig = inp.dataset.orig || '';
  const n = inp.value.trim();
  if (!n) {
    inp.value = orig;
    return;
  }
  if (n === orig) {
    inp.value = orig;
    return;
  }
  inp.value = n;
  inp.dataset.orig = n;
  if (latestStatusData) latestStatusData.ext_name = n;
  lastRenderedVacKey = '';
  abortInFlightPoll();
  fetch(`/api/rename_ext?name=${encodeURIComponent(n)}`).then(r => r.json()).then(applyStatusResponse);
}

function commitMonitoredName(inp) {
  const mac = inp.dataset.mac || '';
  const orig = inp.dataset.orig || '';
  const n = inp.value.trim();
  if (!n || !mac) {
    inp.value = orig;
    return;
  }
  if (n === orig) {
    inp.value = orig;
    return;
  }
  inp.value = n;
  inp.dataset.orig = n;
  if (latestStatusData && Array.isArray(latestStatusData.monitored)) {
    const item = latestStatusData.monitored.find(x => x.mac.toLowerCase() === mac.toLowerCase());
    if (item) item.name = n;
  }
  lastRenderedMonKey = '';
  abortInFlightPoll();
  fetch(`/api/monitored/rename?mac=${encodeURIComponent(mac)}&name=${encodeURIComponent(n)}`).then(r => r.json()).then(applyStatusResponse);
}

function updateMonitoredSpeed(mac, spd) { lastRenderedMonKey = ''; abortInFlightPoll(); fetch(`/api/monitored/update?mac=${encodeURIComponent(mac)}&speed=${spd}`).then(r=>r.json()).then(applyStatusResponse); }
function updateMonitoredWattsThr(mac, thr) {
  const w = parseInt(thr, 10) || 60;
  if (latestStatusData && Array.isArray(latestStatusData.monitored)) {
    const item = latestStatusData.monitored.find(x => x.mac.toLowerCase() === mac.toLowerCase());
    if (item) {
      item.watts_thr = w;
      item.wattsThr = w;
    }
  }
  lastRenderedMonKey = '';
  lastRenderedMonModalKey = '';
  abortInFlightPoll();
  fetch(`/api/monitored/update?mac=${encodeURIComponent(mac)}&wattsThr=${w}`).then(r=>r.json()).then(applyStatusResponse);
}
function toggleHoseRole(mac, nextHose) {
  if (document.activeElement) document.activeElement.blur();
  if (latestStatusData && Array.isArray(latestStatusData.monitored)) {
    const item = latestStatusData.monitored.find(x => x.mac.toLowerCase() === mac.toLowerCase());
    if (item) {
      item.is_hose = !!nextHose;
      item.await_rel = false;
      if (item.is_hose) {
        item.is_gatt = true;
      } else if (item.can_adv) {
        item.cfg = false;
      }
    }
  }
  lastRenderedMonKey = '';
  abortInFlightPoll();
  if (latestStatusData) renderAllFromStatus(latestStatusData, true);
  fetch(`/api/monitored/hose?mac=${encodeURIComponent(mac)}&hose=${nextHose ? 1 : 0}`).then(r=>r.json()).then(applyStatusResponse);
}

function renderAllFromStatus(data, forceUpdate = false) {
      const logoutBtn = document.getElementById('logout-btn');
      if (logoutBtn) logoutBtn.style.display = data.auth_en ? 'flex' : 'none';

      const slotWarnEl = document.getElementById('gatt-slot-warn');
      if (slotWarnEl) {
        const cfgCnt = data.gatt_switches_cfg || 0;
        const maxSlots = data.gatt_slots_max || 2;
        if (cfgCnt > maxSlots) {
          slotWarnEl.textContent = `${cfgCnt} GATT switches configured (${maxSlots} active slots available; idle switches rotate automatically).`;
          slotWarnEl.style.display = 'block';
        } else {
          slotWarnEl.style.display = 'none';
        }
      }

      if (document.getElementById('ext-info-modal').style.display === 'flex') {
          renderExtInfoModal(data);
      }
      if (document.getElementById('mon-info-modal').style.display === 'flex') {
          if (activeDiscModalMac) renderDiscInfoModal(data);
          else renderMonInfoModal(data);
      }

      if (data.evac_rem_ms && data.evac_rem_ms > 0) {
          evacEndMs = Date.now() + data.evac_rem_ms;
      } else if (Date.now() > ignorePollUntil) {
          evacEndMs = 0;
      }
      if (forceUpdate || Date.now() > ignorePollUntil) {
          updateControlUI(data.power, data.speed);
      }
      const wrap = document.getElementById('controls-wrap');
      const cBtns = document.querySelectorAll('.ctrl-btn');
      const fullyReady = (data.paired_mac.length > 0 && data.state === 'CONNECTED');

      if (fullyReady) {
          wrap.classList.remove('controls-disabled'); cBtns.forEach(b => b.disabled = false);
      } else {
          wrap.classList.add('controls-disabled'); cBtns.forEach(b => b.disabled = true);
      }

      const upBadge = document.getElementById('unpaired-badge');
      if (upBadge) upBadge.style.display = data.paired_mac ? 'none' : 'inline-block';

      const extLive = data.paired_mac ? data.devices.find(d => d.address.toLowerCase() === data.paired_mac.toLowerCase()) : null;
      const extRssi = (typeof data.paired_rssi === 'number' && data.paired_rssi < 0) ? data.paired_rssi : (extLive ? extLive.rssi : null);

      let connPillCls = 'badge pill-disc';
      let connPillContent = '<span>Disconnected</span>';
      if (data.state === 'CONNECTED') {
          connPillCls = 'badge pill-conn';
          connPillContent = `${rssiBarsSvg(extRssi)}`;
      } else if (data.state === 'CONNECTING') {
          connPillCls = 'badge pill-pair';
          connPillContent = '<span>Connecting</span>';
      }

      const isExtractorDev = (d) => {
          if (!d || !d.isKnownDevice) return false;
          if (d.type === 'Extractor') return true;
          const n = (d.name || '').toUpperCase();
          if (n.includes('CT-F') || n.includes('CTF')) return false;
          return /\b(CT|CTL|CTM|CTH|CLEANTEC)\b/.test(n) || n.includes('MIDI') || n.includes('MINI');
      };

      const dustDevices = data.devices.filter(d => isExtractorDev(d) && (d.age === undefined || d.age < 300000));

      const t = data.telem || {};
      const faultLabel = t.faults || 'Healthy';
      const isUnhealthy = (faultLabel !== 'Healthy');
      const faultHtml = isUnhealthy ? `<span class="badge pill-warn" title="Fault Status">${faultLabel}</span>` : '';
      const filterShort = fmtFilterRemShort(t.filter_sec);

      const vacSec = document.getElementById('vac-section');
      if (pairingMac) {
        if (data.state === 'CONNECTING') pairingSawConnecting = true;
        if ((data.paired_mac && data.paired_mac.toLowerCase() === pairingMac) ||
            (pairingSawConnecting && data.state === 'DISCONNECTED' && !data.paired_mac) ||
            (Date.now() - pairingStartedMs > 5000)) {
          pairingMac = '';
          pairingSawConnecting = false;
        }
      }

      const vacKey = `${data.paired_mac}|${data.state}|${rssiBarLevel(extRssi)}|${data.ext_name}|${data.evac_sec}|${pairingMac}|${faultLabel}|${filterShort}|${dustDevices.map(x => `${x.address}:${rssiBarLevel(x.rssi)}`).join(',')}`;
      const activeEl = document.activeElement;
      const vacTag = activeEl ? activeEl.tagName : '';
      const vacEditingName = !!(activeEl && vacSec.contains(activeEl) && activeEl.classList && activeEl.classList.contains('inline-name-input'));
      const vacEditing = vacEditingName || (!forceUpdate && (vacSec.contains(activeEl) && (vacTag === 'SELECT' || vacTag === 'INPUT')));
      if (!vacEditing && (vacKey !== lastRenderedVacKey || forceUpdate)) {
        lastRenderedVacKey = vacKey;
        let vHtml = '';
        if (data.paired_mac) {
          const connRssiHtml = `<span id="conn-badge" class="${connPillCls}" title="GATT Connection & Signal Strength">${connPillContent}</span>`;
          vHtml += `<div class="vac-row is-paired">
              <div class="vac-top">
                <div class="name-edit" style="flex:1; min-width:0; flex-wrap:nowrap;">
                  <input type="text" class="inline-name-input" style="font-size:1rem; width:100%; max-width:260px;" value="${escHtml(data.ext_name)}" data-orig="${escHtml(data.ext_name)}" aria-label="Extractor Name" onkeydown="handleInlineNameKey(event, this)" onblur="commitExtName(this)">
                </div>
                <div class="top-right-icons">
                  <button type="button" class="icon-btn" title="Edit Name" onmousedown="this.dataset.wasFocused=(document.activeElement===this.closest('.vac-top').querySelector('.inline-name-input'))?'1':''" onclick="focusInlineName(this)" style="color:var(--sub); padding:2px; flex-shrink:0;">${EDIT_SVG}</button>
                  ${connRssiHtml}
                  ${rolePillHtml(true)}
                  <button type="button" class="icon-btn" title="Extractor Information" onclick="openExtInfoModal()" style="color:var(--accent); padding:2px; flex-shrink:0;">${INFO_SVG}</button>
                  <button type="button" class="icon-btn" style="color:var(--danger); padding:2px 4px; flex-shrink:0;" title="Unpair Extractor" aria-label="Unpair Extractor" onclick="confirmUnpairExtractor()">${TRASH_SVG}</button>
                </div>
              </div>
              <div class="vac-bottom">
                <div class="vac-pills">
                  <span class="badge small" title="Filter Hours Remaining">${filterShort}</span>
                  ${faultHtml}
                </div>
                <div class="vac-actions">
                  <label class="evac-wrap" title="Additional seconds of debris evacuation at 20% before shutting off">
                    <span>Delay:</span>
                    <input type="number" min="0" max="60" class="evac-input" value="${data.evac_sec}" onkeydown="if(event.key==='Enter'){event.preventDefault();this.blur();}" onchange="updateEvacSec(this.value)">
                    <span>s</span>
                  </label>
                </div>
              </div>
            </div>`;
        }
        dustDevices.forEach(f => {
          if(f.address.toLowerCase() !== data.paired_mac.toLowerCase()) {
            const isPairingThis = (pairingMac && f.address.toLowerCase() === pairingMac);
            const pairBtn = isPairingThis
              ? `<button class="btn-pair" disabled>PAIRING...</button>`
              : `<button class="btn-pair" onclick="pairExtractor('${f.address}', this)">PAIR</button>`;
            vHtml += `<div class="vac-row">
              <div class="vac-top">
                <strong style="color:var(--text); font-size:0.98rem; overflow:hidden; text-overflow:ellipsis; white-space:nowrap;">${escHtml(f.name)}</strong>
                <div class="top-right-icons">
                  ${rssiPillHtml(f.rssi, f.age || 0)}
                </div>
              </div>
              <div class="vac-bottom">
                <div class="vac-pills"><span class="info-text" style="margin-top:0;">MAC: ${escHtml(f.address)}</span></div>
                <div class="vac-actions">${pairBtn}</div>
              </div>
            </div>`;
          }
        });
        vacSec.innerHTML = vHtml || '<div style="color:var(--sub); font-size:0.88rem; text-align:center; padding:12px 0;">Put your extractor in pairing mode.</div>';
      }

      const monMacSet = new Set((data.monitored || []).map(m => m.mac.toLowerCase()));
      const pairedLow = (data.paired_mac || '').toLowerCase();

      const discListEl = document.getElementById('discovered-list');
      if (discListEl) {
        const discDevices = (data.devices || []).filter(d => {
          const macLow = d.address.toLowerCase();
          if (!d.isKnownDevice || isExtractorDev(d)) return false;
          if (d.type === 'Festool') return false;
          if (monMacSet.has(macLow) || (pairedLow && macLow === pairedLow)) return false;
          return (d.age === undefined || d.age < 60000);
        });
        const discKey = discDevices.map(k => {
          const wattsBucket = (k.type === 'Tool Plug' && typeof k.watts === 'number' && k.watts >= 0) ? Math.round(k.watts / 5) : -1;
          return `${k.address}:${k.name}:${rssiBarLevel(k.rssi)}:${k.type}:${k.can_adv?1:0}:${k.can_gatt?1:0}:${k.soc}:${wattsBucket}`;
        }).join('|');
        if (discKey !== lastRenderedDiscKey || forceUpdate) {
          lastRenderedDiscKey = discKey;
          if (discDevices.length > 0) {
            discListEl.innerHTML = discDevices.map(k => {
              const socPill = (typeof k.soc === 'number' && k.soc >= 0) ? `<span class="badge small" title="Battery Charge">${k.soc}%</span>` : '';
              const isToolPlug = (k.type === 'Tool Plug');
              const isSwitch = (k.type === 'Button');
              const swMode = isSwitch ? discSwitchModeInfo(k) : null;
              const swModePill = swMode ? `<span class="${swMode.cls}" title="${swMode.tip}">${swMode.label}</span>` : '';
              const hasValidRssi = (typeof k.rssi === 'number' && k.rssi < 0 && (k.age === undefined || k.age <= 300000));
              const barsCount = hasValidRssi ? rssiBarLevel(k.rssi) : 0;
              const hasWatts = hasValidRssi && isToolPlug && (typeof k.watts === 'number' && k.watts >= 0);
              const signalTitle = hasValidRssi ? `${barsCount}/4 bars` : 'No signal';
              const topSignalPill = isToolPlug
                ? (hasValidRssi
                    ? `<span class="badge small rssi-pill" title="${signalTitle}">${rssiBarsSvg(k.rssi, false)}<span class="disc-plug-watts-val" data-mac="${escHtml(k.address)}">${hasWatts ? `${k.watts}W` : ''}</span></span>`
                    : `<span class="badge small rssi-pill" title="No signal">${rssiBarsSvg(null, false)}<span>Off</span></span>`)
                : rssiPillHtml(k.rssi, k.age || 0);
              const bType = (k.type === 'Button') ? 1 : 0;
              return `<div class="found-row">
                <div class="vac-top">
                  <strong style="color:var(--text); font-size:0.98rem; overflow:hidden; text-overflow:ellipsis; white-space:nowrap;">${escHtml(k.name)}</strong>
                  <div class="top-right-icons">
                    ${swModePill}
                    ${topSignalPill}
                    <button type="button" class="icon-btn" title="Device Information" onclick="openDiscInfoModal('${k.address}')" style="color:var(--accent); padding:2px; flex-shrink:0;">${INFO_SVG}</button>
                  </div>
                </div>
                <div class="vac-bottom">
                  <div class="vac-pills">
                    <span class="info-text" style="margin-top:0;">MAC: ${escHtml(k.address)}</span>
                    ${socPill}
                  </div>
                  <div class="vac-actions">
                    <button class="btn-pair" style="padding:6px 12px; font-size:0.78rem;" data-mac="${escHtml(k.address)}" data-name="${escHtml(k.name || k.type)}" data-btype="${bType}" data-dtype="${escHtml(k.type || '')}" data-raw="${escHtml(k.raw || '')}" data-rssi="${k.rssi || 0}" data-at="${k.addr_type || 0}" data-cadv="${k.can_adv ? 1 : 0}" data-cgatt="${k.can_gatt ? 1 : 0}" onclick="addFoundDevice(this.dataset.mac, this.dataset.name, parseInt(this.dataset.btype,10), this.dataset.raw, parseInt(this.dataset.rssi,10), parseInt(this.dataset.at,10), this.dataset.dtype, this.dataset.cadv==='1', this.dataset.cgatt==='1')">+ Add</button>
                  </div>
                </div>
              </div>`;
            }).join('');
          } else {
            discListEl.innerHTML = '<div style="color:var(--sub); font-size:0.86rem; text-align:center; padding:10px 0;">Listening for devices.</div>';
          }
        } else {
          discDevices.forEach(k => {
            if (k.type !== 'Tool Plug') return;
            const span = discListEl.querySelector(`.disc-plug-watts-val[data-mac="${k.address}"]`);
            if (span) {
              const hasValidRssi = (typeof k.rssi === 'number' && k.rssi < 0 && (k.age === undefined || k.age <= 300000));
              span.textContent = (hasValidRssi && typeof k.watts === 'number' && k.watts >= 0) ? `${k.watts}W` : '';
            }
          });
        }
      }

      const nowMs = Date.now();
      const filteredMon = (data.monitored || []).filter(m => {
        const exp = recentlyDeletedMacs.get(m.mac.toLowerCase());
        if (exp && nowMs < exp) return false;
        recentlyDeletedMacs.delete(m.mac.toLowerCase());
        return true;
      });

      const monList = document.getElementById('monitored-list');
      const monStatusSnap = filteredMon.map(m => {
        const live = data.devices.find(d => d.address.toLowerCase() === m.mac.toLowerCase());
        const isCfg = !!m.cfg;
        const isAct = (!isCfg && !m.await_rel)
          ? (m.btnType > 0 ? !!m.btn_live : (live ? (live.state === 1 && live.age < 8000) : false))
          : false;
        const effRssi = (live && typeof live.rssi === 'number' && live.rssi < 0 && live.age <= 300000)
          ? live.rssi
          : ((typeof m.rssi === 'number' && m.rssi < 0 && (m.rssi_age === undefined || m.rssi_age <= 300000)) ? m.rssi : null);
        return { m, cfg: isCfg, act: isAct, rssi: effRssi, soc: live ? live.soc : (m.soc !== undefined ? m.soc : -1) };
      });
      const monKey = monStatusSnap.map(({ m, cfg, act, rssi, soc }) => {
        const hasValidRssi = (typeof rssi === 'number' && rssi < 0);
        const wattsBucket = (hasValidRssi && m.dev_type === 'Tool Plug' && typeof m.watts === 'number' && m.watts >= 0) ? Math.round(m.watts / 5) : -1;
        return `${m.mac}:${m.name}:${m.speed}:${m.watts_thr}:${wattsBucket}:${m.is_gatt?1:0}:${m.can_gatt?1:0}:${m.is_hose?1:0}:${m.gatt_linked?1:0}:${cfg?1:0}:${m.await_rel?1:0}:${act?1:0}:${rssiBarLevel(rssi)}:${soc}`;
      }).join('|');
      const monActiveEl = document.activeElement;
      const monTag = monActiveEl ? monActiveEl.tagName : '';
      const monEditingName = !!(monActiveEl && monList.contains(monActiveEl) && monActiveEl.classList && monActiveEl.classList.contains('inline-name-input'));
      const monEditing = monEditingName || (!forceUpdate && monList.contains(monActiveEl) && (monTag === 'SELECT' || monTag === 'INPUT'));
      if (!monEditing && (monKey !== lastRenderedMonKey || forceUpdate)) {
        lastRenderedMonKey = monKey;
        let mHtml = '';
        const steps = [20, 40, 60, 80, 100];
        const wattSteps = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 90, 100, 125, 150, 200, 250, 300, 400, 500];
        monStatusSnap.forEach(({ m, cfg, act, rssi, soc }) => {
          const hasValidRssi = (typeof rssi === 'number' && rssi < 0);
          const barsCount = hasValidRssi ? rssiBarLevel(rssi) : 0;
          const isToolPlug = (m.dev_type === 'Tool Plug');
          const hasWatts = hasValidRssi && isToolPlug && (typeof m.watts === 'number' && m.watts >= 0);
          const pillInner = isToolPlug
            ? (hasValidRssi ? `${rssiBarsSvg(rssi, act)}<span class="plug-watts-val" data-mac="${escHtml(m.mac)}">${hasWatts ? `${m.watts}W` : ''}</span>` : `${rssiBarsSvg(null, false)}<span>Off</span>`)
            : `${rssiBarsSvg(hasValidRssi ? rssi : null, act)}`;
          const signalTitle = hasValidRssi ? `${barsCount}/4 bars` : 'No signal';
          let statusPillHtml = `<span class="badge small rssi-pill" title="Idle · ${signalTitle}">${pillInner}</span>`;
          if (m.await_rel) {
            statusPillHtml = `<span class="badge pill-pair" title="Paired — release button to arm">Release</span>`;
          } else if (cfg) {
            statusPillHtml = `<span class="badge pill-pair" title="Waiting to link GATT button">Configuring</span>`;
          } else if (act) {
            statusPillHtml = `<span class="badge pill-conn" title="Active · ${signalTitle}">${pillInner}</span>`;
          }
          const socPill = (soc >= 0) ? `<span class="badge small" title="Battery Charge">${soc}%</span>` : '';
          const monRolePill = rolePillHtml(!!m.is_gatt, cfg);
          const hoseCtrl = (m.btnType > 0 && (m.is_gatt || m.can_gatt))
            ? `<label class="tog-wrap${m.is_hose ? ' on' : ''}" title="${m.is_hose ? 'Primary Switch (GATT): Priority Override, Tap=Toggle, Hold=Momentary, 2x/3x Speed Control' : 'Toggle on to enable Primary Switch mode (GATT link, Hold-to-Run, Priority Override & 2x/3x Speed)'}"><input type="checkbox" style="display:none;" ${m.is_hose ? 'checked' : ''} onchange="toggleHoseRole('${m.mac}', this.checked)"><span class="tog-track"><span class="tog-thumb"></span></span><span>Primary</span></label>`
            : '';
          const curThr = m.watts_thr || m.wattsThr || 60;
          const allWattSteps = wattSteps.includes(curThr) ? wattSteps : [...wattSteps, curThr].sort((a, b) => a - b);
          const thrCtrl = isToolPlug
            ? `<select class="spd-select" title="Trigger Threshold (Watts)" onchange="updateMonitoredWattsThr('${m.mac}', this.value)">${allWattSteps.map(w => `<option value="${w}" ${curThr===w?'selected':''}>${w}W</option>`).join('')}</select>`
            : '';
          const opts = steps.map(s => `<option value="${s}" ${m.speed===s?'selected':''}>${s}%</option>`).join('');
          const spdCtrl = `<select class="spd-select" onchange="updateMonitoredSpeed('${m.mac}', this.value)">${opts}</select>`;
          const infoBtn = `<button type="button" class="icon-btn" title="Device Information" onclick="openMonInfoModal('${m.mac}')" style="color:var(--accent); padding:2px; flex-shrink:0;">${INFO_SVG}</button>`;
          const pairHintHtml = m.await_rel
            ? '<span style="font-size:0.74rem; color:#9a5b00; font-weight:500;">Release button to arm</span>'
            : ((cfg && m.is_gatt && !m.gatt_linked) ? '<span style="font-size:0.74rem; color:#9a5b00; font-weight:500;">Press and hold to pair</span>' : '');
          mHtml += `<div class="monitored-row">
              <div class="vac-top">
                <div class="name-edit" style="flex:1; min-width:0; flex-wrap:nowrap;">
                  <input type="text" class="inline-name-input" style="font-size:0.98rem; width:100%; max-width:260px;" value="${escHtml(m.name)}" data-mac="${escHtml(m.mac)}" data-orig="${escHtml(m.name)}" aria-label="Device Name" onkeydown="handleInlineNameKey(event, this)" onblur="commitMonitoredName(this)">
                </div>
                <div class="top-right-icons">
                  <button type="button" class="icon-btn" title="Edit Name" onmousedown="this.dataset.wasFocused=(document.activeElement===this.closest('.vac-top').querySelector('.inline-name-input'))?'1':''" onclick="focusInlineName(this)" style="color:var(--sub); padding:2px; flex-shrink:0;">${EDIT_SVG}</button>
                  ${statusPillHtml}
                  ${monRolePill}
                  ${infoBtn}
                  <button type="button" class="icon-btn" style="color:var(--danger); padding:2px 4px; flex-shrink:0;" title="Remove Device" aria-label="Remove Device" data-mac="${escHtml(m.mac)}" onclick="confirmDeleteMonitored(this.dataset.mac)">${TRASH_SVG}</button>
                </div>
              </div>
              <div class="vac-bottom">
                <div class="vac-pills">
                  ${pairHintHtml}
                  ${socPill}
                </div>
                <div class="vac-actions">
                  ${hoseCtrl}
                  ${thrCtrl}
                  ${spdCtrl}
                </div>
              </div>
            </div>`;
        });
        monList.innerHTML = mHtml || '<div style="color:var(--sub); text-align:center; padding:12px 0;">Activate a tool or press a button to discover.</div>';
      } else {
        monStatusSnap.forEach(({ m, rssi }) => {
          if (m.dev_type !== 'Tool Plug') return;
          const span = monList.querySelector(`.plug-watts-val[data-mac="${m.mac}"]`);
          if (span) {
            const hasValidRssi = (typeof rssi === 'number' && rssi < 0);
            span.textContent = (hasValidRssi && typeof m.watts === 'number' && m.watts >= 0) ? `${m.watts}W` : '';
          }
        });
      }
}

function pollStatus() {
  const reqEpoch = pollEpoch;
  if (pollAbortCtrl) {
    try { pollAbortCtrl.abort(); } catch (e) {}
  }
  pollAbortCtrl = new AbortController();
  return fetch('/api/status', { signal: pollAbortCtrl.signal }).then(r => {
      if (r.status === 401) {
          window.location.href = '/login';
          throw new Error('401');
      }
      return r.json();
  }).then(data => {
      if (reqEpoch !== pollEpoch) return;
      latestStatusData = data;
      renderAllFromStatus(data, false);
  });
}

function scanWifiNetworks() {
  const list = document.getElementById('wifi-scan-list');
  list.style.display = 'block';
  list.innerHTML = '<div style="padding:10px; font-size:0.84rem; color:var(--sub);"><span class="spinner"></span>Scanning Wi-Fi networks...</div>';
  fetch('/api/wifi/scan').then(async r => {
    if (r.status === 401) { window.location.href = '/login'; throw new Error('401'); }
    const data = await r.json().catch(() => null);
    if (!r.ok) {
      const msg = (data && data.error) ? data.error : 'Scan failed.';
      throw new Error(msg);
    }
    return data;
  }).then(nets => {
    if (!Array.isArray(nets) || nets.length === 0) {
      list.innerHTML = '<div style="padding:10px; font-size:0.84rem; color:var(--sub);">No networks found.</div>';
      return;
    }
    nets.sort((a, b) => (b.rssi || -100) - (a.rssi || -100));
    list.innerHTML = '';
    nets.forEach(n => {
      const item = document.createElement('div');
      item.className = 'wifi-item';
      item.innerHTML = `<span>${escHtml(n.ssid)}</span><span style="color:var(--sub); font-family:monospace;">${n.rssi} dBm</span>`;
      item.onclick = () => {
        document.getElementById('new-ssid').value = n.ssid;
        document.getElementById('new-pass').focus();
      };
      list.appendChild(item);
    });
  }).catch(err => {
    if (err && err.message === '401') return;
    list.innerHTML = `<div style="padding:10px; font-size:0.84rem; color:var(--danger);">${escHtml((err && err.message) || 'Scan failed.')}</div>`;
  });
}

setInterval(() => {
  if (document.hidden) return;
  pollStatus().catch(() => {});
}, 850);
pollStatus().catch(() => {});
</script>
</body>
</html>
)rawliteral";

const char OTA_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Firmware Update · BLE Dust Bridge</title>
<style>
  * { box-sizing: border-box; }
  body { margin: 0; min-height: 100vh; display: flex; align-items: center; justify-content: center; padding: 16px; background: #283b31; color: #1f2e26; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; }
  .card { width: 100%; max-width: 400px; background: #f7f3e3; border: 1px solid #dfd9c5; border-radius: 14px; padding: 24px 22px; box-shadow: 0 12px 30px rgba(0,0,0,0.28); }
  .brand { font-size: 1.25rem; font-weight: 700; color: #283b31; margin-bottom: 4px; text-align: center; }
  .sub { font-size: 0.82rem; color: #5c6b63; text-align: center; margin-bottom: 18px; }
  .file-box { background: #fbf9f1; border: 1px dashed #9eb8a8; border-radius: 10px; padding: 14px; text-align: center; margin-bottom: 14px; }
  input[type="file"] { width: 100%; font-size: 0.86rem; color: #1f2e26; }
  .bar-track { display: none; width: 100%; height: 10px; background: #e6e0cd; border-radius: 999px; overflow: hidden; margin: 12px 0 8px 0; border: 1px solid #dfd9c5; }
  .bar-fill { height: 100%; width: 0%; background: #283b31; transition: width 0.15s ease; }
  .status { display: none; padding: 9px 11px; border-radius: 8px; font-size: 0.82rem; font-weight: 600; margin-bottom: 12px; text-align: center; }
  .btn { width: 100%; background: #283b31; color: #f7f3e3; border: none; padding: 12px; font-size: 0.95rem; border-radius: 8px; cursor: pointer; font-weight: 600; }
  .btn:disabled { opacity: 0.55; cursor: not-allowed; }
  .back { display: block; text-align: center; margin-top: 14px; color: #283b31; font-size: 0.84rem; font-weight: 600; text-decoration: none; }
  .back:hover { text-decoration: underline; }
</style>
</head>
<body>
  <div class="card">
    <div class="brand">Firmware Update (OTA)</div>
    <div class="sub">Select a compiled <code>firmware.bin</code> file</div>
    <div id="ota-status" class="status"></div>
    <form id="ota-form" onsubmit="uploadFirmware(event)">
      <div class="file-box">
        <input id="fw-file" type="file" accept=".bin,application/octet-stream" required>
      </div>
      <div id="bar-track" class="bar-track"><div id="bar-fill" class="bar-fill"></div></div>
      <button id="up-btn" class="btn" type="submit">Upload &amp; Flash</button>
    </form>
    <a class="back" href="/">&larr; Back to Dashboard</a>
  </div>
<script>
function setOtaStatus(txt, isErr) {
  const el = document.getElementById('ota-status');
  el.textContent = txt;
  el.style.display = 'block';
  el.style.background = isErr ? '#f8e6e6' : '#e3ece6';
  el.style.color = isErr ? '#b83232' : '#283b31';
  el.style.border = isErr ? '1px solid #dfb0b0' : '1px solid #9eb8a8';
}

function uploadFirmware(e) {
  e.preventDefault();
  const fileInp = document.getElementById('fw-file');
  if (!fileInp.files || !fileInp.files.length) return;
  const btn = document.getElementById('up-btn');
  const track = document.getElementById('bar-track');
  const fill = document.getElementById('bar-fill');
  btn.disabled = true;
  track.style.display = 'block';
  fill.style.width = '0%';
  setOtaStatus('Uploading firmware...', false);

  const formData = new FormData();
  formData.append('update', fileInp.files[0]);

  const xhr = new XMLHttpRequest();
  xhr.open('POST', '/update', true);
  xhr.upload.onprogress = (ev) => {
    if (ev.lengthComputable) {
      const pct = Math.round((ev.loaded / ev.total) * 100);
      fill.style.width = pct + '%';
      setOtaStatus('Flashing: ' + pct + '%', false);
    }
  };
  xhr.onload = () => {
    if (xhr.status === 200 && xhr.responseText.indexOf('OK') === 0) {
      fill.style.width = '100%';
      setOtaStatus('Update complete! Rebooting bridge...', false);
      setTimeout(() => { window.location.href = '/'; }, 4500);
    } else if (xhr.status === 401) {
      window.location.href = '/login';
    } else {
      const detail = (xhr.responseText || '').replace(/^FAIL:\s*/i, '').trim();
      setOtaStatus('Firmware update failed: ' + (detail || ('HTTP ' + xhr.status)), true);
      btn.disabled = false;
    }
  };
  xhr.onerror = () => {
    setOtaStatus('Upload interrupted. Check connection and retry.', true);
    btn.disabled = false;
  };
  xhr.send(formData);
}
</script>
</body>
</html>
)rawliteral";

const char LOGIN_HTML[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Sign In · BLE Dust Bridge</title>
<style>
  * { box-sizing: border-box; }
  body { margin: 0; min-height: 100vh; display: flex; align-items: center; justify-content: center; padding: 16px; background: #283b31; color: #1f2e26; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; }
  .card { width: 100%; max-width: 360px; background: #f7f3e3; border: 1px solid #dfd9c5; border-radius: 14px; padding: 24px 22px; box-shadow: 0 12px 30px rgba(0,0,0,0.28); }
  .brand { font-size: 1.25rem; font-weight: 700; color: #283b31; margin-bottom: 4px; text-align: center; }
  .sub { font-size: 0.82rem; color: #5c6b63; text-align: center; margin-bottom: 20px; }
  .fg { margin-bottom: 14px; }
  .fg label { display: block; font-size: 0.78rem; color: #5c6b63; margin-bottom: 5px; font-weight: 600; }
  .inp { width: 100%; padding: 10px 12px; background: #ffffff; border: 1px solid #dfd9c5; color: #1f2e26; border-radius: 8px; font-size: 0.95rem; outline: none; }
  .inp:focus { border-color: #283b31; box-shadow: 0 0 0 2px #e3ece6; }
  .btn { width: 100%; background: #283b31; color: #f7f3e3; border: none; padding: 12px; font-size: 0.95rem; border-radius: 8px; cursor: pointer; font-weight: 600; margin-top: 4px; }
  .btn:disabled { opacity: 0.55; cursor: not-allowed; }
  .msg { display: none; padding: 9px 11px; border-radius: 8px; font-size: 0.82rem; font-weight: 600; margin-bottom: 14px; background: #f8e6e6; color: #b83232; border: 1px solid #dfb0b0; text-align: center; }
</style>
</head>
<body>
  <div class="card">
    <div class="brand">BLE Dust Bridge</div>
    <div class="sub">Sign in to manage dust extraction</div>
    <div id="login-msg" class="msg"></div>
    <form onsubmit="submitLogin(event)">
      <div class="fg">
        <label for="u">Username</label>
        <input id="u" class="inp" type="text" autocomplete="username" required autofocus>
      </div>
      <div class="fg">
        <label for="p">Password</label>
        <input id="p" class="inp" type="password" autocomplete="current-password" required>
      </div>
      <button id="sub-btn" class="btn" type="submit">Sign In</button>
    </form>
    <div style="margin-top:14px; font-size:0.75rem; color:#5c6b63; text-align:center;">Forgot password? Hold the AtomS3 button for 10s to reset.</div>
  </div>
<script>
function sha256Hex(str) {
  const K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
  ];
  const bytes = new TextEncoder().encode(str);
  const bitLen = bytes.length * 8;
  const padLen = (((bytes.length + 8) >> 6) + 1) << 6;
  const buf = new Uint8Array(padLen);
  buf.set(bytes);
  buf[bytes.length] = 0x80;
  const view = new DataView(buf.buffer);
  view.setUint32(padLen - 8, Math.floor(bitLen / 0x100000000), false);
  view.setUint32(padLen - 4, bitLen >>> 0, false);
  let h0=0x6a09e667, h1=0xbb67ae85, h2=0x3c6ef372, h3=0xa54ff53a;
  let h4=0x510e527f, h5=0x9b05688c, h6=0x1f83d9ab, h7=0x5be0cd19;
  const w = new Uint32Array(64);
  const rrot = (x, n) => (x >>> n) | (x << (32 - n));
  for (let i = 0; i < padLen; i += 64) {
    for (let j = 0; j < 16; j++) w[j] = view.getUint32(i + j * 4, false);
    for (let j = 16; j < 64; j++) {
      const s0 = rrot(w[j-15], 7) ^ rrot(w[j-15], 18) ^ (w[j-15] >>> 3);
      const s1 = rrot(w[j-2], 17) ^ rrot(w[j-2], 19) ^ (w[j-2] >>> 10);
      w[j] = (w[j-16] + s0 + w[j-7] + s1) >>> 0;
    }
    let a=h0, b=h1, c=h2, d=h3, e=h4, f=h5, g=h6, h=h7;
    for (let j = 0; j < 64; j++) {
      const S1 = rrot(e, 6) ^ rrot(e, 11) ^ rrot(e, 25);
      const ch = (e & f) ^ (~e & g);
      const t1 = (h + S1 + ch + K[j] + w[j]) >>> 0;
      const S0 = rrot(a, 2) ^ rrot(a, 13) ^ rrot(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + maj) >>> 0;
      h = g; g = f; f = e; e = (d + t1) >>> 0;
      d = c; c = b; b = a; a = (t1 + t2) >>> 0;
    }
    h0=(h0+a)>>>0; h1=(h1+b)>>>0; h2=(h2+c)>>>0; h3=(h3+d)>>>0;
    h4=(h4+e)>>>0; h5=(h5+f)>>>0; h6=(h6+g)>>>0; h7=(h7+h)>>>0;
  }
  return [h0,h1,h2,h3,h4,h5,h6,h7].map(x => x.toString(16).padStart(8, '0')).join('');
}

function showErr(txt) {
  const m = document.getElementById('login-msg');
  m.textContent = txt;
  m.style.display = 'block';
}

async function submitLogin(e) {
  e.preventDefault();
  const btn = document.getElementById('sub-btn');
  const user = document.getElementById('u').value.trim();
  const pass = document.getElementById('p').value;
  document.getElementById('login-msg').style.display = 'none';
  btn.disabled = true;
  try {
    const chRes = await fetch('/api/auth/challenge?user=' + encodeURIComponent(user));
    if (!chRes.ok) throw new Error('Challenge failed');
    const ch = await chRes.json();
    const credHash = sha256Hex(ch.salt + ':' + user + ':' + pass);
    const proof = sha256Hex(ch.nonce + ':' + credHash);
    const loginRes = await fetch('/api/auth/login', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ user, nonce: ch.nonce, proof })
    });
    if (loginRes.ok) {
      window.location.href = '/';
      return;
    }
    const err = await loginRes.json().catch(() => ({}));
    showErr(err.error || 'Invalid username or password.');
    document.getElementById('p').value = '';
    document.getElementById('p').focus();
  } catch (ex) {
    showErr('Connection error. Please try again.');
  } finally {
    btn.disabled = false;
  }
}
</script>
</body>
</html>
)rawliteral";

volatile bool ledBootMode = true;

void updateStatusLed(unsigned long now) {
    if (ledBootMode) return;
    wifi_mode_t wMode = WiFi.getMode();
    bool blinkOn = ((now / 500UL) % 2) == 0;
    if (connState == STATE_CONNECTED) {
        if (initialTelemDone) {
            setAtomLed(0, 96, 0);
        } else {
            setAtomLed(0, 0, 96);
        }
    } else if (!isExtractorPaired() || wMode == WIFI_AP || wMode == WIFI_AP_STA) {
        setAtomLed(0, blinkOn ? 96 : 0, 0);
    } else {
        setAtomLed(0, 0, blinkOn ? 96 : 0);
    }
}

void setup() {
    logMutex = xSemaphoreCreateMutex();
    ledMutex = xSemaphoreCreateMutex();
    ledBootMode = true;
    setAtomLed(96, 0, 0);
    Serial.begin(115200);
    Serial.setTxTimeoutMs(0);
    while (!Serial && millis() < 600UL) {
        delay(10);
    }
    LOGLN("[BOOT] M5Stack AtomS3 Lite starting...");

    bootAuthSecret = generateRandomHex(16);

    uint64_t chipMac = ESP.getEfuseMac();
    char cidBuf[24];
    snprintf(cidBuf, sizeof(cidBuf), "BLDB_%06X", (uint32_t)(chipMac & 0xFFFFFFULL));
    mqttClientId = String(cidBuf);

    prefs.begin("bldb", false);
    String savedPaired = prefs.isKey("paired_mac") ? prefs.getString("paired_mac", "") : "";
    uint8_t rawSavedType = prefs.isKey("paired_type") ? prefs.getUChar("paired_type", 255) : 255;
    uint8_t savedType = inferRandomAddrType(savedPaired, rawSavedType);
    setPairedMacState(savedPaired, savedType);
    if (pairedMac.length() == 0) {
        LOGLN("[BOOT] No extractor paired -> continuing startup (LED flashes green when ready to configure).");
    }

    extFriendlyName = prefs.isKey("ext_name") ? prefs.getString("ext_name", "Festool Extractor") : "Festool Extractor";
    evacSeconds = prefs.getUChar("evac_sec", 4);
    loadMonitoredFromNvs();
    loadSettingsFromNvs();

    pinMode(BTN_ATOM_GPIO, INPUT_PULLUP);

#if defined(ESP_ARDUINO_VERSION_MAJOR) && ESP_ARDUINO_VERSION_MAJOR >= 3
    espClient.setConnectionTimeout(100);
#endif
    espClient.setTimeout(1);
    mqttClient.setBufferSize(2048);

    WiFi.persistent(false);
    WiFi.mode(WIFI_STA);
    WiFi.disconnect(false, true);
    delay(50);
    WiFi.setSleep(WIFI_PS_NONE);
    WiFi.setHostname(hostname);
    WiFi.setAutoReconnect(false);
    bool connected = false;
    for (size_t wi = 0; wi < wifiList.size(); wi++) {
        const SavedWiFi& w = wifiList[wi];
        if (w.ssid.length() == 0) continue;
        LOGF("[WIFI] Trying (%u/%u): %s...\n", (unsigned)(wi + 1), (unsigned)wifiList.size(), w.ssid.c_str());
        setAtomLed(96, 72, 0);
        WiFi.begin(w.ssid.c_str(), w.pass.c_str());
        int attempts = 0;
        while (WiFi.status() != WL_CONNECTED && attempts < 40) {
            delay(250);
            attempts++;
            bool yellowOn = ((attempts / 2) % 2) == 0;
            setAtomLed(yellowOn ? 96 : 0, yellowOn ? 72 : 0, 0);
        }
        if (WiFi.status() == WL_CONNECTED) {
            connected = true;
            WiFi.setSleep(WIFI_PS_MIN_MODEM);
            LOGF("[WIFI] Connected! IP: %s\n", WiFi.localIP().toString().c_str());
            break;
        }
        WiFi.disconnect(false);
        delay(100);
    }

    if (!connected) {
        WiFi.mode(WIFI_AP_STA);
        WiFi.softAP("BLE_Dust_Bridge");
        LOGLN("[WIFI] Fallback AP 'BLE_Dust_Bridge' started! IP: 192.168.4.1 (continuing background STA retries...)");
    } else {
        if (MDNS.begin(hostname)) LOGLN("[MDNS] Started: http://bldb.local");
        if (mqtt_en && mqtt_ip.length() > 0) mqttClient.setServer(mqtt_ip.c_str(), mqtt_port);
    }
    // ESP32-S3 Wi-Fi/BLE coexistence requires modem sleep enabled before NimBLEDevice::init()
    WiFi.setSleep(WIFI_PS_MIN_MODEM);
    ledBootMode = false;
    updateStatusLed(millis());

    NimBLEDevice::init("BLE-Dust-Bridge");
    esp_coex_preference_set(ESP_COEX_PREFER_BT);
    NimBLEDevice::setSecurityAuth(true, false, true);
    NimBLEDevice::setSecurityIOCap(BLE_HS_IO_NO_INPUT_OUTPUT);
    NimBLEDevice::setOwnAddrType(BLE_OWN_ADDR_PUBLIC);

    LOGF("[BLE] App MAC: %s | Paired Extractor: %s\n",
         NimBLEDevice::getAddress().toString().c_str(),
         pairedMac.length() > 0 ? pairedMac.c_str() : "NONE");

    const char* headerKeys[] = {"Cookie"};
    server.collectHeaders(headerKeys, 1);

    server.on("/favicon.ico", HTTP_GET, []() {
        server.send(204, "image/x-icon", "");
    });

    server.on("/login", HTTP_GET, []() {
        if (!auth_en || isSessionAuthenticated()) {
            server.sendHeader("Location", "/", true);
            server.send(302, "text/plain", "");
            return;
        }
        server.send_P(200, "text/html", LOGIN_HTML);
    });

    server.on("/api/auth/challenge", HTTP_GET, []() {
        unsigned long now = millis();
        String reqUser = server.hasArg("user") ? server.arg("user") : "";
        reqUser.trim();

        String rHex = generateRandomHex(8);
        String tsStr = String(now / 1000UL);
        String sig = sha256Hex(bootAuthSecret + ":" + rHex + ":" + tsStr).substring(0, 32);
        String nonce = rHex + "." + tsStr + "." + sig;

        String saltOut = (reqUser == auth_user && auth_salt.length() == 32)
            ? auth_salt
            : sha256Hex(auth_salt + ":decoy:" + reqUser).substring(0, 32);

        StaticJsonDocument<256> doc;
        doc["nonce"] = nonce;
        doc["salt"] = saltOut;
        String out;
        serializeJson(doc, out);
        server.send(200, "application/json", out);
    });

    server.on("/api/auth/login", HTTP_POST, []() {
        unsigned long now = millis();
        if (lastFailedLoginMs > 0 && elapsedMs(now, lastFailedLoginMs) < 1000UL) {
            server.send(429, "application/json", "{\"error\":\"Please wait a moment before retrying.\"}");
            return;
        }
        if (!server.hasArg("plain")) {
            server.send(400, "application/json", "{\"error\":\"Invalid request.\"}");
            return;
        }
        StaticJsonDocument<384> doc;
        if (deserializeJson(doc, server.arg("plain")) != DeserializationError::Ok) {
            server.send(400, "application/json", "{\"error\":\"Invalid JSON.\"}");
            return;
        }
        String u = doc["user"] | "";
        u.trim();
        String nonce = doc["nonce"] | "";
        String proof = doc["proof"] | "";

        if (!verifyAndConsumeSignedNonce(nonce, now)) {
            lastFailedLoginMs = now;
            server.send(401, "application/json", "{\"error\":\"Login challenge expired. Please try again.\"}");
            return;
        }

        String expectedProof = sha256Hex(nonce + ":" + auth_hash);
        if (u == auth_user && constantTimeHexEquals(proof, expectedProof)) {
            String sid = generateRandomHex(16);
            size_t sessIdx = MAX_AUTH_SESSIONS;
            size_t oldestIdx = 0;
            unsigned long oldestTs = ULONG_MAX;
            for (size_t i = 0; i < MAX_AUTH_SESSIONS; i++) {
                if (!authSessions[i].active || elapsedMs(now, authSessions[i].lastSeenMs) > AUTH_SESSION_TTL_MS) {
                    sessIdx = i;
                    break;
                }
                if (authSessions[i].lastSeenMs < oldestTs) {
                    oldestTs = authSessions[i].lastSeenMs;
                    oldestIdx = i;
                }
            }
            if (sessIdx >= MAX_AUTH_SESSIONS) sessIdx = oldestIdx;
            AuthSession& s = authSessions[sessIdx];
            strncpy(s.token, sid.c_str(), sizeof(s.token) - 1);
            s.token[sizeof(s.token) - 1] = '\0';
            s.lastSeenMs = now;
            s.active = true;
            lastFailedLoginMs = 0;

            server.sendHeader("Set-Cookie", "bldb_sid=" + sid + "; Path=/; HttpOnly; SameSite=Strict; Max-Age=86400");
            server.send(200, "application/json", "{\"ok\":true}");
            LOGF("[AUTH] Web UI login succeeded for user '%s'\n", u.c_str());
        } else {
            lastFailedLoginMs = now;
            server.send(401, "application/json", "{\"error\":\"Invalid username or password.\"}");
            LOGF("[AUTH] Failed Web UI login attempt for user '%s'\n", u.c_str());
        }
    });

    server.on("/api/auth/logout", HTTP_POST, []() {
        String tok = extractSessionCookie();
        if (tok.length() == 32) {
            for (size_t i = 0; i < MAX_AUTH_SESSIONS; i++) {
                if (authSessions[i].active && constantTimeHexEquals(tok, String(authSessions[i].token))) {
                    authSessions[i].active = false;
                }
            }
        }
        server.sendHeader("Set-Cookie", "bldb_sid=; Path=/; HttpOnly; SameSite=Strict; Max-Age=0");
        server.send(200, "application/json", "{\"ok\":true}");
    });

    server.on("/", []() { if (!checkAuth(false)) return; server.send_P(200, "text/html", INDEX_HTML); });
    server.on("/api/identify", []() { if (!checkAuth(true)) return; sendFmpIdentify(true); server.send(200, "application/json", "{}"); });
    server.on("/api/telem/refresh", []() { if (!checkAuth(true)) return; startTelemetryPoll(true); sendJsonStatus(); });

    server.on("/api/evac", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("sec")) {
            int s = server.arg("sec").toInt();
            evacSeconds = (uint8_t)(s < 0 ? 0 : (s > 60 ? 60 : s));
            prefs.putUChar("evac_sec", evacSeconds);
            mqttTelemDirty = true;
            LOGF("[EXTRACT] Debris evacuation set to %us\n", evacSeconds);
        }
        sendJsonStatus();
    });

    server.on("/api/status", []() { if (!checkAuth(true)) return; sendJsonStatus(); });

    server.on("/api/settings", HTTP_GET, []() {
        if (!checkAuth(true)) return;
        DynamicJsonDocument doc(2048);
        JsonArray wifis = doc.createNestedArray("wifis");
        for (const auto& w : wifiList) {
            JsonObject obj = wifis.createNestedObject();
            obj["ssid"] = w.ssid; obj["pass"] = w.pass.length() > 0 ? "********" : "";
        }
        doc["mqtt_en"] = mqtt_en; doc["mqtt_ip"] = mqtt_ip; doc["mqtt_port"] = mqtt_port;
        doc["mqtt_user"] = mqtt_user; doc["mqtt_pass"] = mqtt_pass.length() > 0 ? "********" : "";
        doc["auth_en"] = auth_en; doc["auth_user"] = auth_user;
        String out; serializeJson(doc, out);
        server.send(200, "application/json", out);
    });

    server.on("/api/wifi/reorder", HTTP_POST, []() {
        if (!checkAuth(true)) return;
        if (!server.hasArg("plain")) {
            server.send(400, "text/plain", "Bad Request");
            return;
        }
        DynamicJsonDocument doc(2048);
        if (deserializeJson(doc, server.arg("plain")) != DeserializationError::Ok || !doc["wifis"].is<JsonArray>()) {
            server.send(400, "text/plain", "Invalid JSON");
            return;
        }
        std::vector<SavedWiFi> prevWifis = wifiList;
        std::vector<SavedWiFi> reordered;
        JsonArray wifis = doc["wifis"].as<JsonArray>();
        for (JsonObject w : wifis) {
            String ssid = w["ssid"].as<String>();
            if (ssid.length() == 0) continue;
            String pass = "";
            for (const auto& oldW : prevWifis) {
                if (oldW.ssid.equalsIgnoreCase(ssid)) {
                    pass = oldW.pass;
                    break;
                }
            }
            reordered.push_back({ssid, pass});
        }
        if (!reordered.empty()) {
            wifiList = reordered;
            bgWifiIdx = 0;
            saveWifiListToNvs();
            String orderLog = "";
            for (size_t i = 0; i < wifiList.size(); i++) {
                if (i > 0) orderLog += " -> ";
                orderLog += wifiList[i].ssid;
            }
            LOGF("[WIFI] Priority order saved: %s\n", orderLog.c_str());
        }
        server.send(200, "application/json", "{\"ok\":true}");
    });

    server.on("/api/settings/save", HTTP_POST, []() {
        if (!checkAuth(true)) return;
        if (!server.hasArg("plain")) {
            server.send(400, "application/json", "{\"error\":\"Missing request payload.\"}");
            return;
        }
        DynamicJsonDocument doc(2048);
        if (deserializeJson(doc, server.arg("plain")) != DeserializationError::Ok || !doc.is<JsonObject>()) {
            server.send(400, "application/json", "{\"error\":\"Invalid JSON payload.\"}");
            return;
        }

        bool nextAuthEn = doc["auth_en"] | auth_en;
        String nextAuthUser = doc.containsKey("auth_user") ? doc["auth_user"].as<String>() : auth_user;
        nextAuthUser.trim();
        String nextAuthPass = doc.containsKey("auth_pass") ? doc["auth_pass"].as<String>() : "";

        if (nextAuthEn) {
            if (nextAuthUser.length() == 0) {
                server.send(400, "application/json", "{\"error\":\"Username cannot be empty.\"}");
                return;
            }
            if (nextAuthUser != auth_user && nextAuthPass.length() == 0) {
                server.send(400, "application/json", "{\"error\":\"Enter a password when changing username.\"}");
                return;
            }
            if (nextAuthPass.length() == 0 && (auth_salt.length() != 32 || auth_hash.length() != 64)) {
                server.send(400, "application/json", "{\"error\":\"Password is required to enable login.\"}");
                return;
            }
        }

        if (doc["wifis"].is<JsonArray>()) {
            std::vector<SavedWiFi> prevWifis = wifiList;
            wifiList.clear();

            JsonArray wifis = doc["wifis"].as<JsonArray>();
            for (JsonObject w : wifis) {
                String ssid = w["ssid"].as<String>();
                if (ssid.length() == 0) continue;
                String pass = w["pass"].as<String>();
                if (pass == "********") {
                    pass = "";
                    for (const auto& oldW : prevWifis) if (oldW.ssid.equalsIgnoreCase(ssid)) { pass = oldW.pass; break; }
                }
                wifiList.push_back({ssid, pass});
            }
            saveWifiListToNvs();
        }

        mqtt_en = doc["mqtt_en"] | mqtt_en;
        if (doc.containsKey("mqtt_ip")) mqtt_ip = doc["mqtt_ip"].as<String>();
        if (doc.containsKey("mqtt_port")) {
            int p = doc["mqtt_port"] | 1883;
            if (p <= 0 || p > 65535) p = 1883;
            mqtt_port = p;
        }
        if (doc.containsKey("mqtt_user")) mqtt_user = doc["mqtt_user"].as<String>();
        if (doc.containsKey("mqtt_pass")) {
            String inMqttPass = doc["mqtt_pass"].as<String>();
            if (inMqttPass != "********") mqtt_pass = inMqttPass;
        }
        prefs.putBool("mqtt_en", mqtt_en); prefs.putString("mqtt_ip", mqtt_ip); prefs.putInt("mqtt_port", mqtt_port);
        prefs.putString("mqtt_user", mqtt_user); prefs.putString("mqtt_pass", mqtt_pass);

        auth_en = nextAuthEn;
        if (nextAuthUser.length() > 0) auth_user = nextAuthUser;
        if (nextAuthPass.length() > 0) {
            auth_salt = generateRandomHex(16);
            auth_hash = sha256Hex(auth_salt + ":" + auth_user + ":" + nextAuthPass);
            clearAllAuthSessions();
        } else if (!auth_en) {
            clearAllAuthSessions();
        }
        prefs.putBool("auth_init", true);
        prefs.putBool("auth_en", auth_en);
        prefs.putString("auth_user", auth_user);
        prefs.putString("auth_salt", auth_salt);
        prefs.putString("auth_hash", auth_hash);

        server.send(200, "application/json", "{}");
        if (currentPowerState == 1) {
            stopExtractorMotor(true);
        }
        requestReboot = true; rebootTimer = millis();
    });

    server.on("/api/wifi/scan", []() {
        if (!checkAuth(true)) return;
        if (extConnTaskRunning.load() || gattBtnTaskRunning.load() || connState == STATE_CONNECTING) {
            server.send(409, "application/json", "{\"error\":\"BLE connection in progress, retry in a moment\"}");
            return;
        }
        wifiScanInProgress = true;
        NimBLEDevice::getScan()->stop();
        if (WiFi.status() != WL_CONNECTED) {
            WiFi.disconnect(false);
        }
        delay(20);
        int n = WiFi.scanNetworks(false, true);
        if (n == -1) {
            delay(250);
            n = WiFi.scanNetworks(false, true);
        }
        unsigned long scanStart = millis();
        while (WiFi.scanComplete() == WIFI_SCAN_RUNNING && elapsedMs(millis(), scanStart) < 4000UL) {
            unsigned long tNow = millis();
            if (extConnTaskDone.exchange(false)) finishBleConnect(tNow);
            if (gattBtnTaskDone.exchange(false)) finishGattButtonConnect(tNow);
            drainScanEvents(tNow);
            serviceGattButton(tNow);
            serviceButtonGestures(tNow);
            if (hoseClearActive && (elapsedMs(tNow, hoseClearTimer) >= (unsigned long)evacSeconds * 1000UL)) {
                LOGLN("[DEBRIS EVAC] Evacuation complete -> Motor OFF");
                hoseClearActive = false;
                forceStopNow = true;
                demandDirty = true;
            }
            if (demandDirty) { demandDirty = false; evaluateMotorDemand(); }
            delay(15);
        }
        int n = WiFi.scanComplete();
        struct ScanNet { String ssid; int rssi; };
        std::vector<ScanNet> uniqueNets;
        for (int i = 0; i < n; i++) {
            String ssid = WiFi.SSID(i);
            if (ssid.length() == 0) continue;
            int rssi = WiFi.RSSI(i);
            bool found = false;
            for (auto& u : uniqueNets) {
                if (u.ssid == ssid) {
                    if (rssi > u.rssi) u.rssi = rssi;
                    found = true;
                    break;
                }
            }
            if (!found) uniqueNets.push_back({ssid, rssi});
        }
        DynamicJsonDocument doc(2048);
        JsonArray arr = doc.to<JsonArray>();
        for (const auto& u : uniqueNets) {
            JsonObject obj = arr.createNestedObject();
            obj["ssid"] = u.ssid;
            obj["rssi"] = u.rssi;
        }
        String out; serializeJson(doc, out);
        server.send(200, "application/json", out);
        WiFi.scanDelete();
        wifiScanInProgress = false;
        setCoexScanner();
    });

    server.on("/api/control", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("power") && server.arg("power").toInt() != 1) {
            LOGLN("[WEB UI] Master OFF requested");
            webUiDemandActive = false; webUiSpeedOverride = 0; clearAllButtonToggles();
            toolBattDemandActive = false; activeToolBattMac = "";
            hoseClearActive = false; forceStopNow = true;
            for (auto& m : monitoredList) { m.toolActive = false; m.liveSpeedOverride = 0; }
            evaluateMotorDemand();
            sendJsonStatus();
            return;
        }
        if (pairedMac.length() == 0 || connState != STATE_CONNECTED) { sendJsonStatus(); return; }
        bool hasSpeedArg = server.hasArg("speed");
        if (hasSpeedArg) {
            userManualSpeed = quantizeSpeed((uint8_t)server.arg("speed").toInt());
            bool otherDemandActive = (hoseMomentaryActive || hoseToggleDemandActive || btnToggleDemandActive || toolBattDemandActive);
            if (!webUiDemandActive && otherDemandActive) {
                setActiveLiveSpeedOverride(userManualSpeed);
                evaluateMotorDemand();
                sendJsonStatus();
                return;
            }
            webUiSpeedOverride = 0;
            if (webUiDemandActive || currentPowerState == 1) {
                evaluateMotorDemand();
            }
        }
        if (server.hasArg("power") && server.arg("power").toInt() == 1) {
            LOGF("[WEB UI] Start requested -> %u%%\n", userManualSpeed);
            webUiDemandActive = true; hoseClearActive = false; webUiSpeedOverride = 0;
            evaluateMotorDemand();
        }
        sendJsonStatus();
    });
    server.on("/api/pair", []() {
        if (!checkAuth(true)) return;
        extUnpairPending.store(false);
        lastExtConnectFailMs = 0;
        targetConnectMac = server.arg("mac");
        targetConnectType = 255;
        requestConnect = true;
        sendJsonStatus();
    });

    server.on("/api/forget", []() {
        if (!checkAuth(true)) return;
        requestConnect = false;
        targetConnectMac = "";
        postConnectActionPending = false;
        lastExtConnectFailMs = 0;
        if (extConnTaskRunning.load()) {
            extUnpairPending.store(true);
        } else {
            extUnpairPending.store(false);
            if (pClient && pClient->isConnected()) pClient->disconnect();
        }
        setPairedMacState("", 0);
        pairedLastSeenMs = 0; pairedRssi = 0; lastAutoReconnectTryMs = 0; initialTelemDone = false;
        resetExtractorTelemetry();
        prefs.remove("paired_mac"); prefs.remove("paired_type");
        mqttTelemDirty = true;
        updateStatusLed(millis());
        if (!extConnTaskRunning.load()) setCoexScanner();
        sendJsonStatus();
    });

    server.on("/api/rename_ext", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("name")) {
            extFriendlyName = server.arg("name");
            prefs.putString("ext_name", extFriendlyName);
            mqttTelemDirty = true;
        }
        sendJsonStatus();
    });

    server.on("/api/monitored/rename", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("mac") && server.hasArg("name")) {
            String m = server.arg("mac"), n = server.arg("name");
            for (auto& i : monitoredList) if (i.address.equalsIgnoreCase(m)) { i.name = n; i.customNamed = true; break; }
            saveMonitoredToNvs();
        }
        sendJsonStatus();
    });

    server.on("/api/monitored/update", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("mac")) {
            String m = server.arg("mac");
            for (auto& i : monitoredList) {
                if (i.address.equalsIgnoreCase(m)) {
                    if (server.hasArg("speed")) {
                        uint8_t newSpd = quantizeSpeed((uint8_t)server.arg("speed").toInt());
                        i.speed = newSpd;
                        if (i.momActive) i.momSpeed = newSpd;
                        i.liveSpeedOverride = 0;
                        if (i.toggleActive || i.momActive || i.toolActive) {
                            syncButtonDemandsFromMonitored();
                            syncToolBattDemandFromMonitored(millis());
                            demandDirty = true;
                        }
                    }
                    if (server.hasArg("wattsThr")) {
                        int wt = server.arg("wattsThr").toInt();
                        if (wt < 5) wt = 5;
                        if (wt > 500) wt = 500;
                        i.wattsThr = (uint16_t)wt;
                    }
                    break;
                }
            }
            saveMonitoredToNvs();
        }
        sendJsonStatus();
    });

    server.on("/api/monitored/hose", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("mac")) {
            String m = server.arg("mac");
            bool nextHose = server.hasArg("hose") && (server.arg("hose").toInt() == 1);
            uint8_t aType = 255, bType = 1, spd = 20;
            bool shouldConnectGatt = false;
            bool shouldDisconnectGatt = false;
            for (const auto& b : bleList) {
                if (b.address.equalsIgnoreCase(m)) { aType = b.addrType; break; }
            }
            for (auto& i : monitoredList) {
                if (i.address.equalsIgnoreCase(m)) {
                    if (aType == 255 && (i.addrType == 0 || i.addrType == 1)) aType = i.addrType;
                    else if (aType == 0 || aType == 1) i.addrType = aType;
                    if (i.btnType > 0) {
                        if (nextHose && !i.canGatt) {
                            LOGF("[PRIMARY ROLE] %s does not support GATT Primary mode; ignoring.\n", m.c_str());
                            break;
                        }
                        i.isHose = nextHose;
                        i.waitReleaseAfterPair = false;
                        i.pairHoldGuardUntilMs = 0;
                        if (nextHose) {
                            i.isGatt = true;
                            if (i.canAdv) i.periodicBeacon = false;
                            i.activeRaw = "GATT:FFE0/HID";
                            i.gattReady = i.gattReady || isGattMacConnectedOrBusy(m);
                            shouldConnectGatt = !i.gattReady;
                            bType = i.btnType;
                            spd = i.speed;
                            if (i.gattReady) {
                                LOGF("[PRIMARY ROLE] %s -> Primary Switch ON (already paired & ready)\n", m.c_str());
                            } else {
                                LOGF("[PRIMARY ROLE] %s -> Primary Switch ON (press and hold button to pair GATT)\n", m.c_str());
                            }
                        } else {
                            if (i.canAdv) {
                                i.isGatt = false;
                                i.gattReady = true;
                                i.activeRaw = "ADV:STREAM";
                                shouldDisconnectGatt = true;
                                LOGF("[PRIMARY ROLE] %s -> Primary Switch OFF (returned to passive ADV)\n", m.c_str());
                            } else {
                                i.gattReady = i.gattReady || isGattMacConnectedOrBusy(m);
                                LOGF("[PRIMARY ROLE] %s -> Primary Switch OFF (GATT Tool Switch)\n", m.c_str());
                            }
                        }
                        resetMonitoredButtonGesture(i, true);
                    }
                    break;
                }
            }
            saveMonitoredToNvs();
            if (shouldDisconnectGatt) disconnectGattButtonMac(m);
            else if (shouldConnectGatt) enqueueGattConnect(m, aType, bType, spd, true);
            syncButtonDemandsFromMonitored();
            demandDirty = true;
        }
        sendJsonStatus();
    });

    server.on("/api/monitored/add", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("mac")) {
            String mac = server.arg("mac");
            String name = server.arg("name") ? server.arg("name") : "Device";
            int speed = server.hasArg("speed") ? server.arg("speed").toInt() : 20;
            uint8_t btnType = server.hasArg("btnType") ? server.arg("btnType").toInt() : 0;
            if (btnType > 0) btnType = 1;
            String raw = server.hasArg("raw") ? server.arg("raw") : "";
            int rssi = server.hasArg("rssi") ? server.arg("rssi").toInt() : 0;
            uint8_t addrType = server.hasArg("addrType") ? (uint8_t)server.arg("addrType").toInt() : 255;
            bool argCanAdv = server.hasArg("canAdv") && (server.arg("canAdv").toInt() == 1);
            bool argCanGatt = server.hasArg("canGatt") && (server.arg("canGatt").toInt() == 1);

            unsigned long now = millis();
            String initAdvName = "";
            uint32_t initMatNum = 0;
            uint8_t initDevCat = (btnType > 0) ? CAT_BUTTON : CAT_OTHER;
            bool bleCanAdv = false;
            bool bleCanGatt = false;
            bool bleGattConfirmed = false;
            for (const auto& b : bleList) {
                if (b.address.equalsIgnoreCase(mac)) {
                    addrType = b.addrType;
                    if (b.advName.length() > 0) initAdvName = b.advName;
                    if (b.matNum > 0) initMatNum = b.matNum;
                    bleCanAdv = b.canAdv;
                    bleCanGatt = b.canGatt;
                    bleGattConfirmed = (!b.canAdv && (b.rawData.startsWith("GATT") || b.slowCadenceHits >= 1));
                    if (b.type == "Battery") initDevCat = CAT_BATTERY;
                    else if (b.type == "Tool Plug") initDevCat = CAT_TOOL_PLUG;
                    else if (b.type == "Button") initDevCat = CAT_BUTTON;
                    break;
                }
            }
            String upName = name; upName.toUpperCase();
            String upAdvName = initAdvName; upAdvName.toUpperCase();
            bool isLegacyRemote = (raw == "ADV:FESTOOL_REMOTE" || initMatNum == 202097 || initMatNum == 204842 ||
                                   initMatNum == 10029918 || initMatNum == 10030046 ||
                                   upName.indexOf("CT-F") >= 0 || upName.indexOf("CTF") >= 0 ||
                                   upAdvName.indexOf("CT-F") >= 0 || upAdvName.indexOf("CTF") >= 0);
            if (isLegacyRemote) {
                initDevCat = CAT_BUTTON;
            }
            if (initAdvName.length() == 0 && name != "Device" && name != "Festool Battery" && name != "Shelly Tool Plug" && name != "Auto Tool") {
                initAdvName = name;
            }

            bool canAdvInit = false;
            bool canGattInit = false;
            bool isGattInit = false;
            if (btnType > 0) {
                canAdvInit = bleCanAdv || argCanAdv || isLegacyRemote || raw.startsWith("ADV");
                canGattInit = isLegacyRemote ? false : (bleCanGatt || argCanGatt || raw.startsWith("GATT"));
                // Passive-first: default to passive ADV whenever supported; use GATT only when GATT-required
                if (canAdvInit) {
                    isGattInit = false;
                    raw = "ADV:STREAM";
                } else if (raw.startsWith("GATT") || bleGattConfirmed || (canGattInit && !canAdvInit)) {
                    isGattInit = true;
                    canGattInit = true;
                    raw = "GATT:FFE0/HID";
                }
            }
            bool alreadyConnGatt = isGattInit && isGattMacConnectedOrBusy(mac);

            if (findMonitoredByMac(mac) == nullptr) {
                bool gReady = (!isGattInit) || alreadyConnGatt;
                uint8_t resolvedAddrType = inferRandomAddrType(mac, addrType);
                monitoredList.push_back({mac, name, initAdvName, (uint8_t)speed, btnType, raw, false, false, 0, isGattInit, gReady, false, 0, false, canAdvInit, initMatNum, initDevCat, 60, -1, canGattInit, resolvedAddrType});
            }
            saveMonitoredToNvs();
            if (isGattInit && !alreadyConnGatt) enqueueGattConnect(mac, inferRandomAddrType(mac, addrType), btnType, (uint8_t)speed, true);

            bool inBle = false;
            for (auto& b : bleList) {
                if (b.address.equalsIgnoreCase(mac)) {
                    if (rssi < 0) b.rssi = rssi;
                    if (addrType == 0 || addrType == 1) b.addrType = addrType;
                    if (canAdvInit) b.canAdv = true;
                    if (canGattInit) b.canGatt = true;
                    if (raw.length() > 0) b.rawData = raw;
                    inBle = true;
                    break;
                }
            }
            if (!inBle) {
                bleList.push_back({name, initAdvName, mac, addrType, rssi, true, devCatToTypeStr(initDevCat), now, -1, 0, initMatNum, -1, raw, canAdvInit, canGattInit, 0, 0, 0, 0});
            }
        }
        sendJsonStatus();
    });

    server.on("/api/monitored/delete", []() {
        if (!checkAuth(true)) return;
        if (server.hasArg("mac")) {
            String mac = server.arg("mac");
            disconnectGattButtonMac(mac);
            for (auto it = monitoredList.begin(); it != monitoredList.end(); ) {
                if (it->address.equalsIgnoreCase(mac)) it = monitoredList.erase(it);
                else ++it;
            }
            saveMonitoredToNvs();
            syncButtonDemandsFromMonitored();
            syncToolBattDemandFromMonitored(millis());
            if (!isAnyPrimaryDemandActive() && currentPowerState == 1 && !hoseClearActive) {
                if (evacSeconds > 0) { hoseClearActive = true; hoseClearTimer = millis(); }
                else forceStopNow = true;
            }
            demandDirty = true;
        }
        sendJsonStatus();
    });

    server.on("/update", HTTP_GET, []() { if (!checkAuth(false)) return; server.send_P(200, "text/html", OTA_HTML); });
    server.on("/update", HTTP_POST, []() {
        if (!checkAuth(true)) return;
        bool otaOk = !Update.hasError() && Update.isFinished();
        server.sendHeader("Connection", "close");
        if (otaOk) {
            server.send(200, "text/plain", "OK - Rebooting...");
            requestReboot = true;
            rebootTimer = millis();
        } else {
            String errStr = Update.errorString();
            if (errStr.length() == 0) errStr = "Update failed";
            server.send(500, "text/plain", "FAIL: " + errStr);
            setCoexScanner();
        }
    }, []() {
        HTTPUpload& upload = server.upload();
        if (!isSessionAuthenticated()) {
            if (upload.status == UPLOAD_FILE_START) {
                server.sendHeader("Connection", "close");
                server.send(401, "text/plain", "Unauthorized");
                server.client().stop();
            }
            return;
        }
        if (upload.status == UPLOAD_FILE_START) {
            NimBLEDevice::getScan()->stop();
            if (!Update.begin(UPDATE_SIZE_UNKNOWN)) {
                LOGF("[OTA] Update.begin failed: %s\n", Update.errorString());
            }
        } else if (upload.status == UPLOAD_FILE_WRITE) {
            if (Update.isRunning()) {
                if (Update.write(upload.buf, upload.currentSize) != upload.currentSize) {
                    LOGF("[OTA] Update.write failed: %s\n", Update.errorString());
                    Update.abort();
                }
            }
        } else if (upload.status == UPLOAD_FILE_END) {
            if (Update.isRunning()) {
                if (!Update.end(true)) {
                    LOGF("[OTA] Update.end failed: %s\n", Update.errorString());
                }
            }
        } else if (upload.status == UPLOAD_FILE_ABORTED) {
            LOGLN("[OTA] Upload aborted by client; restoring BLE scanner.");
            if (Update.isRunning()) {
                Update.abort();
            }
            setCoexScanner();
        }
    });

    server.onNotFound([]() {
        wifi_mode_t wMode = WiFi.getMode();
        if (wMode == WIFI_AP || wMode == WIFI_AP_STA) {
            server.sendHeader("Location", "http://192.168.4.1/", true);
            server.send(302, "text/plain", "");
        } else {
            server.send(404, "text/plain", "Not Found");
        }
    });

    server.begin();

    NimBLEScan* pScan = NimBLEDevice::getScan();
    pScan->setScanCallbacks(new ScanCallbacks(), true);
    scannerStartedMs = millis();
    setCoexScanner();
    LOGLN("[BLE] Continuous scanner started");
}

void loop() {
    unsigned long now = millis();
    static unsigned long lastLedTickMs = 0;
    if (elapsedMs(now, lastLedTickMs) >= 100UL) {
        lastLedTickMs = now;
        updateStatusLed(now);
    }
    server.handleClient();
    serviceSerialAndImprov(now);

    if (requestReboot && elapsedMs(now, rebootTimer) >= 600UL) {
        delay(100);
        ESP.restart();
    }
    if (extLinkConnectedLog.exchange(false)) {
        LOGLN("[BLE] Link connected -> securing bond & discovering GATT...");
    }
    if (extLinkDisconnectedFlag.exchange(false)) {
        mqttTelemDirty = true;
        LOGLN("[BLE] Extractor link disconnected.");
        setCoexScanner();
    }
    if (externalShutoffPending) {
        externalShutoffPending = false;
        if (isAnyPrimaryDemandActive() || hoseClearActive) {
            webUiDemandActive = false;
            webUiSpeedOverride = 0;
            clearAllButtonToggles();
            for (auto& m : monitoredList) {
                if (m.btnType == 0) {
                    m.toolActive = false;
                    m.liveSpeedOverride = 0;
                }
            }
            toolBattDemandActive = false;
            activeToolBattMac = "";
            hoseClearActive = false;
            mqttDevicesDirty = true;
            LOGLN("[EXTRACT] External/cutout shutoff event -> cleared all active demands.");
        }
    }
    if (mqttVacStateDirty || mqttVacSpeedDirty || mqttTelemDirty) {
        mqttVacStateDirty = false;
        mqttVacSpeedDirty = false;
        mqttTelemDirty = false;
        publishExtractorTelemetry(now);
    }
    if (mqttDevicesDirty) {
        mqttDevicesDirty = false;
        publishDevicesTelemetry(now);
    }
    if (extConnTaskDone.exchange(false)) {
        finishBleConnect(now);
    }
    if (postConnectActionPending && now >= postConnectActionAtMs) {
        postConnectActionPending = false;
        if (connState == STATE_CONNECTED) {
            if (isAnyPrimaryDemandActive() || hoseClearActive) evaluateMotorDemand();
            else sendFmpHandshake();
        }
    }
    if (connState == STATE_DISCONNECTED && !requestConnect && !extConnTaskRunning.load() && pairedMac.length() > 0 && pairedAdvSeenFlag.exchange(false)) {
        if (lastExtConnectFailMs == 0 || elapsedMs(now, lastExtConnectFailMs) >= 4000UL) {
            targetConnectMac = pairedMac;
            targetConnectType = pairedAddrType;
            requestConnect = true;
        }
    }

    if (requestConnect && !extConnTaskRunning.load() && !gattBtnTaskRunning.load()) {
        requestConnect = false;
        startBleConnect(targetConnectMac, targetConnectType);
    }
    drainScanEvents(now);
    if (needSaveMonitored && elapsedMs(now, needSaveMonitoredAtMs) >= 10000UL) {
        needSaveMonitored = false;
        needSaveMonitoredAtMs = 0;
        saveMonitoredToNvs();
    }

    static unsigned long lastBlePruneMs = 0;
    if (elapsedMs(now, lastBlePruneMs) >= 30000UL) {
        lastBlePruneMs = now;
        pruneStaleBleEntries(now);
    }

    serviceGattButton(now);
    serviceButtonGestures(now);

    static unsigned long lastToolWatchdogMs = 0;
    if (toolBattDemandActive && (elapsedMs(now, lastToolWatchdogMs) >= 250UL)) {
        lastToolWatchdogMs = now;
        for (auto& m : monitoredList) {
            if (m.btnType == 0 && m.toolActive && elapsedMs(now, m.toolLastSeen) >= 8000UL) {
                m.toolActive = false;
                m.liveSpeedOverride = 0;
            }
        }
        syncToolBattDemandFromMonitored(now);
        if (!toolBattDemandActive) {
            if (!isAnyPrimaryDemandActive()) {
                if (evacSeconds > 0) { LOGF("[TOOL WATCHDOG] Signal lost -> %us debris evacuation at 20%%\n", evacSeconds); hoseClearActive = true; hoseClearTimer = now; }
                else { LOGLN("[TOOL WATCHDOG] Signal lost -> Motor OFF"); forceStopNow = true; }
            }
            demandDirty = true;
        }
    }

    if (demandDirty) { demandDirty = false; evaluateMotorDemand(); }

    bool extRecentlySeen = (pairedLastSeenMs > 0 && elapsedMs(now, pairedLastSeenMs) < 30000UL);
    bool bootGrace = (scannerStartedMs > 0 && elapsedMs(now, scannerStartedMs) >= 1500UL && elapsedMs(now, scannerStartedMs) < 5000UL);
    if (pairedMac.length() > 0 && connState == STATE_DISCONNECTED && !requestConnect && !extConnTaskRunning.load() && (extRecentlySeen || bootGrace) &&
        (lastAutoReconnectTryMs == 0 || elapsedMs(now, lastAutoReconnectTryMs) >= 15000UL)) {
        lastAutoReconnectTryMs = now;
        LOGLN("[BLE] Maintaining GATT link -> connecting to paired extractor...");
        targetConnectMac = pairedMac; targetConnectType = pairedAddrType; requestConnect = true;
    }

    bool quietForDiag = !isAnyPrimaryDemandActive() && !hoseClearActive && !demandDirty && !isAnyButtonGestureBusy() &&
                        (elapsedMs(now, connectedAtMs) >= 6500UL) && (elapsedMs(now, lastControlTxMs) >= 3000UL) && (elapsedMs(now, lastBleActivityMs) >= 2500UL);
    if (connState == STATE_CONNECTED && !initialTelemDone && !telemPollRequested && quietForDiag) {
        initialTelemDone = true;
        updateStatusLed(now);
        LOGLN("[FMP TELEM] Link settled -> starting gentle background diagnostics...");
        startTelemetryPoll(true);
    }
    serviceTelemetryPoll(now);
    if (identifyActive && (elapsedMs(now, identifyStartMs) >= 10000UL)) sendFmpIdentify(false);

    if (mqtt_en && WiFi.status() == WL_CONNECTED) {
        if (!mqttClient.connected() && !isAnyButtonGestureBusy() && (elapsedMs(now, lastMqttReconnect) > 5000UL)) {
            lastMqttReconnect = now;
            bool ok = (mqtt_user.length() > 0)
                ? mqttClient.connect(mqttClientId.c_str(), mqtt_user.c_str(), mqtt_pass.c_str(), "BLE_DB/bridge/status", 0, true, "offline")
                : mqttClient.connect(mqttClientId.c_str(), nullptr, nullptr, "BLE_DB/bridge/status", 0, true, "offline");
            if (ok) {
                publishAllMqttTelemetry(now);
            }
        }
        if (mqttClient.connected()) {
            mqttClient.loop();
            if (elapsedMs(now, lastMqttHeartbeatMs) >= 10000UL) {
                publishAllMqttTelemetry(now);
            }
        }
    }

    static bool bgStaPromoted = false;
    static unsigned long lastBgWifiTryMs = 0;
    if (WiFi.status() == WL_CONNECTED) {
        if (!bgStaPromoted && WiFi.getMode() == WIFI_AP_STA) {
            bgStaPromoted = true;
            WiFi.softAPdisconnect(true);
            WiFi.mode(WIFI_STA);
            LOGF("[WIFI] Background STA connected! IP: %s\n", WiFi.localIP().toString().c_str());
            if (MDNS.begin(hostname)) LOGLN("[MDNS] Started: http://bldb.local");
            if (mqtt_en && mqtt_ip.length() > 0) mqttClient.setServer(mqtt_ip.c_str(), mqtt_port);
        }
    } else if (!wifiList.empty() && !wifiScanInProgress && !improvProvPending && !extConnTaskRunning.load() && !gattBtnTaskRunning.load() &&
               connState != STATE_CONNECTING &&
               (lastBgWifiTryMs == 0 || elapsedMs(now, lastBgWifiTryMs) >= 15000UL)) {
        lastBgWifiTryMs = now;
        const SavedWiFi& w = wifiList[bgWifiIdx % wifiList.size()];
        bgWifiIdx++;
        if (w.ssid.length() > 0) {
            WiFi.disconnect(false);
            LOGF("[WIFI] Background retry: %s...\n", w.ssid.c_str());
            WiFi.begin(w.ssid.c_str(), w.pass.c_str());
        }
    }

    // M5Stack AtomS3 Lite single front button (GPIO 41): 10s hold = factory reset
    bool btnAtomLow = (digitalRead(BTN_ATOM_GPIO) == LOW);
    static bool prevAtomLow = false;
    static unsigned long atomPressStartMs = 0;
    if (btnAtomLow) {
        if (!prevAtomLow) atomPressStartMs = now;
        else if (atomPressStartMs > 0 && elapsedMs(now, atomPressStartMs) > 10000UL) { prefs.clear(); delay(500); ESP.restart(); }
    } else {
        atomPressStartMs = 0;
    }
    prevAtomLow = btnAtomLow;

    if (hoseClearActive && (elapsedMs(now, hoseClearTimer) >= (unsigned long)evacSeconds * 1000UL)) {
        LOGLN("[DEBRIS EVAC] Evacuation complete -> Motor OFF");
        hoseClearActive = false; forceStopNow = true; evaluateMotorDemand();
    }
    delay(2);
}

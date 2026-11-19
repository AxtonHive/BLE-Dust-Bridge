/**
 * BLE Dust Bridge - Fast-Response Shelly Plug Power Beacon (Gen3 / Gen4)
 *
 * Broadcasts live relay state and whole-wattage readings over passive BLE
 * manufacturer data (Company ID 0x0BA9, signature "SC") for BLE Dust Bridge.
 *
 * Timing Architecture:
 *  - Local wattage poll:   150 ms (CPU-only; zero BLE radio preemption)
 *  - Step-change burst:      0 ms immediate trigger when |deltaW| >= 15W or
 *                          relay toggles, gated by a 550 ms cooldown so
 *                          Shelly's BLE radio finishes airing across ch 37/38/39
 *  - Keep-alive heartbeat: 2000 ms (overlaps Shelly's 3000 ms advertiseOnce
 *                          window while leaving the radio ready for instant bursts)
 */

var CONFIG = {
  // BLE local name advertised to BLE Dust Bridge (max 17 chars to fit 31B ADV PDU)
  deviceName: "Shelly-Dust",
  // Switch component ID (0 for single-outlet Shelly Plug US / Plus Plug)
  switchId: 0,
  // Local power sampling interval in milliseconds
  pollMs: 150,
  // Minimum wattage jump/drop (W) required to trigger an immediate BLE burst
  stepDeltaW: 15,
  // Minimum spacing (ms) between consecutive BLE.advertiseOnce() calls
  burstCooldownMs: 550,
  // Steady-state refresh interval (ms) to keep the 3000 ms broadcast alive
  keepAliveMs: 2000
};

var seq = 0;
var tickMs = 0;
var lastTxMs = -10000;
var lastTxWatts = -1;
var lastTxRelay = null;
var hasBootTx = false;

function getNowMs() {
  if (typeof Shelly !== "undefined" && typeof Shelly.getUptimeMs === "function") {
    var up = Shelly.getUptimeMs();
    if (typeof up === "number" && up >= 0) {
      return up;
    }
  }
  return tickMs;
}

function transmitBleBeacon(relayOn, watts, nowMs) {
  try {
    var clampedW = watts < 0 ? 0 : (watts > 65535 ? 65535 : watts);
    seq = (seq + 1) & 0x3F;
    var flagsByte = (seq << 2) | (relayOn ? 0x01 : 0x00);
    var wLo = clampedW & 0xFF;
    var wHi = (clampedW >> 8) & 0xFF;

    var mfgPayload = String.fromCharCode(0x53, 0x43, flagsByte, wLo, wHi);

    BLE.AdvBuilder.reset();
    if (!BLE.AdvBuilder.addShellyManufacturerData(mfgPayload)) {
      print("[BLDB] Error: Failed to add manufacturer data");
      return false;
    }

    if (CONFIG.deviceName && CONFIG.deviceName.length > 0) {
      var safeName = CONFIG.deviceName.length > 17
        ? CONFIG.deviceName.slice(0, 17)
        : CONFIG.deviceName;
      BLE.AdvBuilder.addName(safeName, true);
    }

    var advData = BLE.AdvBuilder.build();
    if (BLE.advertiseOnce(advData)) {
      lastTxMs = nowMs;
      lastTxWatts = clampedW;
      lastTxRelay = relayOn;
      hasBootTx = true;
      return true;
    }
  } catch (err) {
    print("[BLDB] Broadcast exception:", JSON.stringify(err));
  }
  return false;
}

function evaluatePowerState(isTimerTick) {
  if (isTimerTick) {
    tickMs += CONFIG.pollMs;
  }

  var sw = null;
  try {
    sw = Shelly.getComponentStatus("switch", CONFIG.switchId);
  } catch (e) {
    return;
  }
  if (!sw) return;

  var relayOn = !!sw.output;
  var rawPower = (typeof sw.apower === "number") ? sw.apower : 0;
  var watts = relayOn ? Math.max(0, Math.round(rawPower)) : 0;
  var nowMs = getNowMs();
  var sinceLastTx = nowMs - lastTxMs;

  if (sinceLastTx < 0) {
    sinceLastTx = CONFIG.keepAliveMs;
  }

  var relayChanged = (lastTxRelay === null) || (relayOn !== lastTxRelay);
  var bigPowerStep = (lastTxWatts < 0) || (Math.abs(watts - lastTxWatts) >= CONFIG.stepDeltaW);
  var keepAliveDue = (sinceLastTx >= CONFIG.keepAliveMs);

  if (!hasBootTx || keepAliveDue) {
    transmitBleBeacon(relayOn, watts, nowMs);
    return;
  }

  if ((relayChanged || bigPowerStep) && sinceLastTx >= CONFIG.burstCooldownMs) {
    transmitBleBeacon(relayOn, watts, nowMs);
  }
}

Shelly.addStatusHandler(function (event) {
  if (!event || event.component !== ("switch:" + CONFIG.switchId)) return;
  if (event.delta && typeof event.delta.output !== "undefined") {
    evaluatePowerState(false);
  }
});

evaluatePowerState(false);
Timer.set(CONFIG.pollMs, true, function () {
  evaluatePowerState(true);
});

print("[BLDB] Fast Shelly power beacon started (poll=" + CONFIG.pollMs + "ms, step=" + CONFIG.stepDeltaW + "W, cooldown=" + CONFIG.burstCooldownMs + "ms)");

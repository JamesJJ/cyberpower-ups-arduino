/*
 * CyberPower UPS HID host → WiFi JSON HTTP server
 * Target: XIAO ESP32S3 (hwcdc default, USB OTG host)
 *
 * Uses ESP-IDF native USB host stack to send HID GET_FEATURE_REPORT
 * control transfers to CyberPower CP1500PFCLCDA (VID=0x0764, PID=0x0601).
 * Serves decoded UPS status as JSON on http://<ip>/ups
 *
 * TM1637 4-digit display: CLK=D9(GPIO8), DIO=D10(GPIO9)
 *   - WiFi connect: shows each IP octet sequentially, leftmost digit
 *     indicates octet index via progressive segment fill (1→2→3→4 segs)
 *   - Operation: cycles battery voltage / realpower / ups_status_raw,
 *     each shown for 5s with 5s display-off between each metric
 *
 */

#include "Arduino.h"
#include "WiFi.h"
#include "WebServer.h"
#include "TM1637Display.h"
#include "OneWire.h"
#include "DallasTemperature.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "usb/usb_host.h"

#include "CH3819_WiFi_PRIVATE.h"

#ifdef CH3819_WiFi_SSID
  #define WIFI_SSID CH3819_WiFi_SSID
  #define WIFI_PASS CH3819_WiFi_KEY
#else
  #define WIFI_SSID "" // REMEMBER TO SET YOUR WIFI DETAILS HERE
  #define WIFI_PASS ""
#endif 

// TM1637 pins (XIAO ESP32S3: D9=GPIO8, D10=GPIO9)
#define TM_CLK D9
#define TM_DIO D10

// LED PIN (XIAO ESP32S3: GPIO21, no board connection)
#define USER_LED LED_BUILTIN

// Leftmost digit segment indicators for each metric
// Segments: a=0x01 b=0x02 c=0x04 d=0x08 e=0x10 f=0x20 g=0x40
#define SEG_VOLT 0x7C // b-shape → voltage
#define SEG_WATT 0x73 // p-shape → watts
#define SEG_STAT 0x6D // S-shape → status
#define SEG_RSSI 0x4F // 3-shape (w on it's side ^^) → Wifi RSSI
#define SEG_TEMP 0x58 // small c (lower half) → temperature in C

static TM1637Display disp(TM_CLK, TM_DIO);

// DS18B20 on D2 (GPIO3)
static OneWire oneWire(D2);
static DallasTemperature tempSensor(&oneWire);
static DeviceAddress tempAddr;
static bool tempFound = false;


#define UPS_VID 0x0764
#define UPS_PID 0x0601

// ── UPS data ──────────────────────────────────────────────────────────────────
struct UpsData {
  float battery_charge;
  float battery_charge_low;
  float battery_charge_warning;
  uint32_t battery_runtime_s;
  uint32_t battery_runtime_low_s;
  float battery_voltage;
  float battery_voltage_nominal;
  float input_voltage;
  float input_voltage_nominal;
  float input_frequency_nominal;
  float input_frequency;
  float input_transfer_low;
  float output_voltage;
  float output_voltage_nominal;
  float output_frequency;
  float ups_realpower;
  float ups_apparent_power;
  float ups_realpower_nominal;
  float ups_load;
  const char *ups_beeper_status;
  uint8_t ups_status_raw;
  bool ac_present;
  bool charging;
  bool discharging;
  bool low_battery;
  bool fully_charged;
  bool runtime_limit_expired;
  uint32_t ups_delay_shutdown_s;
  bool valid;
};

static UpsData g_ups = {};
static SemaphoreHandle_t g_ups_mutex;
static WebServer server(80);
static uint32_t took_a_break_at = 0; // millis() timestamp of last delay/yield (the the processor sleep and not get hot
static uint32_t colon_on_at = 0; // millis() timestamp of last HTTP request, for colon flash
static uint32_t ac_lost_at = 0;  // millis() when ac_present last became false
static uint32_t ac_back_at = 0;  // millis() when ac_present last became true

// ── AC presence tracking over 300s window ─────────────────────────────────────
#define AC_HIST_WINDOW_S  300
#define AC_HIST_SLOTS     300   // 1 slot per second
static uint8_t  ac_hist[AC_HIST_SLOTS];  // 1 = ac present, 0 = not
static uint16_t ac_hist_idx = 0;
static uint32_t ac_hist_last_ms = 0;
static uint16_t ac_hist_count = 0;  // how many slots filled so far

static void ac_hist_record(bool ac_on) {
  uint32_t now = millis();
  if (ac_hist_last_ms == 0) { ac_hist_last_ms = now; }
  uint32_t elapsed = (now - ac_hist_last_ms) / 1000;
  if (elapsed == 0) return;
  uint8_t val = ac_on ? 1 : 0;
  for (uint32_t i = 0; i < elapsed && i < AC_HIST_SLOTS; i++) {
    ac_hist[ac_hist_idx] = val;
    ac_hist_idx = (ac_hist_idx + 1) % AC_HIST_SLOTS;
    if (ac_hist_count < AC_HIST_SLOTS) ac_hist_count++;
  }
  ac_hist_last_ms = now;
}

static float ac_hist_pct() {
  if (ac_hist_count == 0) return 100.0;
  uint16_t sum = 0;
  for (uint16_t i = 0; i < ac_hist_count; i++) sum += ac_hist[i];
  return 100.0f * sum / ac_hist_count;
}
static float g_temp_c = -127.0;  // last DS18B20 reading, -127 = invalid
static volatile uint32_t g_last_poll_ok = 0; // millis() of last successful poll

// ── Display state (desired vs actual) ─────────────────────────────────────────
static struct {
  uint8_t desired[4];
  uint8_t actual[4];
  bool    desired_on;
  bool    actual_on;
} dstate = { {}, {}, false, true }; // mismatch on boot forces initial push

// ── USB host state ────────────────────────────────────────────────────────────
static usb_host_client_handle_t g_client = NULL;
static usb_device_handle_t      g_dev    = NULL;
static uint8_t                  g_itf    = 0;
static volatile bool            g_dev_ready = false;

// ── Decode helpers ────────────────────────────────────────────────────────────
static uint32_t le_uint(const uint8_t *b, int off, int len) {
  uint32_t v = 0;
  for (int i = len - 1; i >= 0; i--) v = (v << 8) | b[off + i];
  return v;
}
static const char *beeper_str(uint8_t v) {
  switch (v) {
    case 1: return "disabled";
    case 2: return "enabled";
    case 3: return "muted";
    case 4: return "enabled+muted";
    case 5: return "enabled";
    default: return "unknown";
  }
}
static float freq_index(uint8_t i) {
  switch (i) { case 1: case 4: case 5: return 50; case 2: case 3: case 6: return 60; default: return 0; }
}
static float freq_nom(uint8_t i) {
  switch (i) { case 1: case 4: return 50; case 2: case 3: return 60; default: return 0; }
}
static float volt_nom(uint8_t i) {
  const float m[] = {0,100,110,120,200,208,220,230,240};
  return (i < 9) ? m[i] : 0;
}
static float batt_volt_nom(uint8_t i) {
  const float m[] = {0,12,24,36,48,72,96,108,120,144};
  return (i < 10) ? m[i] : 0;
}

// ── Synchronous HID GET_FEATURE_REPORT via control transfer ───────────────────
struct XferCtx { SemaphoreHandle_t sem; esp_err_t result; uint8_t *buf; };

static void xfer_cb(usb_transfer_t *t) {
  XferCtx *ctx = (XferCtx *)t->context;
  ctx->result = (t->status == USB_TRANSFER_STATUS_COMPLETED) ? ESP_OK : ESP_FAIL;
  // data starts after 8-byte setup packet
  if (ctx->result == ESP_OK && t->actual_num_bytes > 8)
    memcpy(ctx->buf, t->data_buffer + 8, t->actual_num_bytes - 8);
  xSemaphoreGive(ctx->sem);
}

static bool get_feature_report(uint8_t rid, uint8_t *out, uint16_t len) {
  if (!g_dev_ready || !g_dev) return false;

  usb_transfer_t *t = NULL;
  if (usb_host_transfer_alloc(8 + len, 0, &t) != ESP_OK) return false;

  // Build HID GET_FEATURE_REPORT setup packet
  t->data_buffer[0] = 0xA1; // bmRequestType: D→H, Class, Interface
  t->data_buffer[1] = 0x01; // bRequest: GET_REPORT
  t->data_buffer[2] = rid;
  t->data_buffer[3] = 0x03; // report type: Feature
  t->data_buffer[4] = 0;    // wIndex lo = interface number
  t->data_buffer[5] = 0;    // wIndex hi
  t->data_buffer[6] = (uint8_t)(len & 0xFF);
  t->data_buffer[7] = (uint8_t)(len >> 8);

  uint8_t tmp[64] = {};
  XferCtx ctx = { xSemaphoreCreateBinary(), ESP_FAIL, tmp };

  t->num_bytes      = 8 + len;
  t->device_handle  = g_dev;
  t->bEndpointAddress = 0; // control EP
  t->callback       = xfer_cb;
  t->context        = &ctx;
  t->timeout_ms     = 200;

  bool ok = false;
  if (usb_host_transfer_submit_control(g_client, t) == ESP_OK) {
    if (xSemaphoreTake(ctx.sem, pdMS_TO_TICKS(300)) == pdTRUE)
      ok = (ctx.result == ESP_OK);
  }
  vSemaphoreDelete(ctx.sem);
  usb_host_transfer_free(t);

  if (ok) memcpy(out, tmp, len);
  return ok;
}

// ── Poll and decode all UPS fields ───────────────────────────────────────────
// Bitmask positions for each polled report ID
#define RID_BATTERY   (1 << 0)  // 0x08
#define RID_BATCFG    (1 << 1)  // 0x07
#define RID_BATVOLT   (1 << 2)  // 0x0a
#define RID_INPUTV    (1 << 3)  // 0x0f
#define RID_INPUTF    (1 << 4)  // 0x0e
#define RID_STATUS    (1 << 5)  // 0x0b
#define RID_REALPOWER (1 << 6)  // 0x19
#define RID_APPARENT  (1 << 7)  // 0x1d
#define RID_REQUIRED  (RID_BATTERY | RID_STATUS | RID_REALPOWER)

static uint32_t g_poll_ok_mask = 0;
// RIDs found in HID report descriptor
static uint8_t g_desc_rids[64];
static uint8_t g_desc_rid_count = 0;
// Unknown RID probe results (descriptor RIDs not in known set)
static uint8_t g_unknown_rids[64];  // first data byte per RID (indexed by RID)
static bool g_rid_responds[64];
static bool g_rid_scan_done = false;

// Known RIDs we poll
static const uint8_t known_rids[] = {
  0x07, 0x08, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
  0x10, 0x12, 0x13, 0x14, 0x16, 0x18, 0x19, 0x1a, 0x1b, 0x1d
};

static bool is_known_rid(uint8_t rid) {
  for (uint8_t k : known_rids) if (k == rid) return true;
  return false;
}

// Fetch HID report descriptor and extract REPORT_ID values
static void parse_hid_report_descriptor() {
  if (!g_dev_ready || !g_dev) return;

  // GET_DESCRIPTOR: type 0x22 (HID Report), interface index
  usb_transfer_t *t = NULL;
  const uint16_t max_len = 512;
  if (usb_host_transfer_alloc(8 + max_len, 0, &t) != ESP_OK) return;

  t->data_buffer[0] = 0x81; // bmRequestType: D→H, Standard, Interface
  t->data_buffer[1] = 0x06; // bRequest: GET_DESCRIPTOR
  t->data_buffer[2] = 0x00; // wValue lo: descriptor index 0
  t->data_buffer[3] = 0x22; // wValue hi: HID Report descriptor type
  t->data_buffer[4] = g_itf; // wIndex lo: interface number
  t->data_buffer[5] = 0;
  t->data_buffer[6] = (uint8_t)(max_len & 0xFF);
  t->data_buffer[7] = (uint8_t)(max_len >> 8);

  uint8_t desc_buf[512] = {};
  XferCtx ctx = { xSemaphoreCreateBinary(), ESP_FAIL, desc_buf };

  t->num_bytes      = 8 + max_len;
  t->device_handle  = g_dev;
  t->bEndpointAddress = 0;
  t->callback       = xfer_cb;
  t->context        = &ctx;
  t->timeout_ms     = 500;

  bool ok = false;
  uint16_t desc_len = 0;
  if (usb_host_transfer_submit_control(g_client, t) == ESP_OK) {
    if (xSemaphoreTake(ctx.sem, pdMS_TO_TICKS(600)) == pdTRUE && ctx.result == ESP_OK)  {
      ok = true;
      desc_len = t->actual_num_bytes > 8 ? t->actual_num_bytes - 8 : 0;
    }
  }
  vSemaphoreDelete(ctx.sem);
  usb_host_transfer_free(t);

  if (!ok || desc_len == 0) return;

  // Walk HID item stream, collect REPORT_ID items (prefix 0x85 = 1-byte global, tag 8)
  g_desc_rid_count = 0;
  uint16_t i = 0;
  while (i < desc_len && g_desc_rid_count < sizeof(g_desc_rids)) {
    uint8_t prefix = desc_buf[i];
    if (prefix == 0xFE) { // long item
      if (i + 2 >= desc_len) break;
      i += 3 + desc_buf[i + 1];
      continue;
    }
    uint8_t sz = prefix & 0x03;
    if (sz == 3) sz = 4; // size encoding: 0,1,2,4
    if (prefix == 0x85 && sz == 1 && i + 1 < desc_len) {
      g_desc_rids[g_desc_rid_count++] = desc_buf[i + 1];
    }
    i += 1 + sz;
  }
}

static void poll_ups() {
  uint8_t buf[64];
  UpsData d = {};
  d.ups_beeper_status = "unknown";
  uint32_t mask = 0;

  auto rd = [&](uint8_t rid) -> bool {
    memset(buf, 0, 64);
    return get_feature_report(rid, buf, 64);
  };

  // One-time: parse HID descriptor and probe unknown RIDs
  if (!g_rid_scan_done) {
    if (g_desc_rid_count == 0) parse_hid_report_descriptor();
    for (uint8_t i = 0; i < g_desc_rid_count; i++) {
      uint8_t rid = g_desc_rids[i];
      if (is_known_rid(rid) || rid >= 64) continue;
      if (rd(rid)) {
        g_rid_responds[rid] = true;
        g_unknown_rids[rid] = buf[1];
      }
    }
    g_rid_scan_done = true;
  }

  if (rd(0x08)) {
    d.battery_charge        = le_uint(buf, 1, 1);
    d.battery_runtime_s     = le_uint(buf, 2, 2);
    d.battery_runtime_low_s = le_uint(buf, 4, 2);
    mask |= RID_BATTERY;
  }
  if (rd(0x07)) {
    d.battery_charge_warning = le_uint(buf, 4, 1);
    d.battery_charge_low     = le_uint(buf, 5, 1);
    mask |= RID_BATCFG;
  }
  if (rd(0x0a)) { d.battery_voltage = le_uint(buf, 1, 2) * 0.1f; mask |= RID_BATVOLT; }
  if (rd(0x1a)) d.battery_voltage_nominal   = batt_volt_nom(le_uint(buf, 1, 1));
  if (rd(0x0f)) { d.input_voltage = le_uint(buf, 1, 2); mask |= RID_INPUTV; }
  if (rd(0x0c)) d.input_voltage_nominal     = volt_nom(le_uint(buf, 1, 1));
  if (rd(0x0d)) d.input_frequency_nominal   = freq_nom(le_uint(buf, 1, 1));
  if (rd(0x0e)) { d.input_frequency = le_uint(buf, 1, 1) * 0.5f; mask |= RID_INPUTF; }
  if (rd(0x10)) d.input_transfer_low        = le_uint(buf, 1, 2);
  if (rd(0x12)) d.output_voltage            = le_uint(buf, 1, 2);
  if (rd(0x13)) d.output_voltage_nominal    = volt_nom(le_uint(buf, 1, 1));
  if (rd(0x14)) d.output_frequency          = freq_index(le_uint(buf, 1, 1));
  if (rd(0x19)) {
    d.ups_realpower = le_uint(buf, 1, 2);
    mask |= RID_REALPOWER;
    if (rd(0x18)) {
      d.ups_realpower_nominal = le_uint(buf, 1, 2);
      d.ups_load = d.ups_realpower_nominal > 0
                   ? d.ups_realpower / d.ups_realpower_nominal * 100.0f : 0;
    }
  }
  if (rd(0x18)) d.ups_realpower_nominal = le_uint(buf, 1, 2);
  if (rd(0x1d)) { d.ups_apparent_power = le_uint(buf, 1, 2); mask |= RID_APPARENT; }
  if (rd(0x1b)) d.ups_beeper_status     = beeper_str(le_uint(buf, 1, 1));
  if (rd(0x0b)) {
    uint8_t s = le_uint(buf, 1, 1);
    d.ups_status_raw        = s;
    d.ac_present            = s & (1 << 0);
    d.charging              = s & (1 << 1);
    d.discharging           = s & (1 << 2);
    d.low_battery           = s & (1 << 3);
    d.fully_charged         = s & (1 << 4);
    d.runtime_limit_expired = s & (1 << 5);
    mask |= RID_STATUS;
  }
  if (rd(0x16)) {
    uint32_t raw = le_uint(buf, 1, 2);
    d.ups_delay_shutdown_s = (raw == 0xFFFF) ? 0 : raw;
  }

  g_poll_ok_mask = mask;
  d.valid = (mask & RID_REQUIRED) == RID_REQUIRED;
  xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
  if (g_ups.valid && d.ac_present != g_ups.ac_present) {
    if (d.ac_present) ac_back_at = millis();
    else              ac_lost_at = millis();
  }
  g_ups = d;
  g_last_poll_ok = millis();
  ac_hist_record(d.ac_present);
  xSemaphoreGive(g_ups_mutex);
}

// ── USB host task (runs on core 0) ────────────────────────────────────────────
static void usb_host_task(void *) {
  usb_host_config_t cfg = { .skip_phy_setup = false, .intr_flags = ESP_INTR_FLAG_LEVEL1 };
  ESP_ERROR_CHECK(usb_host_install(&cfg));

  usb_host_client_config_t ccfg = {
    .is_synchronous    = false,
    .max_num_event_msg = 5,
    .async = { .client_event_callback = [](const usb_host_client_event_msg_t *msg, void *) {
      if (msg->event == USB_HOST_CLIENT_EVENT_NEW_DEV) {
        uint8_t addr = msg->new_dev.address;
        usb_device_handle_t dev;
        if (usb_host_device_open(g_client, addr, &dev) != ESP_OK) return;
        const usb_device_desc_t *desc;
        usb_host_get_device_descriptor(dev, &desc);
        if (desc->idVendor == UPS_VID && desc->idProduct == UPS_PID) {
          // Claim first HID interface (interface 0)
          const usb_config_desc_t *cfg_desc;
          usb_host_get_active_config_descriptor(dev, &cfg_desc);
          // Find first HID interface number
          int offset = 0;
          const usb_intf_desc_t *intf = usb_parse_interface_descriptor(cfg_desc, 0, 0, &offset);
          if (intf && usb_host_interface_claim(g_client, dev, intf->bInterfaceNumber, 0) == ESP_OK) {
            g_itf = intf->bInterfaceNumber;
            g_dev = dev;
            g_dev_ready = true;
          }
        } else {
          usb_host_device_close(g_client, dev);
        }
      } else if (msg->event == USB_HOST_CLIENT_EVENT_DEV_GONE) {
        if (g_dev) {
          g_dev_ready = false;
          g_rid_scan_done = false;
          g_desc_rid_count = 0;
          memset(g_rid_responds, 0, sizeof(g_rid_responds));
          xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
          g_ups = {};
          xSemaphoreGive(g_ups_mutex);
          usb_host_interface_release(g_client, g_dev, g_itf);
          usb_host_device_close(g_client, g_dev);
          g_dev = NULL;
        }
      }
    }, .callback_arg = NULL }
  };
  ESP_ERROR_CHECK(usb_host_client_register(&ccfg, &g_client));

  while (true) {
    usb_host_lib_handle_events(pdMS_TO_TICKS(10), NULL);
    usb_host_client_handle_events(g_client, pdMS_TO_TICKS(10));
  }
}

// ── Display helpers ───────────────────────────────────────────────────────────
// Push desired state to hardware when it differs from actual
static void disp_flush() {
  if (dstate.desired_on == dstate.actual_on &&
      memcmp(dstate.desired, dstate.actual, 4) == 0) return;
  if (!dstate.desired_on) {
    disp.clear();
    memset(dstate.actual, 0, 4);
  } else {
    disp.setSegments(dstate.desired, 4, 0);
    memcpy(dstate.actual, dstate.desired, 4);
  }
  dstate.actual_on = dstate.desired_on;
  // LED ON when display is off
  digitalWrite(USER_LED, dstate.desired_on ? HIGH : LOW);
}

// Write 4 raw segment bytes into desired
static void show_word(const uint8_t segs[4]) {
  memcpy(dstate.desired, segs, 4);
  dstate.desired_on = true;
}

// Encode |value| into 3 digits at desired[1..3], no leading zeros
static void encode_number(int value) {
  bool neg = value < 0;
  unsigned v = neg ? -value : value;
  uint8_t d[3] = {0, 0, disp.encodeDigit(v % 10)};
  v /= 10;
  if (v) { d[1] = disp.encodeDigit(v % 10); v /= 10; }
  if (v) d[0] = disp.encodeDigit(v % 10);
  if (neg) { // put minus in leftmost non-blank position
    for (int i = 0; i < 3; i++) { if (!d[i]) { d[i] = 0x40; break; } }
  }
  memcpy(&dstate.desired[1], d, 3);
}

// Show indicator segment on pos 0, value right-aligned on pos 1-3
static void show_metric(uint8_t indicator, int value) {
  dstate.desired[0] = indicator;
  encode_number(value);
  dstate.desired_on = true;
}

static void disp_off() {
  memset(dstate.desired, 0, 4);
  dstate.desired_on = false;
}

// ── HTTP handler ──────────────────────────────────────────────────────────────
static void handle_ups() {
  colon_on_at = millis(); // triggers colon flash in loop

  xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
  UpsData d = g_ups;
  xSemaphoreGive(g_ups_mutex);

  char json[900];
  snprintf(json, sizeof(json),
    "{"
    "\"ups_connected\":%s,"
    "\"battery_charge_pct\":%.0f,"
    "\"battery_charge_low_pct\":%.0f,"
    "\"battery_charge_warning_pct\":%.0f,"
    "\"battery_runtime_s\":%lu,"
    "\"battery_runtime_low_s\":%lu,"
    "\"battery_voltage_v\":%.1f,"
    "\"input_voltage_v\":%.0f,"
    "\"input_frequency_hz\":%.1f,"
    "\"input_transfer_low_v\":%.0f,"
    "\"output_voltage_v\":%.0f,"
    "\"output_frequency_hz\":%.0f,"
    "\"ups_realpower_w\":%.0f,"
    "\"ups_apparent_power_va\":%.0f,"
    "\"ups_load_pct\":%.1f,"
    "\"ups_beeper_status\":\"%s\","
    "\"ups_status_raw\":%u,"
    "\"ac_present\":%s,"
    "\"charging\":%s,"
    "\"discharging\":%s,"
    "\"low_battery\":%s,"
    "\"fully_charged\":%s,"
    "\"runtime_limit_expired\":%s,"
    "\"ups_delay_shutdown_s\":%lu,"
    "\"uptime_ms\":%lu,"
    "\"wifi_rssi_dbm\":%d,"
    "\"ac_lost_at_ms\":%lu,"
    "\"ac_back_at_ms\":%lu,"
    "\"temperature_c\":%.1f,"
    "\"ups_update_ms\":%lu,"
    "\"poll_ok_mask\":\"0x%02lx\","
    "\"ac_present_pct_300s\":%.1f"
    "}",
    d.valid ? "true" : "false",
    d.battery_charge, d.battery_charge_low, d.battery_charge_warning,
    d.battery_runtime_s, d.battery_runtime_low_s,
    d.battery_voltage,
    d.input_voltage,
    d.input_frequency,
    d.input_transfer_low,
    d.output_voltage, d.output_frequency,
    d.ups_realpower, d.ups_apparent_power,
    d.ups_load, d.ups_beeper_status ? d.ups_beeper_status : "unknown",
    d.ups_status_raw,
    d.ac_present ? "true" : "false",
    d.charging ? "true" : "false",
    d.discharging ? "true" : "false",
    d.low_battery ? "true" : "false",
    d.fully_charged ? "true" : "false",
    d.runtime_limit_expired ? "true" : "false",
    d.ups_delay_shutdown_s,
    millis(),
    WiFi.RSSI(),
    ac_lost_at,
    ac_back_at,
    g_temp_c,
    g_last_poll_ok,
    (unsigned long)g_poll_ok_mask,
    ac_hist_pct()
  );
  server.send(200, "application/json", json);
}

static void handle_diag() {
  char hex[8];
  String out = "{\"poll_ok_mask\":\"0x";
  snprintf(hex, sizeof(hex), "%02lx", (unsigned long)g_poll_ok_mask);
  out += hex;
  out += "\",\"rid_scan_done\":";
  out += g_rid_scan_done ? "true" : "false";
  out += ",\"descriptor_rids\":[";
  for (uint8_t i = 0; i < g_desc_rid_count; i++) {
    if (i) out += ",";
    snprintf(hex, sizeof(hex), "\"0x%02x\"", g_desc_rids[i]);
    out += hex;
  }
  out += "],\"unknown_rids\":{";
  bool first = true;
  for (uint8_t i = 0; i < 0x40; i++) {
    if (!g_rid_responds[i]) continue;
    if (!first) out += ",";
    first = false;
    snprintf(hex, sizeof(hex), "\"0x%02x\"", i);
    out += hex;
    out += ":";
    snprintf(hex, sizeof(hex), "%u", g_unknown_rids[i]);
    out += hex;
  }
  out += "}}";
  server.send(200, "application/json", out);
}

// ── Setup / Loop ──────────────────────────────────────────────────────────────
void setup() {
  pinMode(USER_LED, OUTPUT);
  digitalWrite(USER_LED, HIGH);  // off (active-low)
  setCpuFrequencyMhz(80);
  disp.setBrightness(1);
  const uint8_t seg_helo[] = { 0x76, 0x79, 0x38, 0x3F }; // HELO
  disp.setSegments(seg_helo, 4, 0);

  g_ups_mutex = xSemaphoreCreateMutex();

  tempSensor.begin();
  tempSensor.setWaitForConversion(false);
  if (tempSensor.getAddress(tempAddr, 0)) {
    tempFound = true;
    tempSensor.requestTemperatures();
  }

  xTaskCreatePinnedToCore(usb_host_task, "usb_host", 4096, NULL, 5, NULL, 0);

  WiFi.setSleep(WIFI_PS_MIN_MODEM);
  // WiFi.setSleep(false);
  WiFi.begin(WIFI_SSID, WIFI_PASS);
  { uint32_t t = millis();
    while (WiFi.status() != WL_CONNECTED && millis() - t < 20000) delay(300);
  }

  server.on("/ups", handle_ups);
  server.on("/diag", handle_diag);
  server.begin();
}

void loop() {
  server.handleClient();

  // WiFi reconnect: retry every 60s when disconnected
  static uint32_t last_wifi_try = 0;
  if (WiFi.status() != WL_CONNECTED && millis() - last_wifi_try >= 60000) {
    last_wifi_try = millis();
    WiFi.disconnect();
    WiFi.begin(WIFI_SSID, WIFI_PASS);
  }

  // Poll UPS every 5s; clear data if stale for 60s
  static uint32_t last_poll = 0;
  if (millis() - last_poll >= 1000) {
    last_poll = millis();
    if (g_dev_ready) poll_ups();
  }
  if (g_ups.valid && g_last_poll_ok && millis() - g_last_poll_ok > 60000) {
    xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
    g_ups = {};
    xSemaphoreGive(g_ups_mutex);
  }

  // DS18B20: read result and request next conversion every 2s
  static uint32_t last_temp = 0;
  if (tempFound && millis() - last_temp >= 30000) {
    last_temp = millis();
    float t = tempSensor.getTempC(tempAddr);
    if (t != DEVICE_DISCONNECTED_C) g_temp_c = t;
    tempSensor.requestTemperatures();
  }

  // Display cycle — always runs regardless of UPS connection.
  // Phases (5s each):
  //   0: UPS status label ("UPS " or "nOnE")
  //   1: battery voltage (UPS only, else off)
  //   2: off
  //   3: realpower watts (UPS only, else off)
  //   4: off
  //   5: temperature (if sensor present, else off)
  //   6: off
  //   7: WiFi RSSI (if connected, else off)
  //   8: off
  //   9: IP octet 1
  //  10: IP octet 2
  //  11: IP octet 3
  //  12: IP octet 4
  //  13: off  → restart
  static uint32_t disp_start = 0;
  static uint32_t last_phase = 99;

  uint32_t phase = (millis() - disp_start) / 1800;
  if (phase != last_phase) {
    last_phase = phase;

    xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
    UpsData d = g_ups;
    xSemaphoreGive(g_ups_mutex);

    // Segment encodings
    const uint8_t seg_ups[]  = { 0x3E, 0x73, 0x6D, 0x00 };
    const uint8_t seg_none[] = { 0x37, 0x3F, 0x37, 0x79 };
    const uint8_t ip_ind[]   = { 0x01, 0x09, 0x49, 0x63 };

    bool wifi_ok = WiFi.status() == WL_CONNECTED;

    switch (phase % 15) {
      case 0:  show_word(g_dev_ready ? seg_ups : seg_none); break;
      case 1:  if (d.valid) show_metric(SEG_VOLT, (int)(d.battery_voltage * 10));
               else disp_off(); break;
      case 2:  disp_off(); break;
      case 3:  if (d.valid) show_metric(SEG_WATT, (int)d.ups_realpower);
               else disp_off(); break;
      case 4:  disp_off(); break;
      case 5:  if (g_temp_c > -127.0) show_metric(SEG_TEMP, (int)(g_temp_c * 10));
               else disp_off(); break;
      case 6:  disp_off(); break;
      case 7:  if (wifi_ok) show_metric(SEG_RSSI, WiFi.RSSI());
               else disp_off(); break;
      case 8:  disp_off(); break;
      case 9:  // fall through
      case 10:
      case 11:
      case 12: { int i = phase % 14 - 9;
               if (wifi_ok) show_metric(ip_ind[i], WiFi.localIP()[i]);
               else { const uint8_t no_wifi[] = {ip_ind[i], 0x10, 0x10, 0x10};
                      show_word(no_wifi); } } break;
      case 13: disp_off(); break;
      case 14: disp_start = millis(); last_phase = 99; break;
    }
  }

  // Colon flash: show for 300ms on each HTTP request
  if (colon_on_at && millis() - colon_on_at <= 300) {
    dstate.desired[1] |= 0x80;
    dstate.desired_on = true;
  } else {
    dstate.desired[1] &= ~0x80;
    colon_on_at = 0;
  }

  disp_flush();

  if (millis() - took_a_break_at > 5) {
    delay(1);
    took_a_break_at = millis();
  }

}

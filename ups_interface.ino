
/*
 * CyberPower UPS HID host → WiFi JSON HTTP server
 * Target: XIAO ESP32S3 (hwcdc default, USB OTG host)
 *
 * Build compatibility (validated 2026-10-03):
 *   - Primary: Arduino ESP32 core 3.3.12 / ESP-IDF 5.5.5
 *   - Compatible: Arduino ESP32 core 3.3.10 / ESP-IDF 5.5.4
 *   - Libraries: TM1637 1.2.0, OneWire 2.3.8, DallasTemperature 4.0.6
 *   - Optional private build: CH3819_PRIVATE 0.0.2, CH3819_WIFI 1.0.0,
 *     CH3819_OTA 1.1.0
 *
 * ESP32 core 3.3.12 enables the USB enumeration-filter callback whereas
 * 3.3.10 does not. The callback below is deliberately supplied for both, so
 * neither of these previously supported versions is excluded.
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

/* ########### THIS IS THE PUBLIC VERSION ########### */
/* https://github.com/JamesJJ/cyberpower-ups-arduino  */
/* ################################################## */

#if !defined(ARDUINO_XIAO_ESP32S3)
#error "Wrong board selected!"
#endif

#include "Arduino.h"
#include "WiFi.h"
#include "WebServer.h"
#include "TM1637Display.h"
#include "OneWire.h"
#include "DallasTemperature.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "freertos/queue.h"
#include "usb/usb_host.h"
#include "esp_task_wdt.h"

/*  ----------- DISABLE THESE 3 "CH3819_" INCLUDES (unless you are JamesJJ) ------------- */
// #include <CH3819_PRIVATE.h>
// #include <CH3819_WIFI.h>
// #include <CH3819_OTA.h>
/* ------------------------------------------------------------ */

#ifdef CH3819_PRIVATE_H
#define WIFI_SSID CH3819_WiFi_SSID
#define WIFI_PASS CH3819_WiFi_KEY
#else
#define WIFI_SSID "" /* --- REMEMBER TO SET YOUR WIFI DETAILS HERE ---- */
#define WIFI_PASS ""
#endif

// TM1637 pins (XIAO ESP32S3: D9=GPIO8, D10=GPIO9)
#define TM_CLK D9
#define TM_DIO D10

// LED PIN (XIAO ESP32S3: GPIO21, no board connection)
#define USER_LED LED_BUILTIN

// Leftmost digit segment indicators for each metric
// Segments: a=0x01 b=0x02 c=0x04 d=0x08 e=0x10 f=0x20 g=0x40
#define SEG_VOLT 0x7C  // b-shape → voltage
#define SEG_WATT 0x73  // p-shape → watts
#define SEG_STAT 0x6D  // S-shape → status
#define SEG_RSSI 0x4F  // 3-shape (w on it's side ^^) → Wifi RSSI
#define SEG_TEMP 0x58  // small c (lower half) → temperature in C

static TM1637Display disp(TM_CLK, TM_DIO);

// DS18B20 on D2 (GPIO3)
static OneWire oneWire(D2);
static DallasTemperature tempSensor(&oneWire);
static DeviceAddress tempAddr;
static bool tempFound = false;


#define UPS_VID 0x0764
#define UPS_PID 0x0601

// Explicit declarations prevent Arduino's prototype generator from depending on
// Ctags-specific return-type metadata. This supports both Arduino Ctags and
// Universal Ctags without changing normal C++ compilation.
static void ac_hist_record(bool ac_on);
static float ac_hist_pct();
static uint32_t le_uint(const uint8_t *b, int off, int len);
static const char *beeper_str(uint8_t v);
static float freq_index(uint8_t i);
static float freq_nom(uint8_t i);
static float volt_nom(uint8_t i);
static float batt_volt_nom(uint8_t i);
static void xfer_cb(usb_transfer_t *t);
static bool control_in(uint8_t request_type, uint8_t request, uint16_t value, uint16_t index, uint16_t len, uint32_t expected_generation, uint8_t *out, size_t out_capacity, size_t *actual_data_len, uint32_t wait_ms);
static bool get_feature_report(uint8_t rid, uint8_t *out, uint16_t len, uint32_t generation);
static bool is_known_rid(uint8_t rid);
static bool parse_hid_report_descriptor(uint32_t generation);
static void poll_ups();
static void reset_rid_state_locked();
static void close_opened_device(usb_device_handle_t dev);
static const char *usb_stage_str(uint8_t stage);
static void set_usb_stage(uint8_t stage, esp_err_t error);
static bool try_open_ups(uint8_t addr);
static void mark_device_gone(usb_device_handle_t gone);
static void process_pending_cleanup();
static void scan_for_ups();
static bool usb_enum_filter_cb(const usb_device_desc_t *dev_desc, uint8_t *configuration_value);
static void usb_event_cb(const usb_host_client_event_msg_t *msg, void *arg);
static void usb_host_task(void *arg);
static void disp_flush();
static void show_word(const uint8_t segs[4]);
static void encode_number(int value);
static void show_metric(uint8_t indicator, int value);
static void disp_off();
static void handle_ups();
static void handle_diag();
void setup();
void loop();

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
static uint32_t took_a_break_at = 0;  // millis() timestamp of last delay/yield (the the processor sleep and not get hot
static uint32_t colon_on_at = 0;      // millis() timestamp of last HTTP request, for colon flash
static uint32_t ac_lost_at = 0;       // millis() when ac_present last became false
static uint32_t ac_back_at = 0;       // millis() when ac_present last became true

// ── AC presence tracking over 300s window ─────────────────────────────────────
#define AC_HIST_WINDOW_S 300
#define AC_HIST_SLOTS 300               // 1 slot per second
static uint8_t ac_hist[AC_HIST_SLOTS];  // 1 = ac present, 0 = not
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
static float g_temp_c = -127.0;               // last DS18B20 reading, -127 = invalid
static volatile uint32_t g_last_poll_ok = 0;  // millis() of last successful poll

// ── Display state (desired vs actual) ─────────────────────────────────────────
static struct {
  uint8_t desired[4];
  uint8_t actual[4];
  bool desired_on;
  bool actual_on;
} dstate = { {}, {}, false, true };  // mismatch on boot forces initial push

// ── USB host state ────────────────────────────────────────────────────────────
static usb_host_client_handle_t g_client = NULL;
static usb_device_handle_t g_dev = NULL;
static uint8_t g_itf = 0;
static volatile bool g_dev_ready = false;
static uint32_t g_dev_generation = 0;  // protected by g_dev_mutex
static SemaphoreHandle_t g_dev_mutex;

// One persistent control transfer. A submitted transfer is never freed while it
// may still be owned by ESP-IDF, even if the caller stops waiting for it.
#define USB_CTRL_MAX_DATA 512
static usb_transfer_t *g_xfer = NULL;
static SemaphoreHandle_t g_xfer_mutex;
static SemaphoreHandle_t g_xfer_sem;
static volatile bool g_xfer_in_flight = false;
static esp_err_t g_xfer_result = ESP_FAIL;
static int g_xfer_actual_num_bytes = 0;

// The ESP-IDF callback only copies events here. The USB task performs all
// potentially blocking open/claim/release/close work after handle_events().
static QueueHandle_t g_usb_event_queue;
static volatile bool g_usb_rescan_requested = false;
static usb_device_handle_t g_cleanup_dev = NULL;  // USB task only
static uint8_t g_cleanup_itf = 0;                 // USB task only
static bool g_cleanup_pending = false;            // USB task only

enum UsbStage : uint8_t {
  USB_STAGE_STARTING,
  USB_STAGE_WAITING,
  USB_STAGE_OPENING,
  USB_STAGE_DESCRIPTOR_FAILED,
  USB_STAGE_CONFIG_FAILED,
  USB_STAGE_INTERFACE_FAILED,
  USB_STAGE_CLAIM_FAILED,
  USB_STAGE_READY,
  USB_STAGE_GONE,
  USB_STAGE_CLEANUP
};
// Protected by g_dev_mutex unless declared volatile and accessed atomically.
static uint8_t g_usb_stage = USB_STAGE_STARTING;
static esp_err_t g_usb_last_error = ESP_OK;
static uint16_t g_usb_last_vid = 0;
static uint16_t g_usb_last_pid = 0;
static uint8_t g_usb_interface_count = 0;
static uint8_t g_usb_selected_interface = 0;
static uint8_t g_usb_selected_class = 0;
static uint32_t g_usb_new_events = 0;
static uint32_t g_usb_gone_events = 0;
static uint32_t g_usb_open_attempts = 0;
static volatile int g_xfer_last_submit_result = ESP_OK;
static volatile int g_xfer_last_status = -1;
static volatile uint32_t g_xfer_submit_count = 0;
static volatile uint32_t g_xfer_callback_count = 0;
static volatile uint32_t g_xfer_timeout_count = 0;
static volatile uint32_t g_usb_task_loops = 0;
static volatile int g_usb_last_lib_result = ESP_OK;
static volatile int g_usb_last_client_result = ESP_OK;
static volatile int g_usb_library_device_count = 0;

static const char *usb_stage_str(uint8_t stage) {
  switch (stage) {
    case USB_STAGE_STARTING: return "starting";
    case USB_STAGE_WAITING: return "waiting";
    case USB_STAGE_OPENING: return "opening";
    case USB_STAGE_DESCRIPTOR_FAILED: return "descriptor_failed";
    case USB_STAGE_CONFIG_FAILED: return "config_failed";
    case USB_STAGE_INTERFACE_FAILED: return "interface_failed";
    case USB_STAGE_CLAIM_FAILED: return "claim_failed";
    case USB_STAGE_READY: return "ready";
    case USB_STAGE_GONE: return "gone";
    case USB_STAGE_CLEANUP: return "cleanup";
    default: return "unknown";
  }
}

static void set_usb_stage(uint8_t stage, esp_err_t error) {
  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  g_usb_stage = stage;
  g_usb_last_error = error;
  xSemaphoreGive(g_dev_mutex);
}

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
  switch (i) {
    case 1:
    case 4:
    case 5: return 50;
    case 2:
    case 3:
    case 6: return 60;
    default: return 0;
  }
}
static float freq_nom(uint8_t i) {
  switch (i) {
    case 1:
    case 4: return 50;
    case 2:
    case 3: return 60;
    default: return 0;
  }
}
static float volt_nom(uint8_t i) {
  const float m[] = { 0, 100, 110, 120, 200, 208, 220, 230, 240 };
  return (i < 9) ? m[i] : 0;
}
static float batt_volt_nom(uint8_t i) {
  const float m[] = { 0, 12, 24, 36, 48, 72, 96, 108, 120, 144 };
  return (i < 10) ? m[i] : 0;
}

// ── Synchronous control transfer wrapper ──────────────────────────────────────
// ESP-IDF 5.5 does not implement usb_transfer_t::timeout_ms. Keep the transfer
// and all callback state alive permanently so a late completion is always safe.
static void xfer_cb(usb_transfer_t *t) {
  __atomic_store_n(&g_xfer_last_status, (int)t->status, __ATOMIC_RELEASE);
  __atomic_add_fetch(&g_xfer_callback_count, 1U, __ATOMIC_RELAXED);
  g_xfer_result = (t->status == USB_TRANSFER_STATUS_COMPLETED) ? ESP_OK : ESP_FAIL;
  g_xfer_actual_num_bytes = t->actual_num_bytes;
  // Give first, then publish idle. This prevents a new request from draining the
  // semaphore before a late callback has given it.
  xSemaphoreGive(g_xfer_sem);
  __atomic_store_n(&g_xfer_in_flight, false, __ATOMIC_RELEASE);
}

static bool control_in(uint8_t request_type, uint8_t request,
                       uint16_t value, uint16_t index, uint16_t len,
                       uint32_t expected_generation, uint8_t *out,
                       size_t out_capacity, size_t *actual_data_len,
                       uint32_t wait_ms) {
  if (!out || len > USB_CTRL_MAX_DATA || out_capacity < len || !g_xfer) return false;
  if (xSemaphoreTake(g_xfer_mutex, pdMS_TO_TICKS(100)) != pdTRUE) return false;

  if (__atomic_load_n(&g_xfer_in_flight, __ATOMIC_ACQUIRE)) {
    xSemaphoreGive(g_xfer_mutex);
    return false;
  }

  if (xSemaphoreTake(g_dev_mutex, pdMS_TO_TICKS(100)) != pdTRUE) {
    xSemaphoreGive(g_xfer_mutex);
    return false;
  }
  if (!__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) || !g_dev ||
      g_dev_generation != expected_generation) {
    xSemaphoreGive(g_dev_mutex);
    xSemaphoreGive(g_xfer_mutex);
    return false;
  }

  usb_device_handle_t dev = g_dev;
  memset(g_xfer->data_buffer, 0, 8 + len);
  g_xfer->data_buffer[0] = request_type;
  g_xfer->data_buffer[1] = request;
  g_xfer->data_buffer[2] = (uint8_t)(value & 0xFF);
  g_xfer->data_buffer[3] = (uint8_t)(value >> 8);
  g_xfer->data_buffer[4] = (uint8_t)(index & 0xFF);
  g_xfer->data_buffer[5] = (uint8_t)(index >> 8);
  g_xfer->data_buffer[6] = (uint8_t)(len & 0xFF);
  g_xfer->data_buffer[7] = (uint8_t)(len >> 8);
  g_xfer->num_bytes = 8 + len;
  g_xfer->device_handle = dev;
  g_xfer->bEndpointAddress = 0;
  g_xfer->callback = xfer_cb;
  g_xfer->context = NULL;
  g_xfer->timeout_ms = 0;  // unsupported by the current ESP-IDF

  xSemaphoreTake(g_xfer_sem, 0);  // drain a completed request whose waiter timed out
  g_xfer_result = ESP_FAIL;
  g_xfer_actual_num_bytes = 0;
  __atomic_store_n(&g_xfer_in_flight, true, __ATOMIC_RELEASE);
  esp_err_t submit_result = usb_host_transfer_submit_control(g_client, g_xfer);
  __atomic_store_n(&g_xfer_last_submit_result, (int)submit_result, __ATOMIC_RELEASE);
  __atomic_add_fetch(&g_xfer_submit_count, 1U, __ATOMIC_RELAXED);
  if (submit_result != ESP_OK) {
    __atomic_store_n(&g_xfer_in_flight, false, __ATOMIC_RELEASE);
  }
  // DEV_GONE cannot invalidate dev until submission has either succeeded or failed.
  xSemaphoreGive(g_dev_mutex);

  bool ok = false;
  if (submit_result == ESP_OK) {
    if (xSemaphoreTake(g_xfer_sem, pdMS_TO_TICKS(wait_ms)) == pdTRUE) {
      // xfer_cb publishes idle immediately after giving the semaphore.
      while (__atomic_load_n(&g_xfer_in_flight, __ATOMIC_ACQUIRE)) taskYIELD();
      if (g_xfer_result == ESP_OK && g_xfer_actual_num_bytes >= 8) {
        size_t received = (size_t)(g_xfer_actual_num_bytes - 8);
        if (received > len) received = len;
        if (received > out_capacity) received = out_capacity;
        memset(out, 0, out_capacity);
        memcpy(out, g_xfer->data_buffer + 8, received);
        if (actual_data_len) *actual_data_len = received;
        ok = true;
      }
    } else {
      __atomic_add_fetch(&g_xfer_timeout_count, 1U, __ATOMIC_RELAXED);
    }
  }

  // On timeout the persistent transfer remains allocated and marked in-flight.
  // A later callback safely returns it to idle; subsequent polls simply skip it.
  xSemaphoreGive(g_xfer_mutex);
  return ok;
}

static bool get_feature_report(uint8_t rid, uint8_t *out, uint16_t len,
                               uint32_t generation) {
  // HID GET_REPORT, report type Feature. Use the claimed interface, not a
  // hard-coded interface zero.
  uint8_t itf;
  if (xSemaphoreTake(g_dev_mutex, pdMS_TO_TICKS(100)) != pdTRUE) return false;
  if (!__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) ||
      g_dev_generation != generation) {
    xSemaphoreGive(g_dev_mutex);
    return false;
  }
  itf = g_itf;
  xSemaphoreGive(g_dev_mutex);
  return control_in(0xA1, 0x01, (uint16_t)(0x0300 | rid), itf, len,
                    generation, out, len, NULL, 300);
}

// ── Poll and decode all UPS fields ───────────────────────────────────────────
// Bitmask positions for each polled report ID
#define RID_BATTERY (1 << 0)    // 0x08
#define RID_BATCFG (1 << 1)     // 0x07
#define RID_BATVOLT (1 << 2)    // 0x0a
#define RID_INPUTV (1 << 3)     // 0x0f
#define RID_INPUTF (1 << 4)     // 0x0e
#define RID_STATUS (1 << 5)     // 0x0b
#define RID_REALPOWER (1 << 6)  // 0x19
#define RID_APPARENT (1 << 7)   // 0x1d
#define RID_REQUIRED (RID_BATTERY | RID_STATUS | RID_REALPOWER)

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
  for (uint8_t k : known_rids)
    if (k == rid) return true;
  return false;
}

// Fetch the HID report descriptor and publish its REPORT_ID values only if the
// same device generation is still active when parsing completes.
static bool parse_hid_report_descriptor(uint32_t generation) {
  uint8_t itf;
  if (xSemaphoreTake(g_dev_mutex, pdMS_TO_TICKS(100)) != pdTRUE) return false;
  if (!__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) ||
      g_dev_generation != generation) {
    xSemaphoreGive(g_dev_mutex);
    return false;
  }
  itf = g_itf;
  xSemaphoreGive(g_dev_mutex);

  uint8_t desc_buf[USB_CTRL_MAX_DATA] = {};
  size_t desc_len = 0;
  if (!control_in(0x81, 0x06, 0x2200, itf, sizeof(desc_buf), generation,
                  desc_buf, sizeof(desc_buf), &desc_len, 600) || desc_len == 0)
    return false;

  uint8_t parsed_rids[64];
  uint8_t parsed_count = 0;
  size_t i = 0;
  while (i < desc_len && parsed_count < sizeof(parsed_rids)) {
    uint8_t prefix = desc_buf[i];
    if (prefix == 0xFE) {
      if (i + 2 >= desc_len) break;
      size_t item_len = 3U + desc_buf[i + 1];
      if (item_len > desc_len - i) break;
      i += item_len;
      continue;
    }
    uint8_t sz = prefix & 0x03;
    if (sz == 3) sz = 4;
    if ((size_t)sz + 1U > desc_len - i) break;
    if (prefix == 0x85 && sz == 1) parsed_rids[parsed_count++] = desc_buf[i + 1];
    i += 1U + sz;
  }

  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  bool current = __atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) &&
                 g_dev_generation == generation;
  if (current) {
    memcpy(g_desc_rids, parsed_rids, parsed_count);
    g_desc_rid_count = parsed_count;
  }
  xSemaphoreGive(g_dev_mutex);
  return current;
}

static void poll_ups() {
  uint32_t generation;
  bool scan_done;
  uint8_t desc_rids[64];
  uint8_t desc_rid_count;

  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  if (!__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) || !g_dev) {
    xSemaphoreGive(g_dev_mutex);
    return;
  }
  generation = g_dev_generation;
  scan_done = g_rid_scan_done;
  desc_rid_count = g_desc_rid_count;
  memcpy(desc_rids, g_desc_rids, desc_rid_count);
  xSemaphoreGive(g_dev_mutex);

  uint8_t buf[64];
  UpsData d = {};
  d.ups_beeper_status = "unknown";
  uint32_t mask = 0;

  auto rd = [&](uint8_t rid) -> bool {
    memset(buf, 0, sizeof(buf));
    return get_feature_report(rid, buf, sizeof(buf), generation);
  };

  if (!scan_done) {
    bool descriptor_ready = desc_rid_count > 0;
    if (!descriptor_ready && parse_hid_report_descriptor(generation)) {
      xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
      if (g_dev_generation == generation) {
        desc_rid_count = g_desc_rid_count;
        memcpy(desc_rids, g_desc_rids, desc_rid_count);
        descriptor_ready = desc_rid_count > 0;
      }
      xSemaphoreGive(g_dev_mutex);
    }
    if (descriptor_ready) {
      for (uint8_t i = 0; i < desc_rid_count; i++) {
        uint8_t rid = desc_rids[i];
        if (is_known_rid(rid) || rid >= 64) continue;
        if (rd(rid)) {
          xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
          if (__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) &&
              g_dev_generation == generation) {
            g_rid_responds[rid] = true;
            g_unknown_rids[rid] = buf[1];
          }
          xSemaphoreGive(g_dev_mutex);
        }
      }
      xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
      if (__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) &&
          g_dev_generation == generation)
        g_rid_scan_done = true;
      xSemaphoreGive(g_dev_mutex);
    }
  }

  if (rd(0x08)) {
    d.battery_charge = le_uint(buf, 1, 1);
    d.battery_runtime_s = le_uint(buf, 2, 2);
    d.battery_runtime_low_s = le_uint(buf, 4, 2);
    mask |= RID_BATTERY;
  }
  if (rd(0x07)) {
    d.battery_charge_warning = le_uint(buf, 4, 1);
    d.battery_charge_low = le_uint(buf, 5, 1);
    mask |= RID_BATCFG;
  }
  if (rd(0x0a)) {
    d.battery_voltage = le_uint(buf, 1, 2) * 0.1f;
    mask |= RID_BATVOLT;
  }
  if (rd(0x1a)) d.battery_voltage_nominal = batt_volt_nom(le_uint(buf, 1, 1));
  if (rd(0x0f)) {
    d.input_voltage = le_uint(buf, 1, 2);
    mask |= RID_INPUTV;
  }
  if (rd(0x0c)) d.input_voltage_nominal = volt_nom(le_uint(buf, 1, 1));
  if (rd(0x0d)) d.input_frequency_nominal = freq_nom(le_uint(buf, 1, 1));
  if (rd(0x0e)) {
    d.input_frequency = le_uint(buf, 1, 1) * 0.5f;
    mask |= RID_INPUTF;
  }
  if (rd(0x10)) d.input_transfer_low = le_uint(buf, 1, 2);
  if (rd(0x12)) d.output_voltage = le_uint(buf, 1, 2);
  if (rd(0x13)) d.output_voltage_nominal = volt_nom(le_uint(buf, 1, 1));
  if (rd(0x14)) d.output_frequency = freq_index(le_uint(buf, 1, 1));
  if (rd(0x19)) {
    d.ups_realpower = le_uint(buf, 1, 2);
    mask |= RID_REALPOWER;
  }
  if (rd(0x18)) {
    d.ups_realpower_nominal = le_uint(buf, 1, 2);
    d.ups_load = d.ups_realpower_nominal > 0
                   ? d.ups_realpower / d.ups_realpower_nominal * 100.0f
                   : 0;
  }
  if (rd(0x1d)) {
    d.ups_apparent_power = le_uint(buf, 1, 2);
    mask |= RID_APPARENT;
  }
  if (rd(0x1b)) d.ups_beeper_status = beeper_str(le_uint(buf, 1, 1));
  if (rd(0x0b)) {
    uint8_t s = le_uint(buf, 1, 1);
    d.ups_status_raw = s;
    d.ac_present = s & (1 << 0);
    d.charging = s & (1 << 1);
    d.discharging = s & (1 << 2);
    d.low_battery = s & (1 << 3);
    d.fully_charged = s & (1 << 4);
    d.runtime_limit_expired = s & (1 << 5);
    mask |= RID_STATUS;
  }
  if (rd(0x16)) {
    uint32_t raw = le_uint(buf, 1, 2);
    d.ups_delay_shutdown_s = (raw == 0xFFFF) ? 0 : raw;
  }

  d.valid = (mask & RID_REQUIRED) == RID_REQUIRED;
  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  if (!__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) ||
      g_dev_generation != generation) {
    xSemaphoreGive(g_dev_mutex);
    return;
  }
  xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
  if (g_ups.valid && d.ac_present != g_ups.ac_present) {
    if (d.ac_present) ac_back_at = millis();
    else ac_lost_at = millis();
  }
  g_poll_ok_mask = mask;
  g_ups = d;
  g_last_poll_ok = millis();
  ac_hist_record(d.ac_present);
  xSemaphoreGive(g_ups_mutex);
  xSemaphoreGive(g_dev_mutex);
}

// ── USB host task (runs on core 0) ────────────────────────────────────────────
static void reset_rid_state_locked() {
  g_rid_scan_done = false;
  g_desc_rid_count = 0;
  memset(g_desc_rids, 0, sizeof(g_desc_rids));
  memset(g_unknown_rids, 0, sizeof(g_unknown_rids));
  memset(g_rid_responds, 0, sizeof(g_rid_responds));
}

static void close_opened_device(usb_device_handle_t dev) {
  esp_err_t err = usb_host_device_close(g_client, dev);
  if (err != ESP_OK && err != ESP_ERR_NOT_FOUND)
    log_e("USB device close failed: %s", esp_err_to_name(err));
}

static bool try_open_ups(uint8_t addr) {
  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  bool busy = g_dev != NULL || g_cleanup_pending;
  if (!busy) {
    g_usb_open_attempts++;
    g_usb_stage = USB_STAGE_OPENING;
    g_usb_last_error = ESP_OK;
  }
  xSemaphoreGive(g_dev_mutex);
  if (busy) return false;

  usb_device_handle_t dev = NULL;
  esp_err_t err = usb_host_device_open(g_client, addr, &dev);
  if (err != ESP_OK) {
    set_usb_stage(USB_STAGE_WAITING, err);
    return false;
  }

  const usb_device_desc_t *desc = NULL;
  err = usb_host_get_device_descriptor(dev, &desc);
  if (err != ESP_OK || !desc) {
    log_e("USB device descriptor failed: %s", esp_err_to_name(err));
    set_usb_stage(USB_STAGE_DESCRIPTOR_FAILED, err);
    close_opened_device(dev);
    return false;
  }
  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  g_usb_last_vid = desc->idVendor;
  g_usb_last_pid = desc->idProduct;
  xSemaphoreGive(g_dev_mutex);
  if (desc->idVendor != UPS_VID || desc->idProduct != UPS_PID) {
    set_usb_stage(USB_STAGE_WAITING, ESP_ERR_NOT_FOUND);
    close_opened_device(dev);
    return false;
  }

  const usb_config_desc_t *cfg_desc = NULL;
  err = usb_host_get_active_config_descriptor(dev, &cfg_desc);
  if (err != ESP_OK || !cfg_desc) {
    log_e("USB config descriptor failed: %s", esp_err_to_name(err));
    set_usb_stage(USB_STAGE_CONFIG_FAILED, err);
    close_opened_device(dev);
    return false;
  }

  const usb_intf_desc_t *intf = NULL;
  const usb_intf_desc_t *first_intf = NULL;
  for (uint8_t n = 0; n < cfg_desc->bNumInterfaces; n++) {
    int offset = 0;
    const usb_intf_desc_t *candidate =
      usb_parse_interface_descriptor(cfg_desc, n, 0, &offset);
    if (!candidate) continue;
    if (!first_intf) first_intf = candidate;
    if (candidate->bInterfaceClass == 0x03) {
      intf = candidate;
      break;
    }
  }
  // This known UPS worked with interface 0 before class filtering was added.
  // Prefer HID, but retain the first-interface behavior for nonconforming
  // descriptors from the exact supported VID/PID.
  if (!intf) intf = first_intf;
  if (!intf) {
    log_e("No usable interface found on UPS");
    set_usb_stage(USB_STAGE_INTERFACE_FAILED, ESP_ERR_NOT_FOUND);
    close_opened_device(dev);
    return false;
  }

  err = usb_host_interface_claim(g_client, dev, intf->bInterfaceNumber,
                                 intf->bAlternateSetting);
  if (err != ESP_OK) {
    log_e("USB interface claim failed: %s", esp_err_to_name(err));
    set_usb_stage(USB_STAGE_CLAIM_FAILED, err);
    close_opened_device(dev);
    return false;
  }

  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  g_dev = dev;
  g_itf = intf->bInterfaceNumber;
  g_usb_interface_count = cfg_desc->bNumInterfaces;
  g_usb_selected_interface = intf->bInterfaceNumber;
  g_usb_selected_class = intf->bInterfaceClass;
  g_usb_stage = USB_STAGE_READY;
  g_usb_last_error = ESP_OK;
  g_dev_generation++;
  reset_rid_state_locked();
  __atomic_store_n(&g_dev_ready, true, __ATOMIC_RELEASE);
  xSemaphoreGive(g_dev_mutex);
  return true;
}

static void mark_device_gone(usb_device_handle_t gone) {
  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  if (gone != g_dev) {
    xSemaphoreGive(g_dev_mutex);
    return;
  }
  __atomic_store_n(&g_dev_ready, false, __ATOMIC_RELEASE);
  g_usb_stage = USB_STAGE_GONE;
  g_usb_last_error = ESP_OK;
  g_dev_generation++;
  reset_rid_state_locked();
  g_cleanup_dev = g_dev;
  g_cleanup_itf = g_itf;
  g_cleanup_pending = true;

  // Keep lock order dev -> ups, matching poll_ups().
  xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
  g_ups = {};
  g_poll_ok_mask = 0;
  xSemaphoreGive(g_ups_mutex);
  xSemaphoreGive(g_dev_mutex);
}

static void process_pending_cleanup() {
  if (!g_cleanup_pending ||
      __atomic_load_n(&g_xfer_in_flight, __ATOMIC_ACQUIRE))
    return;

  set_usb_stage(USB_STAGE_CLEANUP, ESP_OK);
  esp_err_t err = usb_host_interface_release(g_client, g_cleanup_dev, g_cleanup_itf);
  if (err != ESP_OK && err != ESP_ERR_NOT_FOUND) {
    log_w("USB interface release deferred: %s", esp_err_to_name(err));
    return;
  }
  err = usb_host_device_close(g_client, g_cleanup_dev);
  if (err != ESP_OK && err != ESP_ERR_NOT_FOUND) {
    log_w("USB device close deferred: %s", esp_err_to_name(err));
    return;
  }

  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  if (g_dev == g_cleanup_dev) {
    g_dev = NULL;
    g_itf = 0;
  }
  g_cleanup_dev = NULL;
  g_cleanup_pending = false;
  g_usb_stage = USB_STAGE_WAITING;
  g_usb_last_error = ESP_OK;
  xSemaphoreGive(g_dev_mutex);
  __atomic_store_n(&g_usb_rescan_requested, true, __ATOMIC_RELEASE);
}

static void scan_for_ups() {
  uint8_t addresses[8];
  int count = 0;
  if (usb_host_device_addr_list_fill(8, addresses, &count) != ESP_OK) return;
  for (int i = 0; i < count; i++) {
    if (try_open_ups(addresses[i])) break;
  }
}

static bool usb_enum_filter_cb(const usb_device_desc_t *dev_desc,
                               uint8_t *configuration_value) {
  (void)dev_desc;
  // Arduino ESP32 3.3.12 / ESP-IDF 5.5.5 enables
  // CONFIG_USB_HOST_ENABLE_ENUM_FILTER_CALLBACK and rejects every device when
  // this callback is NULL. Arduino ESP32 3.3.10 / ESP-IDF 5.5.4 leaves the
  // feature disabled. Supplying this callback is compatible with both and
  // preserves the older default by accepting each device's first configuration.
  *configuration_value = 1;
  return true;
}

static void usb_event_cb(const usb_host_client_event_msg_t *msg, void *arg) {
  (void)arg;
  if (xQueueSend(g_usb_event_queue, msg, 0) != pdTRUE)
    __atomic_store_n(&g_usb_rescan_requested, true, __ATOMIC_RELEASE);
}

static void usb_host_task(void *arg) {
  (void)arg;
  usb_host_config_t cfg = {};
  cfg.skip_phy_setup = false;
  // Register the client before applying VBUS so an already-connected device's
  // first enumeration event cannot precede client registration.
  cfg.root_port_unpowered = true;
  cfg.intr_flags = ESP_INTR_FLAG_LEVEL1;
  cfg.enum_filter_cb = usb_enum_filter_cb;
  ESP_ERROR_CHECK(usb_host_install(&cfg));

  usb_host_client_config_t ccfg = {};
  ccfg.is_synchronous = false;
  ccfg.max_num_event_msg = 8;
  ccfg.async.client_event_callback = usb_event_cb;
  ccfg.async.callback_arg = NULL;
  ESP_ERROR_CHECK(usb_host_client_register(&ccfg, &g_client));
  ESP_ERROR_CHECK(usb_host_transfer_alloc(8 + USB_CTRL_MAX_DATA, 0, &g_xfer));
  ESP_ERROR_CHECK(usb_host_lib_set_root_port_power(true));
  set_usb_stage(USB_STAGE_WAITING, ESP_OK);

  esp_task_wdt_add(NULL);
  uint32_t last_scan = 0;
  uint32_t last_info = 0;
  while (true) {
    esp_err_t lib_result = usb_host_lib_handle_events(pdMS_TO_TICKS(10), NULL);
    esp_err_t client_result = usb_host_client_handle_events(g_client, pdMS_TO_TICKS(10));
    __atomic_store_n(&g_usb_last_lib_result, (int)lib_result, __ATOMIC_RELEASE);
    __atomic_store_n(&g_usb_last_client_result, (int)client_result, __ATOMIC_RELEASE);
    __atomic_add_fetch(&g_usb_task_loops, 1U, __ATOMIC_RELAXED);
    if (millis() - last_info >= 1000) {
      last_info = millis();
      usb_host_lib_info_t info = {};
      if (usb_host_lib_info(&info) == ESP_OK)
        __atomic_store_n(&g_usb_library_device_count, info.num_devices, __ATOMIC_RELEASE);
    }

    usb_host_client_event_msg_t event;
    while (xQueueReceive(g_usb_event_queue, &event, 0) == pdTRUE) {
      if (event.event == USB_HOST_CLIENT_EVENT_NEW_DEV) {
        xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
        g_usb_new_events++;
        xSemaphoreGive(g_dev_mutex);
        if (!try_open_ups(event.new_dev.address))
          __atomic_store_n(&g_usb_rescan_requested, true, __ATOMIC_RELEASE);
      } else if (event.event == USB_HOST_CLIENT_EVENT_DEV_GONE) {
        xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
        g_usb_gone_events++;
        xSemaphoreGive(g_dev_mutex);
        mark_device_gone(event.dev_gone.dev_hdl);
      }
    }

    process_pending_cleanup();
    bool should_scan = __atomic_exchange_n(&g_usb_rescan_requested, false, __ATOMIC_ACQ_REL);
    if ((should_scan || millis() - last_scan >= 1000) &&
        !__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE) && !g_cleanup_pending) {
      last_scan = millis();
      scan_for_ups();
    }
    esp_task_wdt_reset();
  }
}

// ── Display helpers ───────────────────────────────────────────────────────────
// Push desired state to hardware when it differs from actual
static void disp_flush() {
  if (dstate.desired_on == dstate.actual_on && memcmp(dstate.desired, dstate.actual, 4) == 0) return;
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
  uint8_t d[3] = { 0, 0, disp.encodeDigit(v % 10) };
  v /= 10;
  if (v) {
    d[1] = disp.encodeDigit(v % 10);
    v /= 10;
  }
  if (v) d[0] = disp.encodeDigit(v % 10);
  if (neg) {  // put minus in leftmost non-blank position
    for (int i = 0; i < 3; i++) {
      if (!d[i]) {
        d[i] = 0x40;
        break;
      }
    }
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
  colon_on_at = millis();  // triggers colon flash in loop

  xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
  UpsData d = g_ups;
  uint32_t snap_ac_lost = ac_lost_at;
  uint32_t snap_ac_back = ac_back_at;
  uint32_t snap_poll_mask = g_poll_ok_mask;
  xSemaphoreGive(g_ups_mutex);

  char json[1200];
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
#ifdef CH3819_WIFI_H
           ",\"bssid\":\"%s\""
#endif
#ifdef CH3819_OTA_H
           ",\"v\":\"%s\""
#endif
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
           snap_ac_lost,
           snap_ac_back,
           g_temp_c,
           g_last_poll_ok,
           (unsigned long)snap_poll_mask,
           ac_hist_pct()
#ifdef CH3819_WIFI_H
             ,
           ch3819_wifi_bssid().c_str()
#endif
#ifdef CH3819_OTA_H
             ,
           ch3819_ota_version()
#endif
  );
  server.send(200, "application/json", json);
}

static void handle_diag() {
  xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
  uint32_t snap_mask = g_poll_ok_mask;
  xSemaphoreGive(g_ups_mutex);

  // Snapshot USB and descriptor state under its actual writer mutex.
  xSemaphoreTake(g_dev_mutex, portMAX_DELAY);
  bool snap_dev_ready = __atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE);
  bool snap_dev_handle = g_dev != NULL;
  uint32_t snap_generation = g_dev_generation;
  uint8_t snap_usb_stage = g_usb_stage;
  esp_err_t snap_usb_error = g_usb_last_error;
  uint16_t snap_vid = g_usb_last_vid;
  uint16_t snap_pid = g_usb_last_pid;
  uint8_t snap_interface_count = g_usb_interface_count;
  uint8_t snap_selected_interface = g_usb_selected_interface;
  uint8_t snap_selected_class = g_usb_selected_class;
  uint32_t snap_new_events = g_usb_new_events;
  uint32_t snap_gone_events = g_usb_gone_events;
  uint32_t snap_open_attempts = g_usb_open_attempts;
  bool snap_scan_done = g_rid_scan_done;
  uint8_t snap_desc_rids[64];
  uint8_t snap_rid_count = g_desc_rid_count;
  memcpy(snap_desc_rids, g_desc_rids, snap_rid_count);
  uint8_t snap_unknown[64];
  bool snap_responds[64];
  memcpy(snap_unknown, g_unknown_rids, sizeof(snap_unknown));
  memcpy(snap_responds, g_rid_responds, sizeof(snap_responds));
  xSemaphoreGive(g_dev_mutex);

  char hex[8];
  String out;
  out.reserve(1500);
  out = "{\"poll_ok_mask\":\"0x";
  snprintf(hex, sizeof(hex), "%02lx", (unsigned long)snap_mask);
  out += hex;
  out += "\",\"usb_stage\":\"";
  out += usb_stage_str(snap_usb_stage);
  out += "\",\"usb_last_error\":\"";
  out += esp_err_to_name(snap_usb_error);
  out += "\",\"device_ready\":";
  out += snap_dev_ready ? "true" : "false";
  out += ",\"device_handle\":";
  out += snap_dev_handle ? "true" : "false";
  out += ",\"device_generation\":";
  out += snap_generation;
  out += ",\"new_device_events\":";
  out += snap_new_events;
  out += ",\"gone_device_events\":";
  out += snap_gone_events;
  out += ",\"open_attempts\":";
  out += snap_open_attempts;
  out += ",\"last_vid\":\"0x";
  snprintf(hex, sizeof(hex), "%04x", snap_vid);
  out += hex;
  out += "\",\"last_pid\":\"0x";
  snprintf(hex, sizeof(hex), "%04x", snap_pid);
  out += hex;
  out += "\",\"interface_count\":";
  out += snap_interface_count;
  out += ",\"selected_interface\":";
  out += snap_selected_interface;
  out += ",\"selected_class\":\"0x";
  snprintf(hex, sizeof(hex), "%02x", snap_selected_class);
  out += hex;
  out += "\",\"transfer_in_flight\":";
  out += __atomic_load_n(&g_xfer_in_flight, __ATOMIC_ACQUIRE) ? "true" : "false";
  out += ",\"transfer_last_submit_error\":\"";
  out += esp_err_to_name((esp_err_t)__atomic_load_n(&g_xfer_last_submit_result, __ATOMIC_ACQUIRE));
  out += "\",\"transfer_last_status\":";
  out += __atomic_load_n(&g_xfer_last_status, __ATOMIC_ACQUIRE);
  out += ",\"transfer_submits\":";
  out += __atomic_load_n(&g_xfer_submit_count, __ATOMIC_RELAXED);
  out += ",\"transfer_callbacks\":";
  out += __atomic_load_n(&g_xfer_callback_count, __ATOMIC_RELAXED);
  out += ",\"transfer_timeouts\":";
  out += __atomic_load_n(&g_xfer_timeout_count, __ATOMIC_RELAXED);
  out += ",\"usb_task_loops\":";
  out += __atomic_load_n(&g_usb_task_loops, __ATOMIC_RELAXED);
  out += ",\"usb_library_devices\":";
  out += __atomic_load_n(&g_usb_library_device_count, __ATOMIC_ACQUIRE);
  out += ",\"usb_last_library_result\":\"";
  out += esp_err_to_name((esp_err_t)__atomic_load_n(&g_usb_last_lib_result, __ATOMIC_ACQUIRE));
  out += "\",\"usb_last_client_result\":\"";
  out += esp_err_to_name((esp_err_t)__atomic_load_n(&g_usb_last_client_result, __ATOMIC_ACQUIRE));
  out += "\",\"compiled_usb_mode\":";
#ifdef ARDUINO_USB_MODE
  out += ARDUINO_USB_MODE;
#else
  out += -1;
#endif
  out += ",\"compiled_cdc_on_boot\":";
#ifdef ARDUINO_USB_CDC_ON_BOOT
  out += ARDUINO_USB_CDC_ON_BOOT;
#else
  out += -1;
#endif
  out += ",\"rid_scan_done\":";
  out += snap_scan_done ? "true" : "false";
  out += ",\"descriptor_rids\":[";
  for (uint8_t i = 0; i < snap_rid_count; i++) {
    if (i) out += ",";
    snprintf(hex, sizeof(hex), "\"0x%02x\"", snap_desc_rids[i]);
    out += hex;
  }
  out += "],\"unknown_rids\":{";
  bool first = true;
  for (uint8_t i = 0; i < 0x40; i++) {
    if (!snap_responds[i]) continue;
    if (!first) out += ",";
    first = false;
    snprintf(hex, sizeof(hex), "\"0x%02x\"", i);
    out += hex;
    out += ":";
    snprintf(hex, sizeof(hex), "%u", snap_unknown[i]);
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
  disp.setBrightness(2);
  const uint8_t seg_helo[] = { 0x76, 0x79, 0x38, 0x3F };  // HELO
  disp.setSegments(seg_helo, 4, 0);

  g_ups_mutex = xSemaphoreCreateMutex();
  g_dev_mutex = xSemaphoreCreateMutex();
  g_xfer_mutex = xSemaphoreCreateMutex();
  g_xfer_sem = xSemaphoreCreateBinary();
  g_usb_event_queue = xQueueCreate(8, sizeof(usb_host_client_event_msg_t));
  if (!g_ups_mutex || !g_dev_mutex || !g_xfer_mutex || !g_xfer_sem ||
      !g_usb_event_queue) {
    log_e("Failed to allocate synchronization primitives");
    abort();
  }

  tempSensor.begin();
  tempSensor.setWaitForConversion(false);
  if (tempSensor.getAddress(tempAddr, 0)) {
    tempFound = true;
    tempSensor.requestTemperatures();
  }

  if (xTaskCreatePinnedToCore(usb_host_task, "usb_host", 8192, NULL, 5, NULL, 0) != pdPASS) {
    log_e("Failed to create USB host task");
    abort();
  }

#ifdef CH3819_WIFI_H
  ch3819_wifi_setup(CH3819_WiFi_SSID, CH3819_WiFi_KEY, CH3819_HOSTNAME_PREFIX);
#else
  WiFi.begin(WIFI_SSID, WIFI_PASS);
#endif

#ifdef CH3819_OTA_H
  ch3819_ota_setup(CH3819_OTA_HOST, CH3819_OTA_PORT, __DATE__, __TIME__, "ups-monitor", 3600000, nullptr);
#endif

  server.on("/ups", handle_ups);
  server.on("/diag", handle_diag);
  server.begin();
}

void loop() {

#ifdef CH3819_WIFI_H
  ch3819_wifi_loop();
#else
  // WiFi reconnect: retry every 60s when disconnected
  static uint32_t last_wifi_try = 0;
  if (WiFi.status() != WL_CONNECTED && millis() - last_wifi_try >= 60000) {
    last_wifi_try = millis();
    WiFi.disconnect();
    WiFi.begin(WIFI_SSID, WIFI_PASS);
  }
#endif

#ifdef CH3819_OTA_H
  ch3819_ota_loop();
#endif

  server.handleClient();

  // Poll UPS every 1s; clear data if stale for 20s
  static uint32_t last_poll = 0;
  if (millis() - last_poll >= 1000) {
    last_poll = millis();
    if (__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE)) poll_ups();
  }
  if (g_last_poll_ok && millis() - g_last_poll_ok > 20000) {
    xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
    if (g_ups.valid) g_ups = {};
    xSemaphoreGive(g_ups_mutex);
  }

  // DS18B20: Request temperatures. Check for conversion in each loop after the request and update g_temp_c when conversion has completed.
  // Wait 10s before requesting temperatures again.
  static bool tempRequested = true;  // already requested in setup()
  static uint32_t last_temp = 0;
  if (tempFound && millis() - last_temp >= 10000) {
    if (tempRequested && tempSensor.isConversionComplete()) {
      float t = tempSensor.getTempC(tempAddr);
      if (t != DEVICE_DISCONNECTED_C) g_temp_c = t;
      last_temp = millis();
      tempRequested = false;
    }
    if (!tempRequested) {
      tempSensor.requestTemperatures();
      tempRequested = true;
    }
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
  static uint32_t last_disp_refresh = 0;
  static uint32_t phase = 0;

  if (millis() - disp_start > 2160) {
    disp_start = millis();
    phase++;
    if (phase > 99) phase = 0;
  }

  if (millis() - last_disp_refresh > 360) {
    last_disp_refresh = millis();

    xSemaphoreTake(g_ups_mutex, portMAX_DELAY);
    UpsData d = g_ups;
    xSemaphoreGive(g_ups_mutex);

    // Segment encodings
    const uint8_t seg_ups[] = { 0x3E, 0x73, 0x6D, 0x00 };
    const uint8_t ip_ind[] = { 0x01, 0x09, 0x49, 0x63 };
    const uint8_t seg_usb[] = { 0x00, 0x3E, 0x6D, 0x7C };
    const uint8_t seg_err[] = { 0x00, 0x79, 0x50, 0x50 };
    //const uint8_t seg_none[] = { 0x37, 0x3F, 0x37, 0x79 };

    bool wifi_ok = WiFi.status() == WL_CONNECTED;

    switch (phase) {
      case 0:
        {
          if (__atomic_load_n(&g_dev_ready, __ATOMIC_ACQUIRE)) {
            show_word(seg_ups);
          } else {
            show_word((millis() / 400) % 2 ? seg_err : seg_usb);
          }
          break;
        }
      case 1:
        if (d.valid) show_metric(SEG_VOLT, (int)(d.battery_voltage * 10));
        else {
          disp_off();
          phase += 2;
        }
        break;
      case 2: disp_off(); break;
      case 3:
        if (d.valid) show_metric(SEG_WATT, (int)d.ups_realpower);
        else {
          disp_off();
          phase += 2;
        }
        break;
      case 4: disp_off(); break;
      case 5:
        if (g_temp_c > -127.0) show_metric(SEG_TEMP, (int)(g_temp_c * 10));
        else {
          disp_off();
          phase += 2;
        }
        break;
      case 6: disp_off(); break;
      case 7:
        if (wifi_ok) show_metric(SEG_RSSI, WiFi.RSSI());
        else {
          disp_off();
          phase += 2;
        }
        break;
      case 8: disp_off(); break;
      case 9:  // fall through
      case 10:
      case 11:
      case 12:
        {
          int i = (phase - 9) % 4;
          if (wifi_ok) show_metric(ip_ind[i], WiFi.localIP()[i]);
          else {
            const uint8_t no_wifi[] = { ip_ind[i], 0x10, 0x10, 0x10 };
            show_word(no_wifi);
          }
        }
        break;
      case 13: disp_off(); break;
      case 14:
        phase = 0;
        break;
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

  if (millis() > 4000) disp_flush();

  if (millis() - took_a_break_at > 5) {
    delay(1);
    took_a_break_at = millis();
  }
}

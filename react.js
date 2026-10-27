/* ============================================================
   Thời gian biểu cá nhân — toàn bộ logic ứng dụng (React 18 + Babel)
   ============================================================ */
const { useState, useEffect, useRef, useMemo, useCallback } = React;

/* ---------- Hằng số ---------- */
const STORAGE_KEY = 'tp_data_v1';
const NOTIFIED_KEY = 'tp_notified_v1';
const DIRTY_KEY = 'tp_sync_dirty';
const HOUR_H = 56;               // chiều cao 1 giờ trên lưới (px) — khớp --hour-h trong font.css
const SYNC_HORIZON_DAYS = 120;   // số ngày tới được gửi lên Apps Script
const MAX_RANGE_DAYS = 366;      // khoảng lặp tối đa
const NOTIFIED_TTL_MS = 7 * 24 * 3600 * 1000;
const TOMBSTONE_TTL_MS = 90 * 24 * 3600 * 1000; // giữ dấu xóa 90 ngày để thiết bị khác xóa theo
const POLL_MS = 120000;                         // tự tải lịch từ máy chủ mỗi 2 phút

const WEEKDAYS = ['T2', 'T3', 'T4', 'T5', 'T6', 'T7', 'CN'];
const WEEKDAYS_LONG = ['Thứ 2', 'Thứ 3', 'Thứ 4', 'Thứ 5', 'Thứ 6', 'Thứ 7', 'Chủ nhật'];
const CATEGORIES = [
  { id: 'study', label: 'Học tập' },
  { id: 'work', label: 'Công việc' },
  { id: 'personal', label: 'Cá nhân' },
  { id: 'health', label: 'Sức khỏe' },
  { id: 'other', label: 'Khác' },
];
const CAT_IDS = CATEGORIES.map((c) => c.id);
const catLabel = (id) => (CATEGORIES.find((c) => c.id === id) || CATEGORIES[4]).label;
const REMIND_OPTIONS = [
  { v: 0, l: 'Không nhắc' }, { v: 5, l: '5 phút' }, { v: 10, l: '10 phút' }, { v: 15, l: '15 phút' },
  { v: 30, l: '30 phút' }, { v: 60, l: '1 tiếng' }, { v: 120, l: '2 tiếng' }, { v: 1440, l: '1 ngày' },
];
const HOUR_OPTIONS = {
  '6-23': { label: '06:00 - 23:00', start: 6, end: 24 },
  '0-23': { label: '00:00 - 23:00 (24h)', start: 0, end: 24 },
};

const DEFAULT_SETTINGS = {
  hours: '6-23', theme: null, soundOn: true, volume: 0.7, notifyOn: false,
  syncEnabled: false, syncUrl: '', syncToken: '', lastSync: null,
  taskSpeak: true, taskPhrase: 'Đến giờ {ghi chú} rồi cậu chủ ơi',
};

/* ---------- Tiện ích ngày giờ (giờ địa phương) ---------- */
const pad = (n) => String(n).padStart(2, '0');
const toISODate = (d) => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
const parseISODate = (s) => { const [y, m, d] = s.split('-').map(Number); return new Date(y, m - 1, d); };
const startOfDay = (d) => new Date(d.getFullYear(), d.getMonth(), d.getDate());
const addDays = (d, n) => new Date(d.getFullYear(), d.getMonth(), d.getDate() + n);
const wdIndex = (d) => (d.getDay() + 6) % 7; // 0 = Thứ 2 ... 6 = Chủ nhật
const startOfWeek = (d) => addDays(d, -wdIndex(d));
const addMonths = (d, n) => {
  const x = new Date(d.getFullYear(), d.getMonth() + n, 1);
  const last = new Date(x.getFullYear(), x.getMonth() + 1, 0).getDate();
  x.setDate(Math.min(d.getDate(), last));
  return x;
};
const daysBetween = (a, b) => Math.round((parseISODate(b) - parseISODate(a)) / 86400000);
const timeToMin = (t) => { const [h, m] = t.split(':').map(Number); return h * 60 + m; };
const minToTime = (m) => `${pad(Math.floor(m / 60))}:${pad(m % 60)}`;
const dateTimeMs = (iso, time) => {
  const [y, mo, d] = iso.split('-').map(Number);
  const [h, mi] = time.split(':').map(Number);
  return new Date(y, mo - 1, d, h, mi, 0, 0).getTime();
};
const fmtDM = (iso) => `${iso.slice(8, 10)}/${iso.slice(5, 7)}`;
const fmtDMY = (iso) => `${fmtDM(iso)}/${iso.slice(0, 4)}`;
const fmtClock = (ms) => { const d = new Date(ms); return `${pad(d.getHours())}:${pad(d.getMinutes())}`; };
const fold = (s) => s.normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/đ/g, 'd').replace(/Đ/g, 'D').toLowerCase();
const uid = () =>
  (window.crypto && crypto.randomUUID) ? crypto.randomUUID()
    : 'id-' + Date.now().toString(36) + Math.random().toString(36).slice(2, 10);
const tzOffsetStr = () => {
  const off = -new Date().getTimezoneOffset();
  const a = Math.abs(off);
  return `${off >= 0 ? '+' : '-'}${pad(Math.floor(a / 60))}:${pad(a % 60)}`;
};

/* ---------- Kiểm tra và làm sạch dữ liệu ---------- */
const RE_DATE = /^\d{4}-\d{2}-\d{2}$/;
const RE_TIME = /^([01]\d|2[0-3]):[0-5]\d$/;
const validDateStr = (s) => typeof s === 'string' && RE_DATE.test(s) && toISODate(parseISODate(s)) === s;

const NOTE_MAX = 500; // số ký tự tối đa của một ghi chú
const HOUR_MS = 3600000;
// Việc cần làm không có giờ kết thúc: lưu giờ kết thúc ảo (+30 phút) để dữ liệu vẫn hợp lệ
const taskEnd = (start) => minToTime(Math.min(timeToMin(start) + 30, 1439));
const SHORTCUTS = [
  [['←'], 'Kỳ trước (ngày, tuần hoặc tháng, theo chế độ đang xem)'],
  [['→'], 'Kỳ sau'],
  [['T'], 'Về hôm nay'],
  [['D'], 'Xem theo ngày'],
  [['W'], 'Xem theo tuần'],
  [['M'], 'Xem theo tháng'],
  [['N'], 'Thêm sự kiện (hoặc thêm việc khi đang ở trang Việc cần làm)'],
  [['?'], 'Mở bảng phím tắt này'],
  [['Esc'], 'Đóng hộp thoại (hoặc hủy khi đang kéo thẻ)'],
];

// Ghi chú theo từng buổi: { 'YYYY-MM-DD': { v: 'nội dung', t: thời điểm sửa } }
function sanitizeNotes(raw) {
  const out = {};
  if (!raw || typeof raw !== 'object') return out;
  Object.keys(raw).forEach((k) => {
    const x = raw[k];
    if (validDateStr(k) && x && typeof x.v === 'string' && Number.isFinite(x.t)) out[k] = { v: x.v.slice(0, NOTE_MAX), t: x.t };
  });
  return out;
}

// Dấu "đã làm" theo từng ngày: { 'YYYY-MM-DD': { v: true/false, t: thời điểm bấm } }
function sanitizeDone(raw) {
  const out = {};
  if (!raw || typeof raw !== 'object') return out;
  Object.keys(raw).forEach((k) => {
    const x = raw[k];
    if (validDateStr(k) && x && typeof x.v === 'boolean' && Number.isFinite(x.t)) out[k] = { v: x.v, t: x.t };
  });
  return out;
}

function sanitizeOverride(o) {
  if (!o || typeof o !== 'object') return null;
  const title = typeof o.title === 'string' ? o.title.trim().slice(0, 120) : '';
  if (!title || !RE_TIME.test(o.startTime) || !RE_TIME.test(o.endTime)) return null;
  if (timeToMin(o.endTime) <= timeToMin(o.startTime)) return null;
  return {
    title,
    category: CAT_IDS.includes(o.category) ? o.category : 'other',
    startTime: o.startTime,
    endTime: o.endTime,
    remindMin: Number.isFinite(o.remindMin) && o.remindMin >= 0 && o.remindMin <= 10080 ? Math.round(o.remindMin) : 0,
  };
}

// Trả về { event } nếu hợp lệ, ngược lại { error }
function sanitizeEvent(raw) {
  if (!raw || typeof raw !== 'object') return { error: 'không phải đối tượng' };
  const title = typeof raw.title === 'string' ? raw.title.trim().slice(0, 120) : '';
  if (!title) return { error: 'thiếu tiêu đề' };
  const isTask = raw.task === true;
  if (!RE_TIME.test(raw.startTime)) return { error: 'giờ không hợp lệ' };
  const endRaw = isTask ? taskEnd(raw.startTime) : raw.endTime;
  if (!RE_TIME.test(endRaw)) return { error: 'giờ không hợp lệ' };
  if (!isTask && timeToMin(endRaw) <= timeToMin(raw.startTime)) return { error: 'giờ kết thúc phải sau giờ bắt đầu' };
  const ev = {
    id: typeof raw.id === 'string' && raw.id ? raw.id.slice(0, 64) : uid(),
    title,
    category: CAT_IDS.includes(raw.category) ? raw.category : 'other',
    startTime: raw.startTime,
    endTime: endRaw,
    remindMin: Number.isFinite(raw.remindMin) && raw.remindMin >= 0 && raw.remindMin <= 10080 ? Math.round(raw.remindMin) : 0,
    kind: raw.kind,
    exceptions: {},
    done: sanitizeDone(raw.done),
    notes: sanitizeNotes(raw.notes),
    updatedAt: Number.isFinite(raw.updatedAt) ? raw.updatedAt : Date.now(),
  };
  if (isTask) {
    if (raw.kind !== 'once') return { error: 'việc cần làm chỉ có kiểu một lần' };
    ev.task = true;
    ev.remindMin = 0;
    ev.repeatMode = raw.repeatMode === 'eod' ? 'eod' : 'times';
    ev.repeatN = raw.repeatN === 3 ? 3 : 2;
  }
  if (raw.kind === 'once') {
    if (!validDateStr(raw.date)) return { error: 'ngày không hợp lệ' };
    ev.date = raw.date;
  } else if (raw.kind === 'weekly') {
    const wd = Array.isArray(raw.weekdays)
      ? [...new Set(raw.weekdays.filter((n) => Number.isInteger(n) && n >= 0 && n <= 6))].sort((a, b) => a - b) : [];
    if (!wd.length) return { error: 'chưa chọn thứ trong tuần' };
    if (!validDateStr(raw.rangeStart) || !validDateStr(raw.rangeEnd) || raw.rangeEnd < raw.rangeStart) {
      return { error: 'khoảng ngày lặp không hợp lệ' };
    }
    ev.weekdays = wd;
    ev.rangeStart = raw.rangeStart;
    ev.rangeEnd = raw.rangeEnd;
    if (raw.exceptions && typeof raw.exceptions === 'object') {
      Object.keys(raw.exceptions).forEach((k) => {
        if (!validDateStr(k)) return;
        const v = raw.exceptions[k];
        if (v === 'deleted') ev.exceptions[k] = 'deleted';
        else { const o = sanitizeOverride(v); if (o) ev.exceptions[k] = o; }
      });
    }
  } else return { error: 'kiểu sự kiện không hợp lệ' };
  return { event: ev };
}

function migrateData(p) {
  const events = Array.isArray(p && p.events)
    ? p.events.map(sanitizeEvent).filter((r) => r.event).map((r) => r.event) : [];
  const st = { ...DEFAULT_SETTINGS, ...(p && p.settings && typeof p.settings === 'object' ? p.settings : {}) };
  if (!HOUR_OPTIONS[st.hours]) st.hours = '6-23';
  if (st.theme !== 'light' && st.theme !== 'dark') st.theme = null;
  st.soundOn = st.soundOn !== false;
  st.notifyOn = st.notifyOn === true;
  st.volume = Number.isFinite(st.volume) ? Math.min(1, Math.max(0, st.volume)) : 0.7;
  st.syncEnabled = st.syncEnabled === true;
  st.syncUrl = typeof st.syncUrl === 'string' ? st.syncUrl : '';
  st.syncToken = typeof st.syncToken === 'string' ? st.syncToken : '';
  st.lastSync = Number.isFinite(st.lastSync) ? st.lastSync : null;
  st.taskSpeak = st.taskSpeak !== false;
  st.taskPhrase = typeof st.taskPhrase === 'string' ? st.taskPhrase.slice(0, 120) : DEFAULT_SETTINGS.taskPhrase;
  const tombstones = {};
  if (p && p.tombstones && typeof p.tombstones === 'object') {
    Object.keys(p.tombstones).forEach((k) => {
      const v = Number(p.tombstones[k]);
      if (k && k.length <= 64 && Number.isFinite(v) && v > Date.now() - TOMBSTONE_TTL_MS) tombstones[k] = v;
    });
  }
  return { version: 1, updatedAt: Number(p && p.updatedAt) || 0, events, tombstones, settings: st };
}

function loadData() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (raw) return migrateData(JSON.parse(raw));
  } catch (e) { console.warn('Không đọc được dữ liệu đã lưu', e); }
  return { version: 1, updatedAt: 0, events: [], tombstones: {}, settings: { ...DEFAULT_SETTINGS } };
}

function loadNotified() {
  try { return JSON.parse(localStorage.getItem(NOTIFIED_KEY) || '{}') || {}; } catch (e) { return {}; }
}
function saveNotified(map) {
  const cutoff = Date.now() - NOTIFIED_TTL_MS;
  Object.keys(map).forEach((k) => { if (map[k] < cutoff) delete map[k]; });
  try { localStorage.setItem(NOTIFIED_KEY, JSON.stringify(map)); } catch (e) { /* bỏ qua */ }
}

/* ---------- Đồng bộ nhiều thiết bị: gộp theo từng sự kiện ---------- */
// Mỗi sự kiện có thời điểm sửa (updatedAt); sự kiện bị xóa để lại "dấu xóa" cùng thời điểm xóa.
// Với mỗi id, bản có thời điểm lớn hơn thắng. Bằng nhau thì giữ bản trên máy này.
function toRemoteSeries(d) {
  const out = d.events.map((ev) => ({ id: ev.id, ts: ev.updatedAt, deleted: false, data: ev }));
  Object.keys(d.tombstones || {}).forEach((id) => out.push({ id, ts: d.tombstones[id], deleted: true }));
  return out;
}

function mergeDone(a, b) {
  const out = { ...(a || {}) };
  Object.keys(b || {}).forEach((k) => { if (!out[k] || b[k].t > out[k].t) out[k] = b[k]; });
  return out;
}
function sameDone(a, b) {
  const ka = Object.keys(a || {});
  const kb = Object.keys(b || {});
  return ka.length === kb.length && ka.every((k) => b[k] && b[k].v === a[k].v && b[k].t === a[k].t);
}

function mergeRemote(local, remoteList) {
  const best = new Map(); // id -> { ts, dead, ev }
  local.events.forEach((ev) => best.set(ev.id, { ts: ev.updatedAt, dead: false, ev }));
  Object.keys(local.tombstones || {}).forEach((id) => {
    const ts = local.tombstones[id];
    const cur = best.get(id);
    if (!cur || ts > cur.ts) best.set(id, { ts, dead: true, ev: null });
  });
  const cutoff = Date.now() - TOMBSTONE_TTL_MS;
  let changedEvents = false;
  let changedTomb = false;
  (Array.isArray(remoteList) ? remoteList : []).forEach((r) => {
    if (!r || typeof r.id !== 'string' || !r.id || r.id.length > 64) return;
    const ts = Number(r.ts);
    if (!Number.isFinite(ts)) return;
    const cur = best.get(r.id);
    if (cur && !cur.dead && !r.deleted) {
      // Cùng một sự kiện ở cả hai nơi: nội dung theo bản mới hơn, dấu "đã làm" gộp theo từng ngày
      const r0 = sanitizeEvent({ ...(r.data && typeof r.data === 'object' ? r.data : {}), id: r.id, updatedAt: ts });
      if (!r0.event) return;
      const remoteWins = ts > cur.ts;
      const doneM = mergeDone(cur.ev.done, r0.event.done);
      const notesM = mergeDone(cur.ev.notes, r0.event.notes);
      const diffRemote = !sameDone(doneM, r0.event.done) || !sameDone(notesM, r0.event.notes);
      const diffLocal = !sameDone(doneM, cur.ev.done) || !sameDone(notesM, cur.ev.notes);
      if (!remoteWins && !diffLocal) return;
      const out = { ...(remoteWins ? r0.event : cur.ev), done: doneM, notes: notesM };
      if (diffRemote) out.updatedAt = Date.now(); // máy chủ thiếu vài dấu tích: đẩy bản đầy đủ lên
      best.set(r.id, { ts: out.updatedAt, dead: false, ev: out });
      changedEvents = true;
      return;
    }
    if (cur && cur.ts >= ts) return;
    if (r.deleted) {
      if (ts < cutoff) return;
      if (cur && !cur.dead) changedEvents = true;
      best.set(r.id, { ts, dead: true, ev: null });
      changedTomb = true;
    } else {
      const res = sanitizeEvent({ ...(r.data && typeof r.data === 'object' ? r.data : {}), id: r.id, updatedAt: ts });
      if (!res.event) return;
      if (cur && cur.dead) changedTomb = true;
      best.set(r.id, { ts, dead: false, ev: res.event });
      changedEvents = true;
    }
  });
  if (!changedEvents && !changedTomb) return { changed: false };
  const events = [];
  const tombstones = {};
  best.forEach((v, id) => {
    if (v.dead) { if (v.ts >= cutoff) tombstones[id] = v.ts; } else events.push(v.ev);
  });
  return { changed: true, events: changedEvents ? events : local.events, tombstones };
}

/* ---------- Mở rộng chuỗi sự kiện thành các buổi cụ thể ---------- */
// fromD, toD: đối tượng Date (bao gồm cả hai đầu)
function occurrencesInRange(s, fromD, toD) {
  const out = [];
  const fromISO = toISODate(fromD);
  const toISO = toISODate(toD);
  const push = (iso) => {
    const ex = s.exceptions && s.exceptions[iso];
    if (ex === 'deleted') return;
    const o = ex && typeof ex === 'object' ? ex : null;
    out.push({
      key: `${s.id}|${iso}`, seriesId: s.id, date: iso, kind: s.kind,
      title: o ? o.title : s.title, category: o ? o.category : s.category,
      startTime: o ? o.startTime : s.startTime, endTime: o ? o.endTime : s.endTime,
      remindMin: o ? o.remindMin : s.remindMin, overridden: !!o,
      done: !!(s.done && s.done[iso] && s.done[iso].v),
      note: (s.notes && s.notes[iso] && s.notes[iso].v) || '',
    });
  };
  if (s.kind === 'once') {
    if (s.date >= fromISO && s.date <= toISO) push(s.date);
    return out;
  }
  const a = s.rangeStart > fromISO ? s.rangeStart : fromISO;
  const b = s.rangeEnd < toISO ? s.rangeEnd : toISO;
  if (a > b) return out;
  for (let d = parseISODate(a); toISODate(d) <= b; d = addDays(d, 1)) {
    if (s.weekdays.includes(wdIndex(d))) push(toISODate(d));
  }
  return out;
}

// Xếp các buổi trong một ngày thành các cột để không đè lên nhau
function layoutDay(items) {
  const sorted = [...items].sort((a, b) => a.s - b.s || a.e - b.e);
  const res = [];
  let cluster = [];
  let clusterEnd = -1;
  const flush = () => {
    if (!cluster.length) return;
    const cols = [];
    cluster.forEach((it) => {
      let ci = cols.findIndex((end) => end <= it.s);
      if (ci === -1) { cols.push(it.e); ci = cols.length - 1; } else cols[ci] = it.e;
      it.col = ci;
    });
    cluster.forEach((it) => { it.cols = cols.length; res.push(it); });
    cluster = [];
  };
  sorted.forEach((it) => {
    if (cluster.length && it.s >= clusterEnd) { flush(); clusterEnd = -1; }
    cluster.push(it);
    clusterEnd = Math.max(clusterEnd, it.e);
  });
  flush();
  return res;
}

function describeSeries(s) {
  const t = `${s.startTime}–${s.endTime}`;
  if (s.kind === 'once') return `${fmtDMY(s.date)} · ${t}`;
  const days = s.weekdays.length === 7 ? 'Hằng ngày' : s.weekdays.map((i) => WEEKDAYS[i]).join(', ');
  return `${days} · ${t} · ${fmtDMY(s.rangeStart)} → ${fmtDMY(s.rangeEnd)}`;
}

/* ---------- Việc cần làm (có giờ bắt đầu, không có giờ kết thúc) ---------- */
const isTask = (s) => !!s && s.task === true;
// Số thứ tự lần nhắc cuối (0 = chỉ nhắc đúng giờ). Nhắc lần k vào lúc bắt đầu + k giờ.
function taskLastK(s) {
  if (s.repeatMode === 'eod') {
    const endOfDay = dateTimeMs(toISODate(addDays(parseISODate(s.date), 1)), '00:00');
    return Math.max(0, Math.floor((endOfDay - 1 - dateTimeMs(s.date, s.startTime)) / HOUR_MS));
  }
  return (s.repeatN === 3 ? 3 : 2) - 1;
}
const taskNote = (s) => (s.notes && s.notes[s.date] && s.notes[s.date].v) || '';
const taskDone = (s) => (s.done && s.done[s.date] && s.done[s.date].v ? s.done[s.date] : null);
// Điền {ghi chú} (trống thì dùng tiêu đề) và {tên} vào câu nhắc
function fillPhrase(tpl, s) {
  const t = (tpl && tpl.trim()) || DEFAULT_SETTINGS.taskPhrase;
  return t.replace(/\{\s*ghi\s*ch[úu]\s*\}/gi, () => taskNote(s) || s.title)
    .replace(/\{\s*t[êe]n\s*\}/gi, () => s.title);
}
// Chọn giọng tiếng Việt nữ: trình duyệt không cho biết giới tính nên đoán theo tên giọng
// (Microsoft HoaiMy, Apple Linh, Google tiếng Việt đều là giọng nữ; NamMinh là giọng nam)
function pickFemaleVoice() {
  const vi = window.speechSynthesis.getVoices().filter((x) => /^vi/i.test(x.lang));
  const female = /hoaimy|hoai my|linh|google|female|nữ|nu\b/i;
  const male = /namminh|nam minh|\bmale\b|nam\b/i;
  return vi.find((x) => female.test(x.name) && !male.test(x.name)) || vi.find((x) => !male.test(x.name)) || vi[0] || null;
}
if ('speechSynthesis' in window) { try { window.speechSynthesis.getVoices(); } catch (e) { /* bỏ qua */ } }
function speakText(text, volume) {
  try {
    if (!('speechSynthesis' in window) || typeof SpeechSynthesisUtterance === 'undefined') return;
    const u = new SpeechSynthesisUtterance(text);
    u.lang = 'vi-VN';
    u.volume = Math.min(1, Math.max(0, volume));
    u.pitch = 1.15; // cao hơn một chút cho giọng nữ rõ hơn
    const v = pickFemaleVoice();
    if (v) u.voice = v;
    window.speechSynthesis.cancel();
    window.speechSynthesis.speak(u);
  } catch (e) { /* bỏ qua */ }
}

/* ---------- Dữ liệu nhắc gửi lên Apps Script ---------- */
function buildReminderPayload(events) {
  const from = startOfDay(new Date());
  const to = addDays(from, SYNC_HORIZON_DAYS);
  const tz = tzOffsetStr();
  const out = [];
  events.forEach((s) => {
    if (isTask(s)) return; // việc cần làm chỉ nhắc khi mở tab
    occurrencesInRange(s, from, to).forEach((o) => {
      if (o.remindMin > 0 && !o.done) {
        out.push({ id: s.id, title: o.title, startISO: `${o.date}T${o.startTime}:00${tz}`, remindMin: o.remindMin });
      }
    });
  });
  return out;
}

async function postToScript(url, payload) {
  let res;
  try {
    // text/plain để tránh preflight CORS (Apps Script không xử lý OPTIONS)
    res = await fetch(url, {
      method: 'POST',
      headers: { 'Content-Type': 'text/plain;charset=utf-8' },
      body: JSON.stringify(payload),
    });
  } catch (e) {
    throw new Error('Không kết nối được máy chủ. Kiểm tra mạng và URL Web App.');
  }
  const text = await res.text();
  try { return JSON.parse(text); } catch (e) {
    throw new Error('Phản hồi không hợp lệ. Kiểm tra URL Web App và quyền truy cập "Anyone".');
  }
}

/* ---------- Âm thanh chuông (Web Audio API, không cần file ngoài) ---------- */
const AudioEngine = {
  ctx: null,
  ensure() {
    if (!this.ctx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return null;
      this.ctx = new AC();
    }
    if (this.ctx.state === 'suspended') this.ctx.resume();
    return this.ctx;
  },
  chime(volume) {
    const ctx = this.ensure();
    if (!ctx) return;
    const v = Math.min(1, Math.max(0, volume));
    const now = ctx.currentTime;
    [880, 1318.5, 1760].forEach((freq, i) => {
      const osc = ctx.createOscillator();
      const gain = ctx.createGain();
      const t = now + i * 0.18;
      osc.type = 'sine';
      osc.frequency.value = freq;
      gain.gain.setValueAtTime(0.0001, t);
      gain.gain.exponentialRampToValueAtTime(Math.max(0.0002, v * 0.35), t + 0.02);
      gain.gain.exponentialRampToValueAtTime(0.0001, t + 1.0);
      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start(t);
      osc.stop(t + 1.05);
    });
  },
};

function showDesktopNotification(title, body, tag) {
  if (!('Notification' in window) || Notification.permission !== 'granted') return;
  try { new Notification(title, { body, tag }); } catch (e) { /* một số trình duyệt di động không cho tạo trực tiếp */ }
}

const getPerm = () => ('Notification' in window ? Notification.permission : 'unsupported');

/* ============================================================
   Component: Icon (Lucide qua CDN, tự dựng SVG, không cần createIcons)
   ============================================================ */
const ICON_ALIASES = {
  TriangleAlert: ['TriangleAlert', 'AlertTriangle'],
  CalendarDays: ['CalendarDays', 'Calendar'],
  Trash2: ['Trash2', 'Trash'],
  ListTodo: ['ListTodo', 'ListChecks', 'List'],
};
function Icon({ name, size = 18, className = '' }) {
  const lib = window.lucide;
  let node = null;
  if (lib && lib.icons) {
    const names = ICON_ALIASES[name] || [name];
    for (const n of names) { if (lib.icons[n]) { node = lib.icons[n]; break; } }
  }
  if (!node) return <span className={`icon-fallback ${className}`} style={{ width: size, height: size }} aria-hidden="true" />;
  // Định dạng cũ: ['svg', attrs, children]; định dạng mới: [[tag, attrs], ...]
  const children = typeof node[0] === 'string' ? node[2] : node;
  return (
    <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width={size} height={size} fill="none"
      stroke="currentColor" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round"
      className={className} aria-hidden="true" focusable="false">
      {children.map((child, i) => {
        const attrs = { ...(child[1] || {}) };
        delete attrs.key;
        return React.createElement(child[0], { key: i, ...attrs });
      })}
    </svg>
  );
}

/* Logo RICO: lịch có dấu tick và góc gấp xanh nhạt (SVG tự vẽ) */
let logoSeq = 0;
function Logo({ size = 36 }) {
  const id = useMemo(() => { logoSeq += 1; return `rico${logoSeq}`; }, []);
  return (
    <svg className="logo-svg" viewBox="0 0 64 64" width={size} height={size} aria-hidden="true" focusable="false">
      <defs>
        <linearGradient id={`${id}a`} x1="8" y1="12" x2="56" y2="62" gradientUnits="userSpaceOnUse">
          <stop offset="0" stopColor="#2f80ff" /><stop offset="1" stopColor="#3a46dc" />
        </linearGradient>
        <linearGradient id={`${id}b`} x1="40" y1="40" x2="60" y2="60" gradientUnits="userSpaceOnUse">
          <stop offset="0" stopColor="#8adbff" /><stop offset="1" stopColor="#4fb4f7" />
        </linearGradient>
      </defs>
      <rect x="17" y="3" width="7" height="16" rx="3.5" fill="#2a6cf0" />
      <rect x="40" y="3" width="7" height="16" rx="3.5" fill="#2a6cf0" />
      <rect x="4" y="11" width="56" height="49" rx="12" fill={`url(#${id}a)`} />
      <path d="M4 28 H60" stroke="#fff" strokeOpacity=".3" strokeWidth="2" />
      <path d="M60 39 A21 21 0 0 0 39 60 H48 A12 12 0 0 0 60 48 Z" fill={`url(#${id}b)`} />
      <path d="M19 42 l8.5 8.5 L44 33" fill="none" stroke="#fff" strokeWidth="6.5" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  );
}

/* ============================================================
   Component: Dialog (Esc đóng, giữ focus trong hộp thoại)
   ============================================================ */
function Dialog({ title, onClose, children, wide }) {
  const ref = useRef(null);
  const closeRef = useRef(onClose);
  closeRef.current = onClose;
  const titleId = React.useId();

  useEffect(() => {
    const prev = document.activeElement;
    const el = ref.current;
    const sel = 'button:not([disabled]), [href], input:not([disabled]), select:not([disabled]), textarea:not([disabled])';
    const first = el.querySelector('[data-autofocus]') || el.querySelector(sel);
    if (first) first.focus();
    const onKey = (e) => {
      if (e.key === 'Escape') { e.stopPropagation(); closeRef.current(); return; }
      if (e.key !== 'Tab') return;
      const items = [...el.querySelectorAll(sel)];
      if (!items.length) return;
      const a = items[0];
      const z = items[items.length - 1];
      if (e.shiftKey && document.activeElement === a) { e.preventDefault(); z.focus(); }
      else if (!e.shiftKey && document.activeElement === z) { e.preventDefault(); a.focus(); }
    };
    document.addEventListener('keydown', onKey);
    return () => {
      document.removeEventListener('keydown', onKey);
      if (prev && prev.focus) prev.focus();
    };
  }, []);

  return (
    <div className="backdrop" onMouseDown={(e) => { if (e.target === e.currentTarget) onClose(); }}>
      <div className={`dialog${wide ? ' wide' : ''}`} role="dialog" aria-modal="true" aria-labelledby={titleId} ref={ref}>
        <div className="dialog-head">
          <h2 id={titleId}>{title}</h2>
          <button type="button" className="icon-btn" aria-label="Đóng" onClick={onClose}><Icon name="X" /></button>
        </div>
        <div className="dialog-body">{children}</div>
      </div>
    </div>
  );
}

function ConfirmDialog({ title, message, confirmLabel = 'Đồng ý', danger, onConfirm, onClose }) {
  return (
    <Dialog title={title} onClose={onClose}>
      <p>{message}</p>
      <div className="dialog-foot" style={{ marginTop: 18 }}>
        <button type="button" className="btn" onClick={onClose}>Hủy</button>
        <button type="button" className={`btn ${danger ? 'btn-danger' : 'btn-primary'}`} data-autofocus
          onClick={() => { onConfirm(); onClose(); }}>{confirmLabel}</button>
      </div>
    </Dialog>
  );
}

function ScopeDialog({ date, onPick, onClose }) {
  return (
    <Dialog title="Sự kiện lặp hằng tuần" onClose={onClose}>
      <p className="muted">Bạn muốn sửa hoặc xóa phần nào của sự kiện này?</p>
      <div className="scope-list">
        <button type="button" className="scope-btn" data-autofocus onClick={() => onPick('this')}>
          <strong>Chỉ buổi này</strong><span>Chỉ ảnh hưởng ngày {fmtDMY(date)}</span>
        </button>
        <button type="button" className="scope-btn" onClick={() => onPick('future')}>
          <strong>Từ buổi này trở đi</strong><span>Các buổi từ ngày {fmtDMY(date)} về sau</span>
        </button>
        <button type="button" className="scope-btn" onClick={() => onPick('all')}>
          <strong>Cả chuỗi</strong><span>Tất cả các buổi, kể cả các buổi đã qua</span>
        </button>
      </div>
    </Dialog>
  );
}

/* ============================================================
   Component: EventModal (thêm / sửa sự kiện)
   ============================================================ */
function initForm(mode, series) {
  if (mode.type === 'new') {
    const date = mode.prefill.date;
    return {
      title: '', category: 'study', kind: 'once', date,
      weekdays: [wdIndex(parseISODate(date))],
      rangeStart: date, rangeEnd: toISODate(addMonths(parseISODate(date), 4)),
      startTime: mode.prefill.startTime, endTime: mode.prefill.endTime, remindMin: 15, note: '',
    };
  }
  const s = series;
  const od = mode.occDate;
  const ex = s.exceptions && s.exceptions[od];
  const o = ex && typeof ex === 'object' ? ex : s;
  const base = mode.scope === 'all' ? s : o;
  const date = s.kind === 'once' ? s.date : od;
  const f = {
    title: base.title, category: base.category, kind: s.kind,
    startTime: base.startTime, endTime: base.endTime, remindMin: base.remindMin, date,
    weekdays: s.kind === 'weekly' ? [...s.weekdays] : [wdIndex(parseISODate(date))],
    rangeStart: s.kind === 'weekly' ? s.rangeStart : date,
    rangeEnd: s.kind === 'weekly' ? s.rangeEnd : toISODate(addMonths(parseISODate(date), 4)),
  };
  f.note = (s.notes && s.notes[od] && s.notes[od].v) || '';
  if (mode.scope === 'future') f.rangeStart = od;
  return f;
}

function validateForm(f, mode) {
  const e = {};
  if (!f.title.trim()) e.title = 'Vui lòng nhập tiêu đề.';
  if (!RE_TIME.test(f.startTime)) e.startTime = 'Giờ bắt đầu không hợp lệ.';
  if (!RE_TIME.test(f.endTime)) e.endTime = 'Giờ kết thúc không hợp lệ.';
  else if (RE_TIME.test(f.startTime) && timeToMin(f.endTime) <= timeToMin(f.startTime)) {
    e.endTime = 'Giờ kết thúc phải sau giờ bắt đầu.';
  }
  if (f.kind === 'once') {
    if (!validDateStr(f.date)) e.date = 'Vui lòng chọn ngày.';
  } else if (!(mode.type === 'edit' && mode.scope === 'this')) {
    if (!f.weekdays.length) e.weekdays = 'Chọn ít nhất 1 thứ trong tuần.';
    if (!validDateStr(f.rangeStart)) e.rangeStart = 'Vui lòng chọn ngày bắt đầu.';
    if (!validDateStr(f.rangeEnd)) e.rangeEnd = 'Vui lòng chọn ngày kết thúc.';
    else if (validDateStr(f.rangeStart)) {
      if (f.rangeEnd < f.rangeStart) e.rangeEnd = 'Ngày kết thúc không được sớm hơn ngày bắt đầu.';
      else if (daysBetween(f.rangeStart, f.rangeEnd) > MAX_RANGE_DAYS) e.rangeEnd = 'Khoảng lặp tối đa 12 tháng.';
    }
  }
  return e;
}

function formToSeries(f, base) {
  const s = {
    id: base ? base.id : uid(), title: f.title.trim(), category: f.category,
    startTime: f.startTime, endTime: f.endTime, remindMin: Number(f.remindMin),
    kind: f.kind, exceptions: {}, done: base && base.done ? { ...base.done } : {},
    notes: base && base.notes ? { ...base.notes } : {}, updatedAt: Date.now(),
  };
  if (f.kind === 'once') {
    s.date = f.date;
  } else {
    s.weekdays = [...f.weekdays].sort((a, b) => a - b);
    s.rangeStart = f.rangeStart;
    s.rangeEnd = f.rangeEnd;
    if (base && base.kind === 'weekly') {
      Object.keys(base.exceptions || {}).forEach((k) => {
        if (k >= s.rangeStart && k <= s.rangeEnd) s.exceptions[k] = base.exceptions[k];
      });
    }
  }
  if (f.kind === 'once' && base && base.kind === 'once' && base.date && base.date !== f.date) {
    ['done', 'notes'].forEach((m) => { if (s[m][base.date]) { s[m][f.date] = s[m][base.date]; delete s[m][base.date]; } });
  }
  return s;
}

// Ngày mà ghi chú trong hộp thoại gắn vào: sự kiện một lần là ngày của nó; lịch lặp là buổi đang sửa
// (khi thêm mới thì là buổi đầu tiên của chuỗi)
function noteDateFor(form, mode) {
  if (form.kind === 'once') return form.date;
  if (mode.type === 'edit') return mode.occDate;
  for (let i = 0; i < 7; i += 1) {
    const d = addDays(parseISODate(form.rangeStart), i);
    if (form.weekdays.includes(wdIndex(d))) return toISODate(d);
  }
  return form.rangeStart;
}

// Trả về bản sao của series với ghi chú của một ngày đã cập nhật (nội dung rỗng = xóa ghi chú)
function withNote(series, date, text, t) {
  const cur = series.notes && series.notes[date];
  const v = String(text || '').trim().slice(0, NOTE_MAX);
  if ((cur ? cur.v : '') === v) return series;
  return { ...series, notes: { ...(series.notes || {}), [date]: { v, t } }, updatedAt: t };
}

function Field({ id, label, error, hint, children }) {
  return (
    <div className="field">
      <label htmlFor={id}>{label}</label>
      {children}
      {hint && <div className="hint">{hint}</div>}
      {error && <div className="field-error" id={`${id}-err`} role="alert">{error}</div>}
    </div>
  );
}

function EventModal({ mode, series, onSave, onDelete, onClose }) {
  const [form, setForm] = useState(() => initForm(mode, series));
  const [errors, setErrors] = useState({});
  const base = React.useId();
  const set = (patch) => setForm((f) => ({ ...f, ...patch }));

  const isEdit = mode.type === 'edit';
  const noteDate = noteDateFor(form, mode);
  const noteLabel = validDateStr(noteDate) ? `Ghi chú cho buổi ngày ${fmtDMY(noteDate)}` : 'Ghi chú';
  const lockKind = isEdit && mode.scope !== 'all';
  const lockDays = isEdit && mode.scope === 'this';
  const lockRangeStart = isEdit && mode.scope === 'future';

  const submit = (e) => {
    e.preventDefault();
    const errs = validateForm(form, mode);
    setErrors(errs);
    const keys = Object.keys(errs);
    if (keys.length) {
      const el = document.getElementById(`${base}-${keys[0]}`);
      if (el) el.focus();
      return;
    }
    onSave(form, mode);
  };

  const toggleDay = (i) => {
    const has = form.weekdays.includes(i);
    set({ weekdays: has ? form.weekdays.filter((x) => x !== i) : [...form.weekdays, i] });
  };
  const setKind = (kind) => {
    const patch = { kind };
    if (kind === 'weekly' && validDateStr(form.date)) {
      patch.rangeStart = form.date;
      patch.rangeEnd = toISODate(addMonths(parseISODate(form.date), 4));
      if (!form.weekdays.length) patch.weekdays = [wdIndex(parseISODate(form.date))];
    }
    set(patch);
  };
  const err = (k) => ({ id: `${base}-${k}`, 'aria-invalid': errors[k] ? 'true' : 'false', 'aria-describedby': errors[k] ? `${base}-${k}-err` : undefined });

  let title = 'Thêm sự kiện';
  if (isEdit) title = mode.scope === 'this' ? 'Sửa buổi này' : mode.scope === 'future' ? 'Sửa từ buổi này trở đi' : 'Sửa sự kiện';

  return (
    <Dialog title={title} onClose={onClose} wide>
      <form onSubmit={submit} noValidate>
        {isEdit && mode.scope === 'this' && <div className="lock-note">Chỉ thay đổi buổi ngày {fmtDMY(mode.occDate)}.</div>}
        {isEdit && mode.scope === 'future' && <div className="lock-note">Áp dụng từ ngày {fmtDMY(mode.occDate)} về sau.</div>}

        <Field id={`${base}-title`} label="Tiêu đề" error={errors.title}>
          <input type="text" {...err('title')} value={form.title} maxLength={120} data-autofocus
            placeholder="Ví dụ: Học Cơ sở dữ liệu" onChange={(e) => set({ title: e.target.value })} />
        </Field>

        <div className="field">
          <span className="field-label" id={`${base}-cat-label`}>Loại công việc</span>
          <div className="chip-group" role="group" aria-labelledby={`${base}-cat-label`}>
            {CATEGORIES.map((c) => (
              <button key={c.id} type="button" className="chip" aria-pressed={form.category === c.id}
                style={{ '--c': `var(--cat-${c.id})` }} onClick={() => set({ category: c.id })}>
                <span className="dot" />{c.label}
              </button>
            ))}
          </div>
        </div>

        <div className="field">
          <span className="field-label" id={`${base}-kind-label`}>Kiểu lịch</span>
          <div className="segmented" role="group" aria-labelledby={`${base}-kind-label`}>
            <button type="button" aria-pressed={form.kind === 'once'} disabled={lockKind} onClick={() => setKind('once')}>Một lần</button>
            <button type="button" aria-pressed={form.kind === 'weekly'} disabled={lockKind} onClick={() => setKind('weekly')}>Lặp hằng tuần</button>
          </div>
        </div>

        {form.kind === 'once' ? (
          <Field id={`${base}-date`} label="Ngày" error={errors.date}>
            <input type="date" {...err('date')} value={form.date} disabled={lockDays} onChange={(e) => set({ date: e.target.value })} />
          </Field>
        ) : (
          <>
            <div className="field">
              <span className="field-label" id={`${base}-wd-label`}>Các thứ trong tuần</span>
              <div className="chip-group" role="group" aria-labelledby={`${base}-wd-label`} id={`${base}-weekdays`} tabIndex={-1}>
                {WEEKDAYS.map((w, i) => (
                  <button key={w} type="button" className="chip" aria-pressed={form.weekdays.includes(i)}
                    aria-label={WEEKDAYS_LONG[i]} disabled={lockDays} onClick={() => toggleDay(i)}>{w}</button>
                ))}
              </div>
              {errors.weekdays && <div className="field-error" role="alert">{errors.weekdays}</div>}
            </div>
            <div className="field-row">
              <Field id={`${base}-rangeStart`} label="Lặp từ ngày" error={errors.rangeStart}>
                <input type="date" {...err('rangeStart')} value={form.rangeStart}
                  disabled={lockDays || lockRangeStart} onChange={(e) => set({ rangeStart: e.target.value })} />
              </Field>
              <Field id={`${base}-rangeEnd`} label="Đến ngày" error={errors.rangeEnd}>
                <input type="date" {...err('rangeEnd')} value={form.rangeEnd} disabled={lockDays}
                  onChange={(e) => set({ rangeEnd: e.target.value })} />
              </Field>
            </div>
            {!lockDays && (
              <div className="field">
                <div>
                  <button type="button" className="btn btn-sm" disabled={!validDateStr(form.rangeStart)}
                    onClick={() => set({ rangeEnd: toISODate(addMonths(parseISODate(form.rangeStart), 4)) })}>
                    Lặp 4 tháng
                  </button>
                </div>
                <div className="hint">Mỗi tuần một buổi cho các thứ đã chọn, tối đa 12 tháng.</div>
              </div>
            )}
          </>
        )}

        <div className="field-row">
          <Field id={`${base}-startTime`} label="Giờ bắt đầu" error={errors.startTime}>
            <input type="time" step="300" {...err('startTime')} value={form.startTime} onChange={(e) => set({ startTime: e.target.value })} />
          </Field>
          <Field id={`${base}-endTime`} label="Giờ kết thúc" error={errors.endTime}>
            <input type="time" step="300" {...err('endTime')} value={form.endTime} onChange={(e) => set({ endTime: e.target.value })} />
          </Field>
        </div>

        <Field id={`${base}-remind`} label="Nhắc trước">
          <select id={`${base}-remind`} value={form.remindMin} onChange={(e) => set({ remindMin: Number(e.target.value) })}>
            {REMIND_OPTIONS.map((o) => <option key={o.v} value={o.v}>{o.l}</option>)}
          </select>
        </Field>

        <Field id={`${base}-note`} label={noteLabel} hint="Mỗi buổi có ghi chú riêng. Với lịch lặp, ghi chú chỉ gắn vào buổi này.">
          <textarea id={`${base}-note`} rows={3} maxLength={NOTE_MAX} value={form.note}
            placeholder="Ví dụ: ôn chương 3, làm bài tập CSDL" onChange={(e) => set({ note: e.target.value })} />
        </Field>

        <div className="dialog-foot">
          {isEdit && (
            <button type="button" className="btn btn-danger" onClick={() => onDelete(mode)}>
              <Icon name="Trash2" size={16} /> Xóa
            </button>
          )}
          <span className="spacer" />
          <button type="button" className="btn" onClick={onClose}>Hủy</button>
          <button type="submit" className="btn btn-primary">Lưu</button>
        </div>
      </form>
    </Dialog>
  );
}

/* Mèo thần tài vẫy tay (SVG tự vẽ): báo còn sự kiện bị khuất phía dưới cột */
function CatWave() {
  return (
    <svg className="cat-svg" viewBox="0 0 52 52" width="46" height="46" aria-hidden="true" focusable="false">
      <g stroke="#4b4f78" strokeWidth="1.6" strokeLinejoin="round" strokeLinecap="round">
        <ellipse cx="22" cy="40" rx="13" ry="10.5" fill="#fff" />
        <ellipse cx="16" cy="48" rx="4" ry="2.6" fill="#fff" />
        <ellipse cx="28" cy="48" rx="4" ry="2.6" fill="#fff" />
        <g className="cat-paw">
          <rect x="35" y="13" width="9" height="23" rx="4.5" fill="#fff" />
          <circle cx="39.5" cy="18" r="2.4" fill="#f9a8c0" stroke="none" />
        </g>
        <path d="M9 17 L10 3 L20 10 Z" fill="#fff" />
        <path d="M35 17 L34 3 L24 10 Z" fill="#fff" />
        <path d="M11.5 13 L12 6.5 L16.5 10 Z" fill="#f9a8c0" stroke="none" />
        <path d="M32.5 13 L32 6.5 L27.5 10 Z" fill="#f9a8c0" stroke="none" />
        <ellipse cx="22" cy="22" rx="14.5" ry="12" fill="#fff" />
        <path d="M14 21 q2.4 -3.4 4.8 0 M25.2 21 q2.4 -3.4 4.8 0" fill="none" />
        <path d="M20.6 25 h2.8 l-1.4 1.8 z" fill="#f08aa6" stroke="#f08aa6" strokeWidth="1" />
        <path d="M22 26.8 q-1.6 2.2 -3.4 0.8 M22 26.8 q1.6 2.2 3.4 0.8" fill="none" />
        <path d="M6.5 24 l5.5 1 M6.5 28 l5.5 -1 M37.5 24 l-5.5 1 M37.5 28 l-5.5 -1" fill="none" strokeWidth="1.2" />
        <path d="M11 33 q11 5 22 0 l0.4 3 q-11.4 5 -22.8 0 z" fill="#e5484d" />
        <circle cx="22" cy="38.5" r="2.7" fill="#f5b82e" />
      </g>
      <circle cx="12.5" cy="26" r="2.2" fill="#f9a8c0" opacity=".75" />
      <circle cx="31.5" cy="26" r="2.2" fill="#f9a8c0" opacity=".75" />
    </svg>
  );
}

/* ============================================================
   Việc cần làm: hộp thoại thêm/sửa, xác nhận 2 bước, danh sách
   ============================================================ */
function TaskModal({ mode, series, defaults, onSave, onDelete, onClose }) {
  const isEdit = mode.type === 'edit';
  const [form, setForm] = useState(() => (isEdit ? {
    title: series.title, date: series.date, startTime: series.startTime,
    repeat: series.repeatMode === 'eod' ? 'eod' : String(series.repeatN === 3 ? 3 : 2), note: taskNote(series),
  } : { title: '', date: defaults.date, startTime: defaults.startTime, repeat: '2', note: '' }));
  const [errors, setErrors] = useState({});
  const base = React.useId();
  const set = (patch) => setForm((f) => ({ ...f, ...patch }));
  const err = (k) => ({ id: `${base}-${k}`, 'aria-invalid': errors[k] ? 'true' : 'false', 'aria-describedby': errors[k] ? `${base}-${k}-err` : undefined });
  const submit = (e) => {
    e.preventDefault();
    const er = {};
    if (!form.title.trim()) er.title = 'Vui lòng nhập tên việc.';
    if (!validDateStr(form.date)) er.date = 'Vui lòng chọn ngày.';
    if (!RE_TIME.test(form.startTime)) er.startTime = 'Giờ không hợp lệ.';
    setErrors(er);
    const keys = Object.keys(er);
    if (keys.length) { const el = document.getElementById(`${base}-${keys[0]}`); if (el) el.focus(); return; }
    onSave(form, mode);
  };
  const REPEATS = [['2', 'Nhắc 2 lần'], ['3', 'Nhắc 3 lần'], ['eod', 'Đến hết ngày']];
  return (
    <Dialog title={isEdit ? 'Sửa việc cần làm' : 'Thêm việc cần làm'} onClose={onClose} wide>
      <form onSubmit={submit} noValidate>
        <Field id={`${base}-title`} label="Việc cần làm" error={errors.title}>
          <input type="text" {...err('title')} value={form.title} maxLength={120} data-autofocus
            placeholder="Ví dụ: Giặt quần áo" onChange={(e) => set({ title: e.target.value })} />
        </Field>
        <div className="field-row">
          <Field id={`${base}-date`} label="Ngày" error={errors.date}>
            <input type="date" {...err('date')} value={form.date} onChange={(e) => set({ date: e.target.value })} />
          </Field>
          <Field id={`${base}-startTime`} label="Giờ bắt đầu" error={errors.startTime}>
            <input type="time" step="300" {...err('startTime')} value={form.startTime} onChange={(e) => set({ startTime: e.target.value })} />
          </Field>
        </div>
        <div className="field">
          <span className="field-label" id={`${base}-rep-label`}>Nhắc lại mỗi 1 tiếng nếu chưa tick</span>
          <div className="segmented" role="group" aria-labelledby={`${base}-rep-label`}>
            {REPEATS.map(([v, l]) => (
              <button key={v} type="button" aria-pressed={form.repeat === v} onClick={() => set({ repeat: v })}>{l}</button>
            ))}
          </div>
          <div className="hint">Nhắc lần đầu đúng giờ bắt đầu, sau đó mỗi 1 tiếng. "Đến hết ngày" nhắc tới 23:59 rồi dừng. Tick xong là dừng nhắc.</div>
        </div>
        <Field id={`${base}-note`} label="Ghi chú (dùng trong câu nhắc)" hint="Câu nhắc sẽ đọc phần ghi chú này. Để trống thì dùng tên việc.">
          <textarea id={`${base}-note`} rows={2} maxLength={NOTE_MAX} value={form.note}
            placeholder="Ví dụ: giặt đồ trắng" onChange={(e) => set({ note: e.target.value })} />
        </Field>
        <div className="dialog-foot">
          {isEdit && (
            <button type="button" className="btn btn-danger" onClick={() => onDelete(mode.seriesId)}>
              <Icon name="Trash2" size={16} /> Xóa
            </button>
          )}
          <span className="spacer" />
          <button type="button" className="btn" onClick={onClose}>Hủy</button>
          <button type="submit" className="btn btn-primary">Lưu</button>
        </div>
      </form>
    </Dialog>
  );
}

// Xác nhận 2 bước trong một hộp thoại; tick xong không thể bỏ
function TaskDoneDialog({ task, onConfirm, onClose }) {
  const [step, setStep] = useState(1);
  const nextRef = useRef(null);
  useEffect(() => { if (nextRef.current) nextRef.current.focus(); }, [step]);
  return (
    <Dialog title={step === 1 ? 'Đã làm xong chưa?' : 'Xác nhận lần cuối'} onClose={onClose}>
      <p className="muted" style={{ marginBottom: 6 }}>Bước {step}/2</p>
      {step === 1
        ? <p>Bạn đã hoàn thành <strong>{task.title}</strong> chưa?</p>
        : <p>Chắc chắn đã xong <strong>{task.title}</strong>? Sau khi xác nhận, <strong>không thể bỏ tick</strong> và sẽ ngừng nhắc.</p>}
      <div className="dialog-foot" style={{ marginTop: 18 }}>
        <button type="button" className="btn" onClick={step === 1 ? onClose : () => setStep(1)}>{step === 1 ? 'Chưa xong' : 'Quay lại'}</button>
        <button type="button" className="btn btn-primary" ref={nextRef}
          onClick={step === 1 ? () => setStep(2) : () => { onConfirm(task.id); onClose(); }}>
          {step === 1 ? 'Đã xong (1/2)' : 'Chắc chắn (2/2)'}
        </button>
      </div>
    </Dialog>
  );
}

function TasksView({ tasks, now, onAdd, onEdit, onDelete, onDone }) {
  const nowMs = now.getTime();
  const todayISO = toISODate(now);
  const rows = useMemo(() => tasks.map((s) => {
    const startMs = dateTimeMs(s.date, s.startTime);
    const dn = taskDone(s);
    const k = nowMs >= startMs ? Math.floor((nowMs - startMs) / HOUR_MS) : -1;
    const lastK = taskLastK(s);
    return {
      s, startMs, doneAt: dn ? dn.t : null, started: nowMs >= startMs, note: taskNote(s),
      sent: k < 0 ? 0 : Math.min(k, lastK) + 1,
      nextMs: k + 1 <= lastK ? startMs + (k + 1) * HOUR_MS : null,
    };
  }), [tasks, nowMs]);
  const due = rows.filter((r) => !r.doneAt && r.started).sort((a, b) => a.startMs - b.startMs);
  const soon = rows.filter((r) => !r.doneAt && !r.started).sort((a, b) => a.startMs - b.startMs);
  const finished = rows.filter((r) => r.doneAt && r.doneAt > nowMs - 7 * 86400000).sort((a, b) => b.doneAt - a.doneAt).slice(0, 30);

  const statusText = (r) => {
    const s = r.s;
    const modeLabel = s.repeatMode === 'eod' ? 'mỗi giờ đến hết ngày' : `${s.repeatN === 3 ? 3 : 2} lần, mỗi giờ`;
    if (r.doneAt) return `Xong lúc ${fmtClock(r.doneAt)} · ${fmtDM(toISODate(new Date(r.doneAt)))}`;
    if (!r.started) return `Nhắc lúc ${s.startTime} (${modeLabel})`;
    return `Đã nhắc ${r.sent} lần${r.nextMs ? ` · lần tới ${fmtClock(r.nextMs)}` : ' · hết lượt nhắc'}`;
  };
  const renderRow = (r) => {
    const s = r.s;
    return (
      <li key={s.id} className={`task-row${r.doneAt ? ' done' : r.started ? ' due' : ''}`}>
        {r.doneAt ? (
          <span className="task-check locked" title="Đã xong, không thể bỏ tick"><Icon name="Check" size={16} /></span>
        ) : (
          <button type="button" className="task-check" disabled={!r.started} aria-label={`Đánh dấu đã xong: ${s.title}`}
            title={r.started ? 'Đánh dấu đã xong' : 'Chỉ tích được từ giờ bắt đầu'} onClick={() => onDone(s.id)} />
        )}
        <div className="task-main">
          <div className="task-title">{s.title}</div>
          <div className="task-sub">
            {s.startTime} · {fmtDM(s.date)}
            {!r.doneAt && s.date < todayISO && <span className="task-badge late">Quá hạn</span>}
          </div>
          {r.note && <div className="task-note"><Icon name="FileText" size={12} /> {r.note}</div>}
          <div className="task-sub">{statusText(r)}</div>
        </div>
        {!r.doneAt && (
          <div className="task-actions">
            <button type="button" className="icon-btn" aria-label={`Sửa ${s.title}`} onClick={() => onEdit(s.id)}><Icon name="Pencil" size={16} /></button>
            <button type="button" className="icon-btn danger" aria-label={`Xóa ${s.title}`} onClick={() => onDelete(s.id)}><Icon name="Trash2" size={16} /></button>
          </div>
        )}
      </li>
    );
  };
  const group = (title, list, cls) => list.length > 0 && (
    <section className={`task-group ${cls || ''}`}>
      <h2>{title} <span className="muted">({list.length})</span></h2>
      <ul className="task-list">{list.map(renderRow)}</ul>
    </section>
  );
  return (
    <div className="tasks-wrap">
      <div className="tasks-card">
        <p className="hint tasks-intro">Việc có giờ bắt đầu nhưng không có giờ kết thúc (giặt đồ, nấu cơm…). Ứng dụng nhắc đúng giờ rồi nhắc lại mỗi 1 tiếng cho tới khi bạn tick. Tick xong không bỏ được.</p>
        {rows.length === 0 && (
          <div className="empty-note">
            Chưa có việc nào. <button type="button" className="btn btn-sm" style={{ marginLeft: 8 }} onClick={onAdd}><Icon name="Plus" size={14} /> Thêm việc</button>
          </div>
        )}
        {group('Cần làm bây giờ', due, 'is-due')}
        {group('Sắp tới', soon)}
        {group('Đã xong (7 ngày gần đây)', finished, 'is-done')}
        {rows.length > 0 && due.length + soon.length === 0 && <div className="empty-note">Không còn việc nào chưa làm.</div>}
      </div>
    </div>
  );
}

/* ============================================================
   Component: Toast
   ============================================================ */
function ToastHost({ toasts, onDismiss }) {
  const iconFor = { success: 'Check', error: 'TriangleAlert', reminder: 'Bell', info: 'Clock' };
  return (
    <div className="toast-host" aria-live="polite" aria-atomic="false">
      {toasts.map((t) => (
        <div key={t.id} className={`toast ${t.kind}`} role={t.kind === 'error' ? 'alert' : 'status'}>
          <Icon name={iconFor[t.kind] || 'Clock'} />
          <div className="toast-body">
            <div className="toast-title">{t.title}</div>
            {t.message && <div className="toast-msg">{t.message}</div>}
          </div>
          <button type="button" className="icon-btn" aria-label="Đóng thông báo" onClick={() => onDismiss(t.id)}>
            <Icon name="X" size={16} />
          </button>
        </div>
      ))}
    </div>
  );
}

/* ============================================================
   Component: WeekGrid (lưới thời gian biểu theo tuần)
   ============================================================ */
function WeekGrid({ weekStart, dayCount = 7, events, hoursKey, now, scrollSignal, slideDir, onSlotClick, onCardClick, onToggleDone, onMoveOccurrence, onShow24h }) {
  const cfg = HOUR_OPTIONS[hoursKey] || HOUR_OPTIONS['6-23'];
  const gridStart = cfg.start * 60;
  const gridEnd = cfg.end * 60;
  const scrollRef = useRef(null);
  // ----- Kéo thả (chuột/bút; màn hình cảm ứng vẫn mở hộp thoại để sửa) -----
  const [drag, setDrag] = useState(null);     // { key, mode: 'move' | 'resize', preview: { iso, s, e } }
  const dragRef = useRef(null);
  const suppressClick = useRef(false);        // bỏ qua cú click ngay sau khi thả
  const latest = useRef({});
  latest.current = { onMoveOccurrence, gridStart };
  const dnd = useRef(null);
  if (!dnd.current) {
    const STEP = 30; // phút
    const finish = (commit) => {
      const st = dragRef.current;
      window.removeEventListener('pointermove', dnd.current.move);
      window.removeEventListener('pointerup', dnd.current.up);
      window.removeEventListener('pointercancel', dnd.current.cancel);
      window.removeEventListener('keydown', dnd.current.key);
      document.body.classList.remove('dragging-card');
      dragRef.current = null;
      setDrag(null);
      if (!st || !st.active) return;
      suppressClick.current = true;
      setTimeout(() => { suppressClick.current = false; }, 60);
      const p = st.preview;
      if (commit && p && (p.iso !== st.it.date || p.s !== st.it.s || p.e !== st.it.e)) {
        latest.current.onMoveOccurrence(st.it.seriesId, st.it.date, { date: p.iso, startTime: minToTime(p.s), endTime: minToTime(p.e) });
      }
    };
    const move = (e) => {
      const st = dragRef.current;
      const root = scrollRef.current;
      if (!st || !root) return;
      if (!st.active) {
        if (Math.abs(e.clientX - st.x0) + Math.abs(e.clientY - st.y0) < 6) return; // chưa đủ xa: coi là click
        st.active = true;
        document.body.classList.add('dragging-card');
      }
      const gs = latest.current.gridStart;
      const sr = root.getBoundingClientRect();
      if (e.clientY < sr.top + 48) root.scrollTop -= 14; // tự cuộn khi kéo sát mép
      else if (e.clientY > sr.bottom - 48) root.scrollTop += 14;
      const cols = [...root.querySelectorAll('.day-col')];
      if (!cols.length) return;
      let col = cols.find((x) => { const r = x.getBoundingClientRect(); return e.clientX >= r.left && e.clientX < r.right; });
      if (!col) col = e.clientX < cols[0].getBoundingClientRect().left ? cols[0] : cols[cols.length - 1];
      const rect = col.getBoundingClientRect();
      const minsAt = (y) => gs + ((y - rect.top) / HOUR_H) * 60;
      let iso = col.dataset.iso;
      let s0 = st.it.s;
      let e0 = st.it.e;
      if (st.mode === 'move') {
        let ns = Math.round(minsAt(e.clientY - st.grab) / STEP) * STEP;
        ns = Math.max(gs, ns);
        if (ns + st.dur > 1439) ns = Math.floor((1439 - st.dur) / STEP) * STEP;
        s0 = ns;
        e0 = ns + st.dur;
      } else {
        iso = st.it.date; // đổi kích thước chỉ đổi giờ kết thúc, giữ nguyên ngày
        e0 = Math.max(st.it.s + STEP, Math.min(Math.round(minsAt(e.clientY) / STEP) * STEP, 1439));
      }
      st.preview = { iso, s: s0, e: e0 };
      setDrag({ key: st.it.key, mode: st.mode, preview: st.preview });
    };
    dnd.current = {
      move,
      up: () => finish(true),
      cancel: () => finish(false),
      key: (e) => { if (e.key === 'Escape') finish(false); },
    };
  }
  useEffect(() => () => { if (dnd.current) dnd.current.cancel(); }, []);
  const startDrag = (e, it, mode) => {
    if (e.pointerType === 'touch' || e.button !== 0) return;
    if (e.target.closest && e.target.closest('.ev-check')) return;
    const r = e.currentTarget.getBoundingClientRect();
    dragRef.current = { mode, it, x0: e.clientX, y0: e.clientY, grab: mode === 'move' ? e.clientY - r.top : 0, dur: it.e - it.s, active: false, preview: null };
    window.addEventListener('pointermove', dnd.current.move);
    window.addEventListener('pointerup', dnd.current.up);
    window.addEventListener('pointercancel', dnd.current.cancel);
    window.addEventListener('keydown', dnd.current.key);
  };

  const days = useMemo(() => Array.from({ length: dayCount }, (_, i) => addDays(weekStart, i)), [weekStart, dayCount]);
  const hours = useMemo(() => Array.from({ length: cfg.end - cfg.start }, (_, i) => cfg.start + i), [cfg]);

  const model = useMemo(() => {
    const all = [];
    events.forEach((s) => all.push(...occurrencesInRange(s, days[0], days[days.length - 1])));
    let hidden = 0;
    let conflicts = 0;
    const cols = days.map((d) => {
      const iso = toISODate(d);
      const items = all.filter((o) => o.date === iso).map((o) => ({ ...o, s: timeToMin(o.startTime), e: timeToMin(o.endTime) }));
      const visible = items.filter((it) => it.s >= gridStart && it.e <= gridEnd);
      hidden += items.length - visible.length;
      visible.forEach((a) => { a.conflict = visible.some((b) => b !== a && b.s < a.e && a.s < b.e); });
      conflicts += visible.filter((a) => a.conflict).length;
      return { iso, date: d, laid: layoutDay(visible) };
    });
    return { cols, hidden, conflicts };
  }, [days, events, gridStart, gridEnd]);

  const todayISO = toISODate(now);
  const nowMin = now.getHours() * 60 + now.getMinutes();
  const nowVisible = nowMin >= gridStart && nowMin <= gridEnd;
  const weekHasToday = days.some((d) => toISODate(d) === todayISO);
  // Tổng kết tuần: số buổi đã làm / số buổi đã bắt đầu
  const summary = useMemo(() => {
    const nowMs = now.getTime();
    let started = 0;
    let done = 0;
    events.forEach((s) => occurrencesInRange(s, days[0], days[days.length - 1]).forEach((o) => {
      if (dateTimeMs(o.date, o.startTime) <= nowMs) { started += 1; if (o.done) done += 1; }
    }));
    return { started, done };
  }, [events, days, now]);

  // Cuộn tới vị trí giờ hiện tại khi mở app, bấm "Hôm nay" hoặc đổi khung giờ
  useEffect(() => {
    const el = scrollRef.current;
    if (!el) return;
    const top = nowVisible ? ((nowMin - gridStart) / 60) * HOUR_H - 140 : 0;
    el.scrollTo({ top: Math.max(0, top), behavior: scrollSignal === 0 ? 'auto' : 'smooth' });
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [scrollSignal, hoursKey]);

  // ----- Gợi ý còn lịch ở ngoài vùng nhìn thấy: mũi tên theo từng cột ngày, và trái/phải khi cuộn ngang -----
  const [hint, setHint] = useState({ cols: [], left: 0, right: 0, headH: 88, sideW: 56 });
  const measureHidden = () => {
    const el = scrollRef.current;
    const vp = el && el.parentElement;
    const out = { cols: [], left: [], right: [], headH: 88, sideW: 56 };
    if (!el || !vp) return out;
    const sr = el.getBoundingClientRect();
    const vr = vp.getBoundingClientRect();
    const head = el.querySelector('.grid-head');
    const tc = el.querySelector('.time-col');
    out.headH = head ? head.offsetHeight : 88;
    out.sideW = tc ? tc.offsetWidth : 56;
    const visL = sr.left + out.sideW;
    const visR = sr.left + el.clientWidth; // bỏ thanh cuộn dọc
    el.querySelectorAll('.day-col').forEach((col) => {
      const cr = col.getBoundingClientRect();
      const c = { iso: col.dataset.iso, up: [], down: [], left: Math.max(cr.left, visL) - vr.left, width: Math.min(cr.right, visR) - Math.max(cr.left, visL) };
      col.querySelectorAll('.event').forEach((n) => {
        const r = n.getBoundingClientRect();
        if (r.height === 0) return;
        if (r.top >= sr.bottom - 2) c.down.push(r.top - sr.top);
        else if (r.bottom <= sr.top + out.headH + 2) c.up.push(r.top - sr.top);
        if (r.left >= visR - 2) out.right.push(r.left - sr.left);
        else if (r.right <= visL + 2) out.left.push(r.right - sr.left);
      });
      out.cols.push(c);
    });
    return out;
  };
  const refreshHint = () => {
    const m = measureHidden();
    const n = {
      cols: m.cols.filter((c) => c.width >= 30 && (c.up.length || c.down.length))
        .map((c) => ({ iso: c.iso, up: c.up.length, down: c.down.length, left: Math.round(c.left), width: Math.round(c.width) })),
      left: m.left.length, right: m.right.length, headH: m.headH, sideW: m.sideW,
    };
    setHint((p) => (JSON.stringify(p) === JSON.stringify(n) ? p : n));
  };
  const hintRef = useRef(null);
  hintRef.current = refreshHint;
  useEffect(() => {
    const el = scrollRef.current;
    if (!el) return undefined;
    let raf = 0;
    const run = () => { cancelAnimationFrame(raf); raf = requestAnimationFrame(() => hintRef.current()); };
    el.addEventListener('scroll', run, { passive: true });
    window.addEventListener('resize', run);
    const ro = window.ResizeObserver ? new ResizeObserver(run) : null;
    if (ro) ro.observe(el);
    run();
    return () => { cancelAnimationFrame(raf); el.removeEventListener('scroll', run); window.removeEventListener('resize', run); if (ro) ro.disconnect(); };
  }, []);
  // Dữ liệu, tuần hoặc khung giờ đổi: đo lại (cả sau khi hiệu ứng trượt tuần kết thúc)
  useEffect(() => {
    hintRef.current();
    const t1 = setTimeout(() => hintRef.current(), 120);
    const t2 = setTimeout(() => hintRef.current(), 700);
    return () => { clearTimeout(t1); clearTimeout(t2); };
  }, [events, weekStart, hoursKey, scrollSignal]);
  // dir: 'up' | 'down' (kèm iso của cột) hoặc 'left' | 'right'
  const jump = (dir, iso) => {
    const el = scrollRef.current;
    if (!el) return;
    const m = measureHidden();
    const reduce = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
    const behavior = reduce ? 'auto' : 'smooth';
    if (dir === 'up' || dir === 'down') {
      const c = m.cols.find((x) => x.iso === iso);
      if (!c) return;
      // Đưa sự kiện khuất gần nhất của cột đó lên sát mép dưới thanh ngày (cách 24px)
      if (dir === 'down' && c.down.length) el.scrollBy({ top: Math.min(...c.down) - m.headH - 24, behavior });
      else if (dir === 'up' && c.up.length) el.scrollBy({ top: Math.max(...c.up) - m.headH - 24, behavior });
    } else if (dir === 'right' && m.right.length) el.scrollBy({ left: Math.min(...m.right) - m.sideW - 8, behavior });
    else if (dir === 'left' && m.left.length) el.scrollBy({ left: Math.max(...m.left) - (el.clientWidth - 8), behavior });
  };

  const handleColClick = (e, iso) => {
    if (suppressClick.current) return;
    const rect = e.currentTarget.getBoundingClientRect();
    const y = e.clientY - rect.top;
    let mins = gridStart + Math.floor((y / HOUR_H) * 2) * 30; // làm tròn xuống 30 phút
    mins = Math.max(gridStart, Math.min(mins, 23 * 60 + 30));
    onSlotClick(iso, minToTime(mins), minToTime(Math.min(mins + 60, 23 * 60 + 59)));
  };

  const bodyHeight = hours.length * HOUR_H;

  return (
    <div className="grid-card">
      {summary.started > 0 && (
        <div className="week-summary" aria-live="polite">
          <span><Icon name="Check" size={14} /> {dayCount === 1 ? (weekHasToday ? 'Hôm nay' : 'Ngày đang xem') : (weekHasToday ? 'Tuần này' : 'Tuần đang xem')}: <strong>{summary.done}/{summary.started}</strong> buổi đã làm</span>
          <span className="bar" aria-hidden="true"><i style={{ width: `${Math.round((summary.done / summary.started) * 100)}%` }} /></span>
        </div>
      )}
      {(model.hidden > 0 || model.conflicts > 0) && (
        <div className="grid-notes">
          {model.conflicts > 0 && (
            <span className="note-chip"><Icon name="TriangleAlert" size={14} /> {model.conflicts} sự kiện trùng giờ {dayCount === 1 ? 'trong ngày này' : 'trong tuần này'}</span>
          )}
          {model.hidden > 0 && (
            <span className="note-chip">
              <Icon name="Clock" size={14} /> {model.hidden} sự kiện nằm ngoài khung giờ đang chọn
              {hoursKey !== '0-23' && <button type="button" onClick={onShow24h}>Xem 24h</button>}
            </span>
          )}
        </div>
      )}
      <div className="grid-viewport">
      <div className="grid-scroll" ref={scrollRef}>
        <div key={toISODate(weekStart)} className={`grid-inner days-${dayCount} slide-${slideDir}`} style={{ '--hour-h': `${HOUR_H}px`, '--cols': dayCount }}>
          <div className="grid-head">
            <div className="head-corner" />
            {days.map((d, i) => {
              const isToday = toISODate(d) === todayISO;
              return (
                <div key={i} className={`day-head${isToday ? ' today' : ''}`} aria-current={isToday ? 'date' : undefined}>
                  <div className="dow">{WEEKDAYS[wdIndex(d)]}</div>
                  <div className="dom">{pad(d.getDate())}/{pad(d.getMonth() + 1)}</div>
                </div>
              );
            })}
          </div>
          <div className="grid-body" style={{ height: bodyHeight }}>
            <div className="time-col">
              {hours.map((h) => (<div key={h} className="time-cell"><span>{pad(h)}:00</span></div>))}
              {weekHasToday && nowVisible && (
                <div className="now-tag" style={{ top: ((nowMin - gridStart) / 60) * HOUR_H }}>{minToTime(nowMin)}</div>
              )}
            </div>
            {model.cols.map((col, ci) => {
              const isToday = col.iso === todayISO;
              return (
                <div key={col.iso} data-iso={col.iso} className={`day-col${isToday ? ' today' : ''}`} onClick={(e) => handleColClick(e, col.iso)}>
                  {col.laid.map((it) => {
                    const top = ((it.s - gridStart) / 60) * HOUR_H;
                    const h = Math.max(((it.e - it.s) / 60) * HOUR_H - 2, 20);
                    const w = 100 / it.cols;
                    const compact = h < 38;
                    const started = dateTimeMs(it.date, it.startTime) <= now.getTime();
                    return (
                      <div key={it.key} className={`event${it.conflict ? ' conflict' : ''}${compact ? ' compact' : ''}${drag && drag.key === it.key ? ' dragging' : ''}`}
                        onPointerDown={(e) => startDrag(e, it, 'move')}
                        style={{
                          animationDelay: `${ci * 0.05}s`, top, height: h, left: `calc(${it.col * w}% + 2px)`, width: `calc(${w}% - 4px)`,
                          '--ev-color': `var(--cat-${it.category})`, '--ev-bg': `var(--cat-${it.category}-bg)`,
                        }}>
                        <button type="button" className="ev-open"
                          title={`${it.title}\n${it.startTime} – ${it.endTime} · ${catLabel(it.category)}${it.conflict ? '\n⚠ Trùng giờ' : ''}${it.done ? '\n✓ Đã làm' : ''}${it.note ? '\n' + it.note : ''}`}
                          aria-label={`${it.title}, ${fmtDMY(it.date)}, ${it.startTime} đến ${it.endTime}, ${catLabel(it.category)}${it.conflict ? ', trùng giờ' : ''}${it.done ? ', đã làm' : ''}${it.note ? ', có ghi chú' : ''}`}
                          onClick={(e) => { e.stopPropagation(); if (suppressClick.current) return; onCardClick(it.seriesId, it.date); }}>
                          <span className="ev-title">{it.title}</span>
                          <span className="ev-time">{it.startTime} – {it.endTime}</span>
                          {h >= 64 && (
                            <span className="ev-meta">
                              {it.kind === 'weekly' && <Icon name="Repeat" size={12} />}
                              {it.remindMin > 0 && !it.done && <Icon name="Bell" size={12} />}
                              {it.conflict && <Icon name="TriangleAlert" size={12} />}
                              {it.note && <Icon name="FileText" size={12} />}
                              <span className="ev-cat">{catLabel(it.category)}</span>
                            </span>
                          )}
                          {h >= 96 && it.note && <span className="ev-note">{it.note}</span>}
                        </button>
                        {(started || it.done) && (
                        <button type="button" role="checkbox" aria-checked={it.done} className={`ev-check${it.done ? ' on' : ''}`}
                          title={it.done ? 'Đã làm (bấm để bỏ)' : 'Đánh dấu đã làm'}
                          aria-label={`${it.done ? 'Bỏ đánh dấu đã làm' : 'Đánh dấu đã làm'}: ${it.title}, ${fmtDMY(it.date)}`}
                          onClick={(e) => { e.stopPropagation(); onToggleDone(it.seriesId, it.date); }}>
                          {it.done && <Icon name="Check" size={12} />}
                        </button>
                        )}
                        <div className="ev-resize" aria-hidden="true" title="Kéo để đổi giờ kết thúc"
                          onPointerDown={(e) => { e.stopPropagation(); startDrag(e, it, 'resize'); }} />
                      </div>
                    );
                  })}
                  {drag && drag.preview && drag.preview.iso === col.iso && (
                    <div className="event-ghost" style={{
                      top: ((drag.preview.s - gridStart) / 60) * HOUR_H,
                      height: Math.max(((drag.preview.e - drag.preview.s) / 60) * HOUR_H - 2, 20),
                    }}>{minToTime(drag.preview.s)} – {minToTime(drag.preview.e)}</div>
                  )}
                  {isToday && nowVisible && (
                    <div className="now-line" style={{ top: ((nowMin - gridStart) / 60) * HOUR_H }}><span className="now-dot" /></div>
                  )}
                </div>
              );
            })}
          </div>
        </div>
      </div>
      {hint.cols.map((c) => (
        <div key={c.iso} className="col-hints" style={{ left: c.left, width: c.width }}>
          {c.up > 0 && (
            <button type="button" className="col-hint up" style={{ top: hint.headH + 6 }} onClick={() => jump('up', c.iso)}
              aria-label={`${fmtDM(c.iso)}: còn ${c.up} sự kiện phía trên, bấm để cuộn lên`}>
              <Icon name="ChevronUp" size={15} />{c.up}
            </button>
          )}
          {c.down > 0 && (
            <button type="button" className="col-hint down cat" title={`Còn ${c.down} sự kiện bên dưới`}
              onClick={(e) => {
                const svg = e.currentTarget.querySelector('.cat-svg');
                if (svg) { svg.classList.remove('hop'); void svg.getBoundingClientRect(); svg.classList.add('hop'); }
                jump('down', c.iso);
              }}
              aria-label={`${fmtDM(c.iso)}: còn ${c.down} sự kiện phía dưới, bấm để cuộn xuống`}>
              <CatWave />
            </button>
          )}
        </div>
      ))}
      {hint.left > 0 && (
        <button type="button" className="scroll-hint side left" style={{ left: hint.sideW + 6 }} onClick={() => jump('left')}
          aria-label={`Còn ${hint.left} sự kiện bên trái, bấm để cuộn sang trái`}>
          <Icon name="ChevronLeft" size={16} /> {hint.left}
        </button>
      )}
      {hint.right > 0 && (
        <button type="button" className="scroll-hint side right" onClick={() => jump('right')}
          aria-label={`Còn ${hint.right} sự kiện bên phải, bấm để cuộn sang phải`}>
          {hint.right} <Icon name="ChevronRight" size={16} />
        </button>
      )}
      </div>
    </div>
  );
}

/* ============================================================
   Component: EmailSyncPanel (nhắc qua email — Google Apps Script)
   ============================================================ */
function EmailSyncPanel({ settings, status, onSave, onToggle, onTest, onSyncNow, onCopyLink }) {
  const [url, setUrl] = useState(settings.syncUrl);
  const [token, setToken] = useState(settings.syncToken);
  const [showToken, setShowToken] = useState(false);
  const urlId = React.useId();
  const tokenId = React.useId();
  const dirty = url.trim() !== settings.syncUrl || token.trim() !== settings.syncToken;
  const ready = !dirty && settings.syncUrl && settings.syncToken;

  return (
    <div className="sync-panel">
      <p className="hint">Các thiết bị dùng cùng URL và token sẽ chia sẻ một bộ lịch (tự đồng bộ khi mở app và mỗi 2 phút). Khi đóng tab, email nhắc được gửi từ Google Apps Script của bạn.</p>
      <label htmlFor={urlId}>URL Web App</label>
      <input id={urlId} type="url" autoComplete="off" spellCheck="false" placeholder="https://script.google.com/macros/s/.../exec"
        value={url} onChange={(e) => setUrl(e.target.value)} />
      <label htmlFor={tokenId}>Token</label>
      <div className="input-row">
        <input id={tokenId} type={showToken ? 'text' : 'password'} autoComplete="off" spellCheck="false"
          value={token} onChange={(e) => setToken(e.target.value)} />
        <button type="button" className="icon-btn bordered" aria-label={showToken ? 'Ẩn token' : 'Hiện token'} onClick={() => setShowToken((v) => !v)}>
          <Icon name={showToken ? 'EyeOff' : 'Eye'} />
        </button>
      </div>
      <div className="row" style={{ marginTop: 8 }}>
        <button type="button" className="btn btn-primary" disabled={!dirty} onClick={() => onSave(url.trim(), token.trim())}>Lưu</button>
      </div>
      <label className="switch-row">
        <input type="checkbox" role="switch" checked={settings.syncEnabled} onChange={(e) => onToggle(e.target.checked)} />
        <span>Bật đồng bộ và nhắc qua email</span>
      </label>
      <div className={`sync-status ${status.state}`} role="status">{status.message}</div>
      <div className="row">
        <button type="button" className="btn btn-sm" disabled={!ready} onClick={onTest}><Icon name="Send" size={15} /> Gửi thử email</button>
        <button type="button" className="btn btn-sm" disabled={!ready || !settings.syncEnabled} onClick={onSyncNow}><Icon name="RefreshCw" size={15} /> Đồng bộ ngay</button>
      </div>
      <button type="button" className="btn btn-sm btn-block" style={{ marginTop: 8 }} disabled={!ready} onClick={onCopyLink}>
        <Icon name="Link" size={15} /> Sao chép link cấu hình cho thiết bị khác
      </button>
      {dirty && <p className="hint" style={{ marginTop: 6 }}>Hãy bấm "Lưu" trước khi gửi thử hoặc đồng bộ.</p>}
    </div>
  );
}

/* ============================================================
   Component: MiniCalendar (lịch tháng nhỏ để nhảy tuần)
   ============================================================ */
function MiniCalendar({ weekStart, spanDays = 7, events, onPick }) {
  const [month, setMonth] = useState(() => new Date(weekStart.getFullYear(), weekStart.getMonth(), 1));
  const wsKey = toISODate(weekStart);
  // Khi đổi tuần ở nơi khác (nút Tuần trước/sau, Hôm nay) thì lịch tháng đi theo
  useEffect(() => { setMonth(new Date(weekStart.getFullYear(), weekStart.getMonth(), 1)); }, [wsKey]);
  const todayISO = toISODate(new Date());
  const weekEndISO = toISODate(addDays(weekStart, spanDays - 1));
  const cells = useMemo(() => {
    const first = startOfWeek(month);
    return Array.from({ length: 42 }, (_, i) => addDays(first, i));
  }, [month]);
  // Các ngày có sự kiện (hiện chấm nhỏ)
  const busy = useMemo(() => {
    const set = new Set();
    events.forEach((s) => occurrencesInRange(s, cells[0], cells[41]).forEach((o) => set.add(o.date)));
    return set;
  }, [events, cells]);
  const shift = (n) => setMonth((m) => new Date(m.getFullYear(), m.getMonth() + n, 1));

  return (
    <div className="mini-cal">
      <div className="mini-head">
        <button type="button" className="icon-btn" aria-label="Lịch nhỏ: tháng trước" onClick={() => shift(-1)}><Icon name="ChevronLeft" size={16} /></button>
        <strong aria-live="polite">Tháng {month.getMonth() + 1}/{month.getFullYear()}</strong>
        <button type="button" className="icon-btn" aria-label="Lịch nhỏ: tháng sau" onClick={() => shift(1)}><Icon name="ChevronRight" size={16} /></button>
      </div>
      <div className="mini-grid">
        {WEEKDAYS.map((w) => <span key={w} className="mini-dow">{w}</span>)}
        {cells.map((d) => {
          const iso = toISODate(d);
          const cls = ['mini-day'];
          if (d.getMonth() !== month.getMonth()) cls.push('outside');
          if (iso === todayISO) cls.push('today');
          if (iso >= wsKey && iso <= weekEndISO) cls.push('in-week');
          const has = busy.has(iso);
          return (
            <button key={iso} type="button" className={cls.join(' ')} onClick={() => onPick(d)}
              aria-current={iso === todayISO ? 'date' : undefined}
              aria-label={`${fmtDMY(iso)}${has ? ', có lịch' : ''}`}>
              {d.getDate()}
              {has && <span className="mini-dot" aria-hidden="true" />}
            </button>
          );
        })}
      </div>
    </div>
  );
}

/* ============================================================
   Component: Menu trái (PC) / thanh dưới (điện thoại)
   ============================================================ */
const NAV_ITEMS = [
  { id: 'calendar', label: 'Lịch', icon: 'CalendarDays' },
  { id: 'tasks', label: 'Việc cần làm', icon: 'ListChecks' },
  { id: 'list', label: 'Lịch trình', icon: 'ListTodo' },
  { id: 'settings', label: 'Cài đặt', icon: 'Settings' },
];

function NavRail({ page, onPage, dueCount }) {
  return (
    <nav className="rail" aria-label="Điều hướng chính">
      <div className="rail-brand">
        <Logo size={38} />
        <div className="rail-name"><strong>RICO</strong><span>Routine, Itinerary &amp; Calendar Organizer</span></div>
      </div>
      <div className="rail-items">
        {NAV_ITEMS.map((it) => (
          <button key={it.id} type="button" className={`rail-item${page === it.id ? ' active' : ''}`}
            aria-current={page === it.id ? 'page' : undefined} onClick={() => onPage(it.id)}>
            <Icon name={it.icon} size={20} />
            <span className="rail-label">{it.label}</span>
            {it.id === 'tasks' && dueCount > 0 && <span className="tab-badge" aria-label={`${dueCount} việc chưa làm`}>{dueCount}</span>}
          </button>
        ))}
      </div>
      <div className="rail-foot">Make time work for you.</div>
    </nav>
  );
}

/* ============================================================
   Component: Xem theo tháng
   ============================================================ */
function MonthGrid({ cursor, events, now, slideDir, onOpenDay, onAddDay, onCardClick }) {
  const first = new Date(cursor.getFullYear(), cursor.getMonth(), 1);
  const lastDay = new Date(cursor.getFullYear(), cursor.getMonth() + 1, 0).getDate();
  const rows = Math.ceil((wdIndex(first) + lastDay) / 7);
  const gridFirstMs = startOfWeek(first).getTime();
  const cells = useMemo(() => Array.from({ length: rows * 7 }, (_, i) => addDays(new Date(gridFirstMs), i)), [rows, gridFirstMs]);
  const byDay = useMemo(() => {
    const map = new Map();
    events.forEach((s) => occurrencesInRange(s, cells[0], cells[cells.length - 1]).forEach((o) => {
      if (!map.has(o.date)) map.set(o.date, []);
      map.get(o.date).push(o);
    }));
    map.forEach((list) => list.sort((a, b) => a.startTime.localeCompare(b.startTime)));
    return map;
  }, [events, cells]);
  const todayISO = toISODate(now);
  const MAX = 3;
  return (
    <div className="grid-card month-card">
      <div className="month-scroll">
        <div key={toISODate(first)} className={`month-inner slide-${slideDir}`}>
          <div className="month-head">{WEEKDAYS.map((w) => <div key={w} className="mh">{w}</div>)}</div>
          <div className="month-body" style={{ gridTemplateRows: `repeat(${rows}, minmax(104px, 1fr))` }}>
            {cells.map((d) => {
              const iso = toISODate(d);
              const list = byDay.get(iso) || [];
              const more = list.length - MAX;
              const cls = ['month-cell'];
              if (d.getMonth() !== cursor.getMonth()) cls.push('outside');
              if (iso === todayISO) cls.push('today');
              return (
                <div key={iso} className={cls.join(' ')} data-iso={iso} onClick={() => onAddDay(iso)}>
                  <button type="button" className="month-num" aria-label={`Xem ngày ${fmtDMY(iso)}${list.length ? `, ${list.length} sự kiện` : ''}`}
                    onClick={(e) => { e.stopPropagation(); onOpenDay(d); }}>{d.getDate()}</button>
                  <div className="month-chips">
                    {list.slice(0, MAX).map((o) => (
                      <button key={o.key} type="button" className={`month-chip${o.done ? ' done' : ''}`}
                        style={{ '--ev-color': `var(--cat-${o.category})`, '--ev-bg': `var(--cat-${o.category}-bg)` }}
                        title={`${o.title}\n${o.startTime} – ${o.endTime}`}
                        aria-label={`${o.title}, ${fmtDMY(o.date)}, ${o.startTime} đến ${o.endTime}${o.done ? ', đã làm' : ''}`}
                        onClick={(e) => { e.stopPropagation(); onCardClick(o.seriesId, o.date); }}>
                        <span className="t">{o.startTime} {o.title}</span>
                      </button>
                    ))}
                    {more > 0 && (
                      <button type="button" className="month-more" onClick={(e) => { e.stopPropagation(); onOpenDay(d); }}>+{more} nữa</button>
                    )}
                  </div>
                </div>
              );
            })}
          </div>
        </div>
      </div>
    </div>
  );
}

/* ============================================================
   Component: Bảng bên phải (lịch tháng nhỏ + việc hôm nay)
   ============================================================ */
function TodayList({ events, now, onOpen }) {
  const iso = toISODate(now);
  const items = useMemo(() => {
    const d = parseISODate(iso);
    const out = [];
    events.forEach((s) => occurrencesInRange(s, d, d).forEach((o) => out.push(o)));
    return out.sort((a, b) => a.startTime.localeCompare(b.startTime));
  }, [events, iso]);
  if (!items.length) return <div className="empty-note">Hôm nay chưa có sự kiện nào.</div>;
  return (
    <ul className="today-list">
      {items.map((o) => (
        <li key={o.key}>
          <button type="button" className={`today-item${o.done ? ' done' : ''}`} style={{ '--c': `var(--cat-${o.category})` }}
            onClick={() => onOpen(o.seriesId, o.date)}>
            <span className="dot" aria-hidden="true" />
            <span className="today-main"><span className="today-title">{o.title}</span><span className="today-time">{o.startTime} – {o.endTime}</span></span>
            {o.done && <Icon name="Check" size={14} />}
          </button>
        </li>
      ))}
    </ul>
  );
}

function Sidebar({ open, onClose, events, now, weekStart, spanDays, onPickDate, onOpenOccurrence }) {
  return (
    <aside className={`sidebar${open ? ' open' : ''}`} aria-label="Lịch tháng và hôm nay">
      <div className="sidebar-head">
        <h2>Lịch của tôi</h2>
        <button type="button" className="icon-btn" aria-label="Đóng bảng bên" onClick={onClose}><Icon name="X" /></button>
      </div>
      <div className="sidebar-scroll">
        <section className="panel">
          <h3>Lịch tháng</h3>
          <MiniCalendar weekStart={weekStart} spanDays={spanDays} events={events} onPick={onPickDate} />
        </section>
        <section className="panel">
          <h3>Hôm nay</h3>
          <TodayList events={events} now={now} onOpen={onOpenOccurrence} />
        </section>
      </div>
    </aside>
  );
}

/* ============================================================
   Trang: Lịch trình (danh sách các chuỗi sự kiện)
   ============================================================ */
function SchedulePage({ events, onEditSeries, onDeleteSeries, onAdd }) {
  const [query, setQuery] = useState('');
  const groups = useMemo(() => {
    const q = fold(query.trim());
    const filtered = events.filter((s) => !q || fold(s.title).includes(q));
    const sorted = [...filtered].sort((a, b) => a.startTime.localeCompare(b.startTime) || a.title.localeCompare(b.title, 'vi'));
    return CATEGORIES.map((c) => ({ ...c, items: sorted.filter((s) => s.category === c.id) })).filter((g) => g.items.length);
  }, [events, query]);
  return (
    <div className="page-wrap">
      <div className="page-card">
        <section className="panel">
          <h3>Lịch trình ({events.length})</h3>
          <input type="search" placeholder="Tìm theo tiêu đề…" aria-label="Tìm sự kiện" value={query} onChange={(e) => setQuery(e.target.value)} />
          {events.length === 0 && (
            <div className="empty-note" style={{ marginTop: 12 }}>
              Chưa có sự kiện nào. <button type="button" className="btn btn-sm" style={{ marginLeft: 8 }} onClick={onAdd}><Icon name="Plus" size={14} /> Thêm sự kiện</button>
            </div>
          )}
          {events.length > 0 && groups.length === 0 && <div className="empty-note" style={{ marginTop: 12 }}>Không tìm thấy sự kiện phù hợp.</div>}
          {groups.map((g) => (
            <div className="list-group" key={g.id}>
              <h4 style={{ '--c': `var(--cat-${g.id})` }}><span className="dot" />{g.label} <span className="muted">({g.items.length})</span></h4>
              <ul className="sched-list">
                {g.items.map((s) => (
                  <li key={s.id} className="sched-item" style={{ '--c': `var(--cat-${s.category})` }}>
                    <button type="button" className="sched-main" onClick={() => onEditSeries(s.id)} aria-label={`Sửa ${s.title}`}>
                      <span className="sched-title">{s.title}</span>
                      <span className="sched-sub">{describeSeries(s)}</span>
                    </button>
                    <button type="button" className="icon-btn danger" aria-label={`Xóa ${s.title}`} onClick={() => onDeleteSeries(s.id)}>
                      <Icon name="Trash2" size={16} />
                    </button>
                  </li>
                ))}
              </ul>
            </div>
          ))}
        </section>
      </div>
    </div>
  );
}

/* ============================================================
   Trang: Cài đặt
   ============================================================ */
function SettingsPage(props) {
  const {
    data, perm, onToggleNotify, onTestChime, onUpdateSettings, onExport, onImportFile,
    syncStatus, onSaveSync, onToggleSync, onTestEmail, onSyncNow, onCopyLink, onTestPhrase, onOpenShortcuts,
  } = props;
  const { settings } = data;
  const fileRef = useRef(null);
  const notifyActive = perm === 'granted' && settings.notifyOn;
  let notifyLabel = 'Bật thông báo';
  let notifyBadge = null;
  if (perm === 'unsupported') notifyLabel = 'Không hỗ trợ thông báo';
  else if (perm === 'denied') { notifyLabel = 'Thông báo bị chặn'; notifyBadge = <span className="status-badge bad">Đã chặn</span>; }
  else if (notifyActive) { notifyLabel = 'Thông báo đang bật'; notifyBadge = <span className="status-badge good">Bật</span>; }
  const themeVal = settings.theme === 'light' || settings.theme === 'dark' ? settings.theme : 'auto';

  return (
    <div className="page-wrap">
      <div className="page-card">
        <section className="panel">
          <h3>Giao diện</h3>
          <div className="segmented" role="group" aria-label="Giao diện">
            {[['auto', 'Theo hệ thống'], ['light', 'Sáng'], ['dark', 'Tối']].map(([v, l]) => (
              <button key={v} type="button" aria-pressed={themeVal === v} onClick={() => onUpdateSettings({ theme: v === 'auto' ? null : v })}>{l}</button>
            ))}
          </div>
        </section>

        <section className="panel">
          <h3>Thông báo và âm thanh</h3>
          <div className="stack">
            <button type="button" className={`btn btn-block${notifyActive ? ' is-on' : ''}`} onClick={onToggleNotify}
              disabled={perm === 'unsupported'} aria-pressed={notifyActive}>
              <Icon name={notifyActive ? 'Bell' : 'BellOff'} size={16} /> {notifyLabel} {notifyBadge}
            </button>
            <button type="button" className="btn btn-block" onClick={onTestChime}>
              <Icon name="Volume2" size={16} /> Thử chuông báo
            </button>
            <label className="switch-row">
              <input type="checkbox" role="switch" checked={settings.soundOn} onChange={(e) => onUpdateSettings({ soundOn: e.target.checked })} />
              <span>Phát chuông khi nhắc</span>
            </label>
            <div>
              <label htmlFor="vol" className="status-line">Âm lượng: {Math.round(settings.volume * 100)}%</label>
              <input id="vol" type="range" min="0" max="1" step="0.05" value={settings.volume}
                onChange={(e) => onUpdateSettings({ volume: Number(e.target.value) })} />
            </div>
            <p className="hint">Thông báo trên trang chỉ hoạt động khi tab còn mở (kể cả ở chế độ nền). Khi đóng tab, hãy dùng nhắc qua email bên dưới.</p>
          </div>
        </section>

        <section className="panel">
          <h3>Câu nhắc cho việc cần làm</h3>
          <div className="stack">
            <label className="switch-row">
              <input type="checkbox" role="switch" checked={settings.taskSpeak} onChange={(e) => onUpdateSettings({ taskSpeak: e.target.checked })} />
              <span>Đọc to câu nhắc</span>
            </label>
            <div>
              <label htmlFor="taskPhrase" className="status-line">Câu nhắc</label>
              <input id="taskPhrase" type="text" maxLength={120} value={settings.taskPhrase}
                placeholder={DEFAULT_SETTINGS.taskPhrase} onChange={(e) => onUpdateSettings({ taskPhrase: e.target.value })} />
            </div>
            <button type="button" className="btn btn-block" onClick={onTestPhrase}><Icon name="Volume2" size={16} /> Thử câu nhắc</button>
            <p className="hint">{'Chèn {ghi chú} để thay bằng ghi chú của việc (trống thì dùng tên việc), {tên} để chèn tên việc. Giọng đọc tiếng Việt tùy thiết bị; không có thì chỉ phát chuông và hiện chữ.'}</p>
          </div>
        </section>

        <section className="panel">
          <h3>Sao lưu và khôi phục</h3>
          <div className="row">
            <button type="button" className="btn" onClick={onExport}><Icon name="Download" size={16} /> Xuất .json</button>
            <button type="button" className="btn" onClick={() => fileRef.current && fileRef.current.click()}><Icon name="Upload" size={16} /> Nhập .json</button>
            <input ref={fileRef} type="file" accept="application/json,.json" hidden
              onChange={(e) => { const f = e.target.files && e.target.files[0]; if (f) onImportFile(f); e.target.value = ''; }} />
          </div>
          <p className="hint" style={{ marginTop: 8 }}>File sao lưu không chứa URL và token email.</p>
        </section>

        <section className="panel">
          <h3>Đồng bộ thiết bị và nhắc email</h3>
          <EmailSyncPanel settings={settings} status={syncStatus} onSave={onSaveSync} onToggle={onToggleSync}
            onTest={onTestEmail} onSyncNow={onSyncNow} onCopyLink={onCopyLink} />
        </section>

        <section className="panel about">
          <h3>Giới thiệu</h3>
          <div className="about-row">
            <Logo size={44} />
            <div>
              <strong>RICO</strong>
              <div className="muted">Routine, Itinerary &amp; Calendar Organizer</div>
              <div className="muted">Make time work for you.</div>
            </div>
          </div>
          <button type="button" className="btn btn-sm" style={{ marginTop: 10 }} onClick={onOpenShortcuts}><Icon name="Keyboard" size={15} /> Xem phím tắt</button>
        </section>
      </div>
    </div>
  );
}

/* ============================================================
   Hook: theo dõi giao diện tối của hệ thống
   ============================================================ */
function useSystemDark() {
  const mq = window.matchMedia ? window.matchMedia('(prefers-color-scheme: dark)') : null;
  const [dark, setDark] = useState(mq ? mq.matches : false);
  useEffect(() => {
    if (!mq) return undefined;
    const h = (e) => setDark(e.matches);
    if (mq.addEventListener) mq.addEventListener('change', h); else mq.addListener(h);
    return () => { if (mq.removeEventListener) mq.removeEventListener('change', h); else mq.removeListener(h); };
  }, []);
  return dark;
}

/* ============================================================
   Component: App
   ============================================================ */
function App() {
  const [data, setData] = useState(loadData);
  const dataRef = useRef(data);
  dataRef.current = data;
  // cursor: ngày đang xem; mode: chế độ xem 'day' | 'week' | 'month'
  const [cursor, setCursor] = useState(() => startOfDay(new Date()));
  const [mode, setMode] = useState(() => {
    try { const m = localStorage.getItem('tp_cal_mode'); return m === 'day' || m === 'month' ? m : 'week'; } catch (e) { return 'week'; }
  });
  const weekStart = useMemo(() => startOfWeek(cursor), [cursor]);
  const [slideDir, setSlideDir] = useState('next'); // hướng trượt khi đổi tuần
  const [now, setNow] = useState(() => new Date());
  const [scrollSignal, setScrollSignal] = useState(0);
  const [sidebarOpen, setSidebarOpen] = useState(false);
  const [shortcutsOpen, setShortcutsOpen] = useState(false);
  const keyActions = useRef({}); // các hành động của phím tắt (luôn là bản mới nhất)
  // PC: thanh bên có thể ẩn/hiện (nhớ lại lựa chọn). Điện thoại: thanh bên là ngăn kéo.
  const [sideCollapsed, setSideCollapsed] = useState(() => {
    try { return localStorage.getItem('tp_side_collapsed') === '1'; } catch (e) { return false; }
  });
  const isMobileView = () => window.matchMedia('(max-width: 960px)').matches;
  const setPanel = (show) => {
    if (isMobileView()) { setSidebarOpen(show); return; }
    setSideCollapsed(!show);
    try { localStorage.setItem('tp_side_collapsed', show ? '0' : '1'); } catch (e) { /* bỏ qua */ }
  };
  const togglePanel = () => setPanel(isMobileView() ? !sidebarOpen : sideCollapsed);
  const [modal, setModal] = useState(null);       // { mode }
  const [scopeAsk, setScopeAsk] = useState(null); // { seriesId, date }
  const [confirm, setConfirm] = useState(null);
  const [importAsk, setImportAsk] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [perm, setPerm] = useState(getPerm);
  const systemDark = useSystemDark();
  const settings = data.settings;
  const resolvedTheme = settings.theme || (systemDark ? 'dark' : 'light');
  const [page, setPage] = useState('calendar');  // 'calendar' | 'tasks' | 'list' | 'settings'
  const [taskModal, setTaskModal] = useState(null); // { mode }
  const [doneAsk, setDoneAsk] = useState(null);     // việc đang xác nhận tick
  const calEvents = useMemo(() => data.events.filter((x) => !isTask(x)), [data.events]);
  const taskList = useMemo(() => data.events.filter(isTask), [data.events]);

  const [syncStatus, setSyncStatus] = useState(() => {
    if (data.settings.syncEnabled && localStorage.getItem(DIRTY_KEY) === '1') return { state: 'pending', message: 'Chờ đồng bộ…' };
    if (data.settings.lastSync) return { state: 'ok', message: `Đã đồng bộ lúc ${fmtClock(data.settings.lastSync)}` };
    return { state: 'idle', message: 'Chưa đồng bộ' };
  });

  /* ----- Toast ----- */
  const pushToast = useCallback((t) => {
    const id = uid();
    setToasts((list) => [...list.slice(-4), { kind: 'info', ...t, id }]);
    const ttl = t.ttl || (t.kind === 'reminder' ? 15000 : 5000);
    setTimeout(() => setToasts((l) => l.filter((x) => x.id !== id)), ttl);
  }, []);
  const dismissToast = useCallback((id) => setToasts((l) => l.filter((x) => x.id !== id)), []);

  /* ----- Cập nhật dữ liệu ----- */
  const mutateEvents = useCallback((fn) => {
    setData((d) => {
      const events = fn(d.events);
      const keep = new Set(events.map((s) => s.id));
      const now = Date.now();
      const tombstones = { ...(d.tombstones || {}) };
      d.events.forEach((s) => { if (!keep.has(s.id)) tombstones[s.id] = now; }); // đánh dấu đã xóa
      keep.forEach((id) => { delete tombstones[id]; });
      return { ...d, events, tombstones, updatedAt: now };
    });
  }, []);
  const updateSettings = useCallback((patch) => {
    setData((d) => ({ ...d, settings: { ...d.settings, ...patch } }));
  }, []);

  /* ----- Lưu cục bộ (offline-first) ----- */
  useEffect(() => {
    try { localStorage.setItem(STORAGE_KEY, JSON.stringify(data)); } catch (e) {
      pushToast({ kind: 'error', title: 'Không thể lưu dữ liệu', message: 'Bộ nhớ trình duyệt đầy hoặc đang bị chặn. Hãy xuất file .json để sao lưu.' });
    }
  }, [data, pushToast]);

  /* ----- Giao diện Sáng/Tối ----- */
  useEffect(() => { document.documentElement.setAttribute('data-theme', resolvedTheme); }, [resolvedTheme]);

  /* ----- Mở khóa âm thanh ngay lần chạm đầu tiên ----- */
  useEffect(() => {
    const unlock = () => AudioEngine.ensure();
    window.addEventListener('pointerdown', unlock, { once: true });
    window.addEventListener('keydown', unlock, { once: true });
    return () => { window.removeEventListener('pointerdown', unlock); window.removeEventListener('keydown', unlock); };
  }, []);

  /* ----- Quét nền: phát hiện sự kiện sắp tới và nhắc ----- */
  useEffect(() => {
    const fire = (o, startMs) => {
      const st = dataRef.current.settings;
      const mins = Math.max(0, Math.ceil((startMs - Date.now()) / 60000));
      const when = mins >= 60 ? `${Math.floor(mins / 60)} giờ ${mins % 60 ? (mins % 60) + ' phút' : ''}` : `${mins} phút`;
      const body = `${o.startTime} – ${o.endTime} · còn khoảng ${when.trim()}`;
      pushToast({ kind: 'reminder', title: `⏰ ${o.title}`, message: body });
      if (st.soundOn) AudioEngine.chime(st.volume);
      if (st.notifyOn) showDesktopNotification(`⏰ ${o.title}`, body, `${o.seriesId}|${o.date}`);
    };
    const fireTask = (t, k) => {
      const st = dataRef.current.settings;
      const text = fillPhrase(st.taskPhrase, t);
      const total = t.repeatMode === 'eod' ? '' : `/${t.repeatN === 3 ? 3 : 2}`;
      const body = `${t.startTime} · nhắc lần ${k + 1}${total}${k > 0 ? ' · bạn chưa tick xong' : ''}`;
      pushToast({ kind: 'reminder', title: `⏰ ${text}`, message: body, ttl: 20000 });
      if (st.soundOn) AudioEngine.chime(st.volume);
      if (st.soundOn && st.taskSpeak) setTimeout(() => speakText(text, st.volume), 1300);
      if (st.notifyOn) showDesktopNotification(`⏰ ${t.title}`, `${text} (${body})`, `task|${t.id}|${t.date}|${k}`);
    };
    const scan = () => {
      const nowD = new Date();
      setNow(nowD);
      const nowMs = nowD.getTime();
      const from = startOfDay(nowD);
      const to = addDays(from, 2);
      const notified = loadNotified();
      let changed = false;
      dataRef.current.events.forEach((s) => {
        occurrencesInRange(s, from, to).forEach((o) => {
          if (o.remindMin <= 0 || o.done) return;
          const startMs = dateTimeMs(o.date, o.startTime);
          const key = `${o.seriesId}|${o.date}|${o.startTime}`;
          // Báo bù nếu lỡ mốc nhưng sự kiện chưa bắt đầu
          if (nowMs >= startMs - o.remindMin * 60000 && nowMs < startMs && !notified[key]) {
            notified[key] = nowMs;
            changed = true;
            fire(o, startMs);
          }
        });
      });
      // Việc cần làm: nhắc đúng giờ rồi mỗi 1 tiếng cho tới khi tick (hoặc hết lượt)
      const yIso = toISODate(addDays(from, -1));
      const tIso = toISODate(from);
      dataRef.current.events.forEach((t) => {
        if (!isTask(t) || (t.date !== yIso && t.date !== tIso) || taskDone(t)) return;
        const startMs = dateTimeMs(t.date, t.startTime);
        if (nowMs < startMs) return;
        const k = Math.floor((nowMs - startMs) / HOUR_MS);
        if (k > taskLastK(t)) return;
        const pre = `task|${t.id}|${t.date}|${t.startTime}|`;
        if (notified[pre + k]) return;
        for (let i = 0; i <= k; i += 1) notified[pre + i] = nowMs; // lỡ mốc cũ thì không báo dồn
        changed = true;
        fireTask(t, k);
      });
      if (changed) saveNotified(notified);
    };
    scan();
    const timer = setInterval(scan, 30000);
    const onVisible = () => {
      if (document.visibilityState === 'visible') { setPerm(getPerm()); scan(); }
    };
    document.addEventListener('visibilitychange', onVisible);
    return () => { clearInterval(timer); document.removeEventListener('visibilitychange', onVisible); };
  }, [pushToast]);

  /* ----- Đồng bộ nhắc qua email (Apps Script) ----- */
  const syncRef = useRef({ timer: null, busy: false, again: false });

  const doSync = useCallback(async () => {
    const d = dataRef.current;
    const s = d.settings;
    if (!(s.syncEnabled && s.syncUrl && s.syncToken)) return;
    if (!navigator.onLine) { setSyncStatus({ state: 'offline', message: 'Đang chờ có mạng để đồng bộ.' }); return; }
    if (syncRef.current.busy) { syncRef.current.again = true; return; }
    syncRef.current.busy = true;
    setSyncStatus((p) => (p.state === 'ok' ? p : { state: 'syncing', message: 'Đang đồng bộ…' }));
    try {
      // Đẩy lịch của máy này lên và nhận về bản đã gộp từ máy chủ (hai chiều)
      const res = await postToScript(s.syncUrl, {
        action: 'sync2', token: s.syncToken,
        series: toRemoteSeries(d), reminders: buildReminderPayload(d.events),
      });
      if (res.ok) {
        const merged = mergeRemote(dataRef.current, res.series);
        if (merged.changed) {
          setData((cur) => {
            const m = mergeRemote(cur, res.series);
            return m.changed ? { ...cur, events: m.events, tombstones: m.tombstones } : cur;
          });
          pushToast({ kind: 'info', title: 'Đã cập nhật lịch từ thiết bị khác' });
        }
        if (dataRef.current.updatedAt === d.updatedAt) { try { localStorage.removeItem(DIRTY_KEY); } catch (e) { /* bỏ qua */ } }
        const at = Date.now();
        updateSettings({ lastSync: at });
        setSyncStatus({ state: 'ok', message: `Đã đồng bộ lúc ${fmtClock(at)} · ${res.count != null ? res.count : 0} sự kiện trên máy chủ` });
      } else if (res.error === 'forbidden') {
        setSyncStatus({ state: 'error', message: 'Token không đúng. Kiểm tra lại token trong Script Properties.' });
      } else if (res.error === 'bad_action') {
        setSyncStatus({ state: 'error', message: 'Script chưa phải bản mới. Dán Code.gs mới rồi triển khai "Phiên bản mới".' });
      } else if (res.error === 'busy') {
        setSyncStatus({ state: 'error', message: 'Máy chủ đang bận, sẽ thử lại ở lần đồng bộ sau.' });
      } else {
        setSyncStatus({ state: 'error', message: `Máy chủ báo lỗi: ${res.error || 'không rõ'}` });
      }
    } catch (e) {
      setSyncStatus({ state: 'error', message: e.message });
    } finally {
      syncRef.current.busy = false;
      if (syncRef.current.again) { syncRef.current.again = false; syncRef.current.timer = setTimeout(() => doSync(), 1500); }
    }
  }, [updateSettings, pushToast]);

  const scheduleSync = useCallback((delay = 3000) => {
    const s = dataRef.current.settings;
    if (!(s.syncEnabled && s.syncUrl && s.syncToken)) return;
    clearTimeout(syncRef.current.timer);
    setSyncStatus((p) => (navigator.onLine ? { state: 'pending', message: 'Chờ đồng bộ…' } : { state: 'offline', message: 'Đang chờ có mạng để đồng bộ.', at: p.at }));
    syncRef.current.timer = setTimeout(() => doSync(false), delay);
  }, [doSync]);

  // Khi danh sách sự kiện thay đổi: đánh dấu cần đồng bộ, gộp sau 3 giây
  const eventsFirst = useRef(true);
  useEffect(() => {
    if (eventsFirst.current) {
      eventsFirst.current = false;
      if (localStorage.getItem(DIRTY_KEY) === '1') scheduleSync(1500);
      return;
    }
    try { localStorage.setItem(DIRTY_KEY, '1'); } catch (e) { /* bỏ qua */ }
    scheduleSync(3000);
  }, [data.events, scheduleSync]);

  // Khi bật đồng bộ hoặc đổi URL/token
  const syncCfgFirst = useRef(true);
  useEffect(() => {
    if (syncCfgFirst.current) { syncCfgFirst.current = false; return; }
    if (settings.syncEnabled && settings.syncUrl && settings.syncToken) {
      try { localStorage.setItem(DIRTY_KEY, '1'); } catch (e) { /* bỏ qua */ }
      scheduleSync(500);
    }
  }, [settings.syncEnabled, settings.syncUrl, settings.syncToken, scheduleSync]);

  // Có mạng lại thì gửi bù
  useEffect(() => {
    const onOnline = () => { if (localStorage.getItem(DIRTY_KEY) === '1') scheduleSync(500); };
    window.addEventListener('online', onOnline);
    return () => window.removeEventListener('online', onOnline);
  }, [scheduleSync]);

  // Tự đồng bộ khi mở app, khi quay lại tab, khi có mạng và mỗi 2 phút
  useEffect(() => {
    if (!(settings.syncEnabled && settings.syncUrl && settings.syncToken)) return undefined;
    const tick = () => { if (document.visibilityState === 'visible') doSync(); };
    const first = setTimeout(tick, 800);
    const timer = setInterval(tick, POLL_MS);
    document.addEventListener('visibilitychange', tick);
    window.addEventListener('online', tick);
    return () => {
      clearTimeout(first);
      clearInterval(timer);
      document.removeEventListener('visibilitychange', tick);
      window.removeEventListener('online', tick);
    };
  }, [settings.syncEnabled, settings.syncUrl, settings.syncToken, doSync]);

  // Link cấu hình: mở trên thiết bị khác để tự điền URL + token (nằm sau dấu #, không gửi lên máy chủ web)
  const copyConfigLink = async () => {
    const st = dataRef.current.settings;
    if (!(st.syncUrl && st.syncToken)) {
      pushToast({ kind: 'error', title: 'Chưa có cấu hình', message: 'Hãy nhập URL, token và bấm "Lưu" trước.' });
      return;
    }
    const payload = encodeURIComponent(btoa(JSON.stringify({ u: st.syncUrl, t: st.syncToken })));
    const link = `${location.origin}${location.pathname}#cfg=${payload}`;
    try {
      await navigator.clipboard.writeText(link);
      pushToast({ kind: 'success', title: 'Đã sao chép link cấu hình', ttl: 9000,
        message: 'Mở link này trên thiết bị khác. Link chứa token, đừng gửi cho người lạ.' });
    } catch (e) {
      window.prompt('Sao chép link cấu hình (chứa token, đừng chia sẻ):', link);
    }
  };

  // Nhận link cấu hình khi mở trang (hỏi xác nhận trước khi áp dụng)
  useEffect(() => {
    const m = /[#&]cfg=([^&]+)/.exec(location.hash || '');
    if (!m) return;
    try { history.replaceState(null, '', location.pathname + location.search); } catch (e) { /* bỏ qua */ }
    try {
      const cfg = JSON.parse(atob(decodeURIComponent(m[1])));
      const okUrl = typeof cfg.u === 'string' && /^https:\/\/script\.google\.com\/macros\//.test(cfg.u);
      if (!okUrl || typeof cfg.t !== 'string' || !cfg.t) throw new Error('bad');
      setConfirm({
        title: 'Áp dụng cấu hình đồng bộ?',
        message: `Thiết bị này sẽ đồng bộ lịch với Google Apps Script: ...${cfg.u.slice(-24)}. Chỉ đồng ý nếu link do chính bạn tạo.`,
        confirmLabel: 'Áp dụng',
        onConfirm: () => {
          updateSettings({ syncUrl: cfg.u, syncToken: cfg.t, syncEnabled: true });
          pushToast({ kind: 'success', title: 'Đã áp dụng cấu hình', message: 'Đang tải lịch từ máy chủ…' });
        },
      });
    } catch (e) {
      pushToast({ kind: 'error', title: 'Link cấu hình không hợp lệ' });
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const saveSyncSettings = (url, token) => {
    updateSettings({ syncUrl: url, syncToken: token });
    pushToast({ kind: 'success', title: 'Đã lưu cấu hình email' });
  };
  const toggleSync = (checked) => {
    const s = dataRef.current.settings;
    if (checked && !(s.syncUrl && s.syncToken)) {
      pushToast({ kind: 'error', title: 'Chưa thể bật', message: 'Hãy nhập URL Web App và token rồi bấm "Lưu" trước.' });
      return;
    }
    updateSettings({ syncEnabled: checked });
    if (!checked) setSyncStatus({ state: 'idle', message: 'Đã tắt đồng bộ email.' });
  };
  const testEmail = async () => {
    const s = dataRef.current.settings;
    setSyncStatus({ state: 'syncing', message: 'Đang gửi email thử…' });
    try {
      const res = await postToScript(s.syncUrl, { action: 'test', token: s.syncToken });
      if (res.ok) {
        setSyncStatus({ state: 'ok', message: 'Đã gửi email thử. Hãy kiểm tra hộp thư (cả mục Spam).' });
        pushToast({ kind: 'success', title: 'Đã gửi email thử' });
      } else {
        const msg = res.error === 'forbidden' ? 'Token không đúng.' : `Máy chủ báo lỗi: ${res.error || 'không rõ'}`;
        setSyncStatus({ state: 'error', message: msg });
        pushToast({ kind: 'error', title: 'Gửi thử thất bại', message: msg });
      }
    } catch (e) {
      setSyncStatus({ state: 'error', message: e.message });
      pushToast({ kind: 'error', title: 'Gửi thử thất bại', message: e.message });
    }
  };

  /* ----- Thông báo trình duyệt ----- */
  const toggleNotify = async () => {
    AudioEngine.ensure();
    if (perm === 'unsupported') {
      pushToast({ kind: 'error', title: 'Trình duyệt không hỗ trợ thông báo', message: 'Nhắc lịch vẫn hiện trong ứng dụng và phát chuông.' });
      return;
    }
    if (perm === 'denied') {
      pushToast({ kind: 'error', title: 'Thông báo đang bị chặn', ttl: 9000,
        message: 'Bấm biểu tượng ổ khóa cạnh thanh địa chỉ, chọn Cho phép thông báo rồi tải lại trang. Trong lúc đó, nhắc lịch vẫn hiện trong ứng dụng.' });
      return;
    }
    if (settings.notifyOn) {
      updateSettings({ notifyOn: false });
      pushToast({ kind: 'info', title: 'Đã tắt thông báo đẩy' });
      return;
    }
    if (perm === 'default') {
      const result = await new Promise((resolve) => {
        const p = Notification.requestPermission(resolve);
        if (p && p.then) p.then(resolve);
      });
      setPerm(result);
      if (result !== 'granted') {
        pushToast({ kind: 'error', title: 'Chưa được cấp quyền thông báo', message: 'Nhắc lịch vẫn hiện trong ứng dụng và phát chuông.' });
        return;
      }
    }
    updateSettings({ notifyOn: true });
    pushToast({ kind: 'success', title: 'Đã bật thông báo' });
    showDesktopNotification('Đã bật thông báo', 'Bạn sẽ nhận nhắc lịch khi tab còn mở.', 'enabled');
  };

  /* ----- Thêm / sửa / xóa ----- */
  const defaultSlot = () => {
    const days = mode === 'day' ? [toISODate(cursor)] : Array.from({ length: 7 }, (_, i) => toISODate(addDays(weekStart, i)));
    const todayISO = toISODate(now);
    const date = days.includes(todayISO) ? todayISO : days[0];
    const cfg = HOUR_OPTIONS[settings.hours] || HOUR_OPTIONS['6-23'];
    const nowMin = now.getHours() * 60 + now.getMinutes();
    const start = Math.min(Math.max(Math.ceil(nowMin / 60) * 60, cfg.start * 60), 22 * 60);
    return { date, startTime: minToTime(start), endTime: minToTime(start + 60) };
  };
  const openNew = (prefill) => setModal({ mode: { type: 'new', prefill: prefill || defaultSlot() } });

  const openOccurrence = (seriesId, date) => {
    const s = dataRef.current.events.find((x) => x.id === seriesId);
    if (!s) return;
    if (s.kind === 'once') setModal({ mode: { type: 'edit', seriesId, occDate: date, scope: 'all' } });
    else setScopeAsk({ seriesId, date });
  };
  const editSeries = (id) => {
    const s = dataRef.current.events.find((x) => x.id === id);
    if (!s) return;
    setModal({ mode: { type: 'edit', seriesId: id, occDate: s.kind === 'once' ? s.date : s.rangeStart, scope: 'all' } });
    setSidebarOpen(false);
  };

  const saveForm = (form, mode) => {
    const nowTs = Date.now();
    const noteDate = noteDateFor(form, mode);
    const noteText = form.note || '';
    mutateEvents((list) => {
      if (mode.type === 'new') return [...list, withNote(formToSeries(form, null), noteDate, noteText, nowTs)];
      const idx = list.findIndex((s) => s.id === mode.seriesId);
      if (idx < 0) return list;
      const s = list[idx];
      const next = [...list];
      if (mode.scope === 'all') {
        next[idx] = withNote(formToSeries(form, s), noteDate, noteText, nowTs);
      } else if (mode.scope === 'this') {
        next[idx] = withNote({
          ...s, updatedAt: nowTs,
          exceptions: {
            ...s.exceptions,
            [mode.occDate]: {
              title: form.title.trim(), category: form.category, startTime: form.startTime,
              endTime: form.endTime, remindMin: Number(form.remindMin),
            },
          },
        }, noteDate, noteText, nowTs);
      } else {
        // 'future': tách chuỗi thành hai phần
        const prevEnd = toISODate(addDays(parseISODate(mode.occDate), -1));
        const kept = {};
        const moved = {};
        Object.keys(s.exceptions || {}).forEach((k) => {
          if (k < mode.occDate) kept[k] = s.exceptions[k];
          else if (s.exceptions[k] === 'deleted') moved[k] = 'deleted';
        });
        const tail = formToSeries(form, null);
        const keptDone = {};
        Object.keys(s.done || {}).forEach((k) => { if (k < mode.occDate) keptDone[k] = s.done[k]; else tail.done[k] = s.done[k]; });
        Object.keys(moved).forEach((k) => { if (k >= tail.rangeStart && k <= tail.rangeEnd) tail.exceptions[k] = 'deleted'; });
        const keptNotes = {};
        Object.keys(s.notes || {}).forEach((k) => { if (k < mode.occDate) keptNotes[k] = s.notes[k]; else tail.notes[k] = s.notes[k]; });
        const tailF = withNote(tail, noteDate, noteText, nowTs);
        if (prevEnd < s.rangeStart) next.splice(idx, 1, tailF);
        else next.splice(idx, 1, { ...s, rangeEnd: prevEnd, exceptions: kept, done: keptDone, notes: keptNotes, updatedAt: nowTs }, tailF);
      }
      return next;
    });
    setModal(null);
    pushToast({ kind: 'success', title: mode.type === 'new' ? 'Đã thêm sự kiện' : 'Đã lưu thay đổi' });
  };

  const deleteOcc = (seriesId, date, scope) => {
    mutateEvents((list) => {
      const s = list.find((x) => x.id === seriesId);
      if (!s) return list;
      if (scope === 'all' || s.kind === 'once') return list.filter((x) => x.id !== seriesId);
      if (scope === 'this') {
        return list.map((x) => (x.id === seriesId ? { ...x, updatedAt: Date.now(), exceptions: { ...x.exceptions, [date]: 'deleted' } } : x));
      }
      const prevEnd = toISODate(addDays(parseISODate(date), -1));
      if (prevEnd < s.rangeStart) return list.filter((x) => x.id !== seriesId);
      const kept = {};
      Object.keys(s.exceptions || {}).forEach((k) => { if (k < date) kept[k] = s.exceptions[k]; });
      return list.map((x) => (x.id === seriesId ? { ...x, rangeEnd: prevEnd, exceptions: kept, updatedAt: Date.now() } : x));
    });
    pushToast({ kind: 'success', title: 'Đã xóa' });
  };

  const requestDeleteFromModal = (mode) => {
    const s = dataRef.current.events.find((x) => x.id === mode.seriesId);
    if (!s) return;
    setModal(null);
    let message = `Sự kiện "${s.title}" sẽ bị xóa.`;
    if (s.kind === 'weekly') {
      if (mode.scope === 'this') message = `Chỉ xóa buổi "${s.title}" ngày ${fmtDMY(mode.occDate)}.`;
      else if (mode.scope === 'future') message = `Xóa buổi "${s.title}" ngày ${fmtDMY(mode.occDate)} và tất cả các buổi sau đó.`;
      else message = `Xóa toàn bộ chuỗi "${s.title}" (${fmtDMY(s.rangeStart)} → ${fmtDMY(s.rangeEnd)}).`;
    }
    setConfirm({ title: 'Xóa sự kiện?', message, confirmLabel: 'Xóa', danger: true, onConfirm: () => deleteOcc(mode.seriesId, mode.occDate, mode.scope) });
  };
  const requestDeleteSeries = (id) => {
    const s = dataRef.current.events.find((x) => x.id === id);
    if (!s) return;
    const message = s.kind === 'weekly'
      ? `Xóa toàn bộ chuỗi "${s.title}" (${describeSeries(s)}).`
      : `Sự kiện "${s.title}" ngày ${fmtDMY(s.date)} sẽ bị xóa.`;
    setConfirm({ title: 'Xóa sự kiện?', message, confirmLabel: 'Xóa', danger: true, onConfirm: () => deleteOcc(id, null, 'all') });
  };

  /* ----- Sao lưu / khôi phục ----- */
  const exportData = () => {
    const d = dataRef.current;
    const payload = {
      app: 'timetable-planner', version: 1, exportedAt: new Date().toISOString(),
      settings: { hours: d.settings.hours, theme: d.settings.theme, soundOn: d.settings.soundOn, volume: d.settings.volume },
      events: d.events,
    };
    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `thoi-gian-bieu-${toISODate(new Date())}.json`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
    pushToast({ kind: 'success', title: 'Đã xuất file sao lưu', message: `${d.events.length} sự kiện.` });
  };

  const importFile = async (file) => {
    let parsed;
    try { parsed = JSON.parse(await file.text()); } catch (e) {
      pushToast({ kind: 'error', title: 'File không hợp lệ', message: 'Không đọc được nội dung JSON. File có thể bị hỏng.' });
      return;
    }
    if (!parsed || typeof parsed !== 'object' || !Array.isArray(parsed.events)) {
      pushToast({ kind: 'error', title: 'Sai định dạng', message: 'File không phải bản sao lưu của ứng dụng này (thiếu danh sách "events").' });
      return;
    }
    const valid = [];
    const bad = [];
    parsed.events.forEach((raw, i) => {
      const r = sanitizeEvent(raw);
      if (r.event) valid.push(r.event); else bad.push(`#${i + 1}: ${r.error}`);
    });
    if (!valid.length) {
      pushToast({ kind: 'error', title: 'Không có sự kiện hợp lệ', message: bad.slice(0, 3).join('; ') || 'File trống.' });
      return;
    }
    setImportAsk({ fileName: file.name, events: valid, bad, settings: parsed.settings && typeof parsed.settings === 'object' ? parsed.settings : null });
  };

  const applyImport = (how) => {
    const imp = importAsk;
    if (!imp) return;
    mutateEvents((list) => {
      const stamp = Date.now();
      if (how === 'replace') return imp.events.map((s) => ({ ...s, updatedAt: stamp }));
      const map = new Map(list.map((s) => [s.id, s]));
      imp.events.forEach((s) => {
        const cur = map.get(s.id);
        if (!cur || s.updatedAt >= cur.updatedAt) map.set(s.id, { ...s, updatedAt: stamp });
      });
      return [...map.values()];
    });
    if (how === 'replace' && imp.settings) {
      const m = migrateData({ events: [], settings: { ...dataRef.current.settings, ...imp.settings, syncUrl: dataRef.current.settings.syncUrl, syncToken: dataRef.current.settings.syncToken, syncEnabled: dataRef.current.settings.syncEnabled } });
      updateSettings({ hours: m.settings.hours, theme: m.settings.theme, soundOn: m.settings.soundOn, volume: m.settings.volume });
    }
    setImportAsk(null);
    pushToast({ kind: 'success', title: how === 'replace' ? 'Đã ghi đè dữ liệu' : 'Đã gộp dữ liệu', message: `${imp.events.length} sự kiện từ ${imp.fileName}.` });
  };

  /* ----- Việc cần làm ----- */
  const taskDefaults = () => {
    const m = now.getHours() * 60 + now.getMinutes();
    return { date: toISODate(now), startTime: minToTime(Math.min(Math.ceil((m + 1) / 5) * 5, 1435)) };
  };
  const openNewTask = () => { setTaskModal({ mode: { type: 'new' } }); setSidebarOpen(false); };
  const saveTask = (f, mode) => {
    const ts = Date.now();
    mutateEvents((list) => {
      const old = mode.type === 'edit' ? list.find((x) => x.id === mode.seriesId) : null;
      if (mode.type === 'edit' && (!old || taskDone(old))) return list; // việc đã xong thì khóa
      let t = {
        id: old ? old.id : uid(), title: f.title.trim(), category: 'other', startTime: f.startTime, endTime: taskEnd(f.startTime),
        remindMin: 0, kind: 'once', date: f.date, task: true, repeatMode: f.repeat === 'eod' ? 'eod' : 'times',
        repeatN: f.repeat === '3' ? 3 : 2, exceptions: {}, done: old ? { ...old.done } : {}, notes: old ? { ...old.notes } : {}, updatedAt: ts,
      };
      if (old && old.date !== f.date && t.notes[old.date]) { t.notes[f.date] = t.notes[old.date]; delete t.notes[old.date]; }
      t = withNote(t, f.date, f.note, ts);
      return old ? list.map((x) => (x.id === old.id ? t : x)) : [...list, t];
    });
    setTaskModal(null);
    pushToast({ kind: 'success', title: mode.type === 'new' ? 'Đã thêm việc cần làm' : 'Đã lưu thay đổi' });
  };
  const requestDeleteTask = (id) => {
    const t = dataRef.current.events.find((x) => x.id === id);
    if (!t) return;
    setTaskModal(null);
    setConfirm({ title: 'Xóa việc?', message: `Việc "${t.title}" sẽ bị xóa.`, confirmLabel: 'Xóa', danger: true, onConfirm: () => deleteOcc(id, null, 'all') });
  };
  // Bấm tick: chỉ được từ giờ bắt đầu, rồi hỏi xác nhận 2 bước
  const askDoneTask = (id) => {
    const t = dataRef.current.events.find((x) => x.id === id);
    if (!t || taskDone(t)) return;
    if (dateTimeMs(t.date, t.startTime) > Date.now()) {
      pushToast({ kind: 'info', title: 'Chưa đến giờ', message: 'Chỉ tích "đã xong" được từ giờ bắt đầu.' });
      return;
    }
    setDoneAsk(t);
  };
  const completeTask = (id) => {
    const ts = Date.now();
    mutateEvents((list) => list.map((x) => {
      if (x.id !== id || !isTask(x) || taskDone(x)) return x; // chỉ tick một chiều, không bỏ tick
      return { ...x, done: { ...(x.done || {}), [x.date]: { v: true, t: ts } }, updatedAt: ts };
    }));
    pushToast({ kind: 'success', title: 'Đã ghi nhận hoàn thành', message: 'Ngừng nhắc việc này.' });
  };
  const testPhrase = () => {
    const st = dataRef.current.settings;
    AudioEngine.chime(st.volume);
    const text = fillPhrase(st.taskPhrase, { title: 'nấu cơm', date: '', notes: {} });
    pushToast({ kind: 'reminder', title: `⏰ ${text}`, message: 'Câu nhắc thử' });
    setTimeout(() => speakText(text, st.volume), 1300);
  };
  const dueCount = useMemo(() => taskList.filter((x) => !taskDone(x) && dateTimeMs(x.date, x.startTime) <= now.getTime()).length, [taskList, now]);

  /* ----- Điều hướng tuần ----- */
  // Đánh dấu "đã làm" cho một buổi (bấm lần nữa để bỏ)
  const toggleDone = (seriesId, date) => {
    const s0 = dataRef.current.events.find((x) => x.id === seriesId);
    if (!s0) return;
    const occ = occurrencesInRange(s0, parseISODate(date), parseISODate(date))[0];
    const wasDone = !!(s0.done && s0.done[date] && s0.done[date].v);
    if (occ && !wasDone && dateTimeMs(date, occ.startTime) > Date.now()) {
      pushToast({ kind: 'info', title: 'Buổi này chưa bắt đầu', message: 'Chỉ tích "đã làm" được từ khi buổi bắt đầu.' });
      return;
    }
    mutateEvents((list) => list.map((s) => {
      if (s.id !== seriesId) return s;
      const cur = !!(s.done && s.done[date] && s.done[date].v);
      const t = Date.now();
      return { ...s, done: { ...(s.done || {}), [date]: { v: !cur, t } }, updatedAt: t };
    }));
  };
  // Kéo thả / đổi kích thước một buổi: luôn chỉ áp dụng cho buổi này
  const moveOccurrence = (seriesId, fromDate, t) => {
    const s0 = dataRef.current.events.find((x) => x.id === seriesId);
    if (!s0) return;
    const occ = occurrencesInRange(s0, parseISODate(fromDate), parseISODate(fromDate))[0];
    if (!occ) return;
    const ts = Date.now();
    mutateEvents((list) => list.flatMap((s) => {
      if (s.id !== seriesId) return [s];
      if (s.kind === 'once') {
        // Sự kiện một lần: đổi thẳng ngày/giờ, dấu tích và ghi chú đi theo ngày mới
        const moveKey = (m) => {
          const out = { ...(m || {}) };
          if (t.date !== fromDate && out[fromDate]) { out[t.date] = out[fromDate]; delete out[fromDate]; }
          return out;
        };
        return [{ ...s, date: t.date, startTime: t.startTime, endTime: t.endTime, done: moveKey(s.done), notes: moveKey(s.notes), updatedAt: ts }];
      }
      if (t.date === fromDate) {
        // Lịch lặp, chỉ đổi giờ: ghi đè riêng buổi này
        return [{ ...s, updatedAt: ts, exceptions: { ...s.exceptions, [fromDate]: {
          title: occ.title, category: occ.category, startTime: t.startTime, endTime: t.endTime, remindMin: occ.remindMin } } }];
      }
      // Lịch lặp, sang ngày khác: bỏ buổi gốc và tạo sự kiện "một lần" ở ngày mới (mang theo dấu tích và ghi chú)
      const carry = (m) => (m && m[fromDate] ? { [t.date]: { ...m[fromDate], t: ts } } : {});
      const moved = {
        id: uid(), title: occ.title, category: occ.category, startTime: t.startTime, endTime: t.endTime,
        remindMin: occ.remindMin, kind: 'once', date: t.date, exceptions: {}, done: carry(s.done), notes: carry(s.notes), updatedAt: ts,
      };
      return [{ ...s, updatedAt: ts, exceptions: { ...s.exceptions, [fromDate]: 'deleted' } }, moved];
    }));
    pushToast({ kind: 'success', title: 'Đã cập nhật buổi này',
      message: `${occ.title} · ${t.startTime}–${t.endTime}${t.date !== fromDate ? ` · ${fmtDMY(t.date)}` : ''}` });
  };
  // Đổi tuần kèm hướng trượt: tuần sau trượt từ phải, tuần trước trượt từ trái
  const goTo = (next, dir) => { setSlideDir(dir); setCursor(startOfDay(next)); };
  // Lùi/tiến một ngày, một tuần hoặc một tháng tùy chế độ đang xem
  const shiftView = (n) => {
    if (mode === 'day') goTo(addDays(cursor, n), n > 0 ? 'next' : 'prev');
    else if (mode === 'week') goTo(addDays(cursor, 7 * n), n > 0 ? 'next' : 'prev');
    else goTo(addMonths(new Date(cursor.getFullYear(), cursor.getMonth(), 1), n), n > 0 ? 'next' : 'prev');
  };
  const goToday = () => { const t = new Date(); goTo(t, t >= cursor ? 'next' : 'prev'); setScrollSignal((n) => n + 1); };
  // Bấm một ngày trong lịch tháng nhỏ: nhảy tới ngày đó (điện thoại thì đóng ngăn kéo)
  const pickDate = (d) => { goTo(d, d >= cursor ? 'next' : 'prev'); setPage('calendar'); if (isMobileView()) setSidebarOpen(false); };
  const changeMode = (m) => {
    setMode(m);
    setSlideDir('next');
    try { localStorage.setItem('tp_cal_mode', m); } catch (e) { /* bỏ qua */ }
  };
  const goPage = (p) => { setPage(p); if (isMobileView()) setSidebarOpen(false); };
  const unitName = mode === 'day' ? 'Ngày' : mode === 'week' ? 'Tuần' : 'Tháng';
  const weekLabel = mode === 'day'
    ? `${WEEKDAYS_LONG[wdIndex(cursor)]}, ${fmtDMY(toISODate(cursor))}`
    : mode === 'month'
      ? `Tháng ${cursor.getMonth() + 1}/${cursor.getFullYear()}`
      : `${fmtDM(toISODate(weekStart))} – ${fmtDMY(toISODate(addDays(weekStart, 6)))}`;
  const span = mode === 'day' ? { ws: cursor, n: 1 }
    : mode === 'month' ? { ws: new Date(cursor.getFullYear(), cursor.getMonth(), 1), n: 0 }
      : { ws: weekStart, n: 7 };
  const PAGE_TITLES = { calendar: 'Lịch', tasks: 'Việc cần làm', list: 'Lịch trình', settings: 'Cài đặt' };
  keyActions.current = {
    prev: () => { if (page === 'calendar') shiftView(-1); },
    next: () => { if (page === 'calendar') shiftView(1); },
    today: goToday,
    add: () => (page === 'tasks' ? openNewTask() : openNew()),
    mode: (m) => { if (page === 'calendar') changeMode(m); },
    help: () => setShortcutsOpen(true),
  };

  // Phím tắt toàn trang (không hoạt động khi đang gõ hoặc khi có hộp thoại mở)
  useEffect(() => {
    const onKey = (e) => {
      if (e.defaultPrevented || e.ctrlKey || e.metaKey || e.altKey || e.repeat) return;
      const t = e.target;
      const tag = t && t.tagName;
      if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT' || (t && t.isContentEditable)) return;
      if (document.querySelector('[role="dialog"]')) return;
      const k = e.key;
      const a = keyActions.current;
      if (k === 'ArrowLeft') { e.preventDefault(); a.prev(); }
      else if (k === 'ArrowRight') { e.preventDefault(); a.next(); }
      else if (k === 't' || k === 'T') { e.preventDefault(); a.today(); }
      else if (k === 'n' || k === 'N') { e.preventDefault(); a.add(); }
      else if (k === 'd' || k === 'D') { e.preventDefault(); a.mode('day'); }
      else if (k === 'w' || k === 'W') { e.preventDefault(); a.mode('week'); }
      else if (k === 'm' || k === 'M') { e.preventDefault(); a.mode('month'); }
      else if (k === '?') { e.preventDefault(); a.help(); }
    };
    document.addEventListener('keydown', onKey);
    return () => document.removeEventListener('keydown', onKey);
  }, []);

  const modalSeries = modal && modal.mode.type === 'edit' ? data.events.find((s) => s.id === modal.mode.seriesId) : null;

  return (
    <div className={`app${sideCollapsed ? ' side-collapsed' : ''}`}>
      <NavRail page={page} onPage={goPage} dueCount={dueCount} />
      <div className="main">
        <header className="toolbar">
          <div className="toolbar-left">
            <span className="brand-m" aria-hidden="true"><Logo size={30} /></span>
            <h1 className="app-title">{PAGE_TITLES[page]}</h1>
          </div>
          {page === 'calendar' && (
            <div className="toolbar-nav">
              <button type="button" className="icon-btn bordered" aria-label={`${unitName} trước`} onClick={() => shiftView(-1)}><Icon name="ChevronLeft" /></button>
              <button type="button" className="btn" onClick={goToday}>Hôm nay</button>
              <button type="button" className="icon-btn bordered" aria-label={`${unitName} sau`} onClick={() => shiftView(1)}><Icon name="ChevronRight" /></button>
              <span className="week-label" aria-live="polite">{weekLabel}</span>
            </div>
          )}
          <div className="toolbar-right">
            {page === 'calendar' && (
              <div className="segmented mode-tabs" role="group" aria-label="Chế độ xem">
                {[['day', 'Ngày'], ['week', 'Tuần'], ['month', 'Tháng']].map(([m, l]) => (
                  <button key={m} type="button" aria-pressed={mode === m} onClick={() => changeMode(m)}>{l}</button>
                ))}
              </div>
            )}
            {page === 'calendar' && mode !== 'month' && (
              <select aria-label="Khung giờ hiển thị" value={settings.hours} onChange={(e) => updateSettings({ hours: e.target.value })}>
                {Object.keys(HOUR_OPTIONS).map((k) => <option key={k} value={k}>{HOUR_OPTIONS[k].label}</option>)}
              </select>
            )}
            <button type="button" className="icon-btn bordered kb-btn" aria-label="Phím tắt (?)" title="Phím tắt (?)" onClick={() => setShortcutsOpen(true)}><Icon name="Keyboard" /></button>
            <button type="button" className="icon-btn bordered" aria-label={resolvedTheme === 'dark' ? 'Chuyển sang giao diện Sáng' : 'Chuyển sang giao diện Tối'}
              onClick={() => updateSettings({ theme: resolvedTheme === 'dark' ? 'light' : 'dark' })}>
              <Icon name={resolvedTheme === 'dark' ? 'Sun' : 'Moon'} />
            </button>
            {page !== 'settings' && (
              <button type="button" className="btn btn-primary" onClick={() => (page === 'tasks' ? openNewTask() : openNew())}>
                <Icon name="Plus" size={16} /> <span className="label">{page === 'tasks' ? 'Thêm việc' : 'Thêm sự kiện'}</span>
              </button>
            )}
            <button type="button" className="icon-btn bordered" aria-label="Mở hoặc ẩn lịch tháng" title="Lịch tháng và hôm nay" onClick={togglePanel}><Icon name="CalendarDays" /></button>
          </div>
        </header>
        {page === 'tasks' && (
          <TasksView tasks={taskList} now={now} onAdd={openNewTask} onEdit={(id) => setTaskModal({ mode: { type: 'edit', seriesId: id } })}
            onDelete={requestDeleteTask} onDone={askDoneTask} />
        )}
        {page === 'list' && (
          <SchedulePage events={calEvents} onEditSeries={editSeries} onDeleteSeries={requestDeleteSeries} onAdd={() => openNew()} />
        )}
        {page === 'settings' && (
          <SettingsPage data={data} perm={perm} onToggleNotify={toggleNotify} onTestChime={() => AudioEngine.chime(settings.volume)}
            onUpdateSettings={updateSettings} onExport={exportData} onImportFile={importFile}
            syncStatus={syncStatus} onSaveSync={saveSyncSettings} onToggleSync={toggleSync}
            onTestEmail={testEmail} onSyncNow={() => doSync()} onCopyLink={copyConfigLink} onTestPhrase={testPhrase}
            onOpenShortcuts={() => setShortcutsOpen(true)} />
        )}
        {page === 'calendar' && mode === 'month' && (
          <div className="grid-wrap">
            <MonthGrid cursor={cursor} events={calEvents} now={now} slideDir={slideDir}
              onOpenDay={(d) => { setSlideDir('next'); setCursor(startOfDay(d)); changeMode('day'); }}
              onAddDay={(iso) => { const ds = defaultSlot(); openNew({ date: iso, startTime: ds.startTime, endTime: ds.endTime }); }}
              onCardClick={openOccurrence} />
          </div>
        )}
        {page === 'calendar' && mode !== 'month' && (
          <div className="grid-wrap">
            <WeekGrid weekStart={mode === 'day' ? cursor : weekStart} dayCount={mode === 'day' ? 1 : 7} events={calEvents} hoursKey={settings.hours}
              now={now} scrollSignal={scrollSignal} slideDir={slideDir}
              onSlotClick={(date, startTime, endTime) => openNew({ date, startTime, endTime })}
              onCardClick={openOccurrence} onToggleDone={toggleDone} onMoveOccurrence={moveOccurrence} onShow24h={() => updateSettings({ hours: '0-23' })} />
          </div>
        )}
      </div>

      <div className={`sidebar-backdrop${sidebarOpen ? ' open' : ''}`} onClick={() => setSidebarOpen(false)} />
      <Sidebar open={sidebarOpen} onClose={() => setPanel(false)} events={calEvents} now={now} weekStart={span.ws} spanDays={span.n}
        onPickDate={pickDate}
        onOpenOccurrence={(id, date) => { openOccurrence(id, date); if (isMobileView()) setSidebarOpen(false); }} />

      {taskModal && (taskModal.mode.type === 'new' || data.events.find((x) => x.id === taskModal.mode.seriesId)) && (
        <TaskModal mode={taskModal.mode} series={taskModal.mode.type === 'edit' ? data.events.find((x) => x.id === taskModal.mode.seriesId) : null}
          defaults={taskDefaults()} onSave={saveTask} onDelete={requestDeleteTask} onClose={() => setTaskModal(null)} />
      )}
      {doneAsk && <TaskDoneDialog task={doneAsk} onConfirm={completeTask} onClose={() => setDoneAsk(null)} />}

      {modal && (modal.mode.type === 'new' || modalSeries) && (
        <EventModal mode={modal.mode} series={modalSeries} onSave={saveForm}
          onDelete={requestDeleteFromModal} onClose={() => setModal(null)} />
      )}
      {scopeAsk && (
        <ScopeDialog date={scopeAsk.date} onClose={() => setScopeAsk(null)}
          onPick={(scope) => { setModal({ mode: { type: 'edit', seriesId: scopeAsk.seriesId, occDate: scopeAsk.date, scope } }); setScopeAsk(null); }} />
      )}
      {confirm && <ConfirmDialog {...confirm} onClose={() => setConfirm(null)} />}
      {shortcutsOpen && (
        <Dialog title="Phím tắt và thao tác nhanh" onClose={() => setShortcutsOpen(false)}>
          <table className="kbd-table">
            <tbody>
              {SHORTCUTS.map(([keys, desc]) => (
                <tr key={desc}><td>{keys.map((k) => <kbd key={k}>{k}</kbd>)}</td><td>{desc}</td></tr>
              ))}
            </tbody>
          </table>
          <p className="hint" style={{ marginTop: 12 }}>
            Bằng chuột: kéo một thẻ để đổi ngày hoặc giờ (bước 30 phút), kéo mép dưới thẻ để đổi giờ kết thúc. Với lịch lặp, thao tác chỉ áp dụng cho buổi đó.
            Phím tắt không hoạt động khi bạn đang gõ trong ô nhập hoặc khi có hộp thoại mở.
          </p>
          <div className="dialog-foot" style={{ marginTop: 14 }}>
            <button type="button" className="btn btn-primary" data-autofocus onClick={() => setShortcutsOpen(false)}>Đã hiểu</button>
          </div>
        </Dialog>
      )}
      {importAsk && (
        <Dialog title="Nhập dữ liệu" onClose={() => setImportAsk(null)}>
          <p>File <strong>{importAsk.fileName}</strong> có <strong>{importAsk.events.length}</strong> sự kiện hợp lệ.</p>
          {importAsk.bad.length > 0 && (
            <p className="field-error" style={{ marginTop: 8 }}>Bỏ qua {importAsk.bad.length} sự kiện lỗi ({importAsk.bad.slice(0, 3).join('; ')}{importAsk.bad.length > 3 ? '…' : ''}).</p>
          )}
          <p className="muted" style={{ marginTop: 8 }}>Gộp: giữ dữ liệu hiện tại và thêm hoặc cập nhật theo bản mới hơn. Ghi đè: thay toàn bộ lịch hiện tại.</p>
          <div className="dialog-foot" style={{ marginTop: 16 }}>
            <button type="button" className="btn" onClick={() => setImportAsk(null)}>Hủy</button>
            <button type="button" className="btn btn-danger" onClick={() => applyImport('replace')}>Ghi đè</button>
            <button type="button" className="btn btn-primary" data-autofocus onClick={() => applyImport('merge')}>Gộp</button>
          </div>
        </Dialog>
      )}
      <ToastHost toasts={toasts} onDismiss={dismissToast} />
    </div>
  );
}

ReactDOM.createRoot(document.getElementById('root')).render(<App />);

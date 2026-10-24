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
  if (!RE_TIME.test(raw.startTime) || !RE_TIME.test(raw.endTime)) return { error: 'giờ không hợp lệ' };
  if (timeToMin(raw.endTime) <= timeToMin(raw.startTime)) return { error: 'giờ kết thúc phải sau giờ bắt đầu' };
  const ev = {
    id: typeof raw.id === 'string' && raw.id ? raw.id.slice(0, 64) : uid(),
    title,
    category: CAT_IDS.includes(raw.category) ? raw.category : 'other',
    startTime: raw.startTime,
    endTime: raw.endTime,
    remindMin: Number.isFinite(raw.remindMin) && raw.remindMin >= 0 && raw.remindMin <= 10080 ? Math.round(raw.remindMin) : 0,
    kind: raw.kind,
    exceptions: {},
    updatedAt: Number.isFinite(raw.updatedAt) ? raw.updatedAt : Date.now(),
  };
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
  return { version: 1, updatedAt: Number(p && p.updatedAt) || 0, events, settings: st };
}

function loadData() {
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (raw) return migrateData(JSON.parse(raw));
  } catch (e) { console.warn('Không đọc được dữ liệu đã lưu', e); }
  return { version: 1, updatedAt: 0, events: [], settings: { ...DEFAULT_SETTINGS } };
}

function loadNotified() {
  try { return JSON.parse(localStorage.getItem(NOTIFIED_KEY) || '{}') || {}; } catch (e) { return {}; }
}
function saveNotified(map) {
  const cutoff = Date.now() - NOTIFIED_TTL_MS;
  Object.keys(map).forEach((k) => { if (map[k] < cutoff) delete map[k]; });
  try { localStorage.setItem(NOTIFIED_KEY, JSON.stringify(map)); } catch (e) { /* bỏ qua */ }
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

/* ---------- Dữ liệu nhắc gửi lên Apps Script ---------- */
function buildReminderPayload(events) {
  const from = startOfDay(new Date());
  const to = addDays(from, SYNC_HORIZON_DAYS);
  const tz = tzOffsetStr();
  const out = [];
  events.forEach((s) => {
    occurrencesInRange(s, from, to).forEach((o) => {
      if (o.remindMin > 0) {
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
      startTime: mode.prefill.startTime, endTime: mode.prefill.endTime, remindMin: 15,
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
    kind: f.kind, exceptions: {}, updatedAt: Date.now(),
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
  return s;
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
function WeekGrid({ weekStart, events, hoursKey, now, scrollSignal, onSlotClick, onCardClick, onShow24h }) {
  const cfg = HOUR_OPTIONS[hoursKey] || HOUR_OPTIONS['6-23'];
  const gridStart = cfg.start * 60;
  const gridEnd = cfg.end * 60;
  const scrollRef = useRef(null);
  const days = useMemo(() => Array.from({ length: 7 }, (_, i) => addDays(weekStart, i)), [weekStart]);
  const hours = useMemo(() => Array.from({ length: cfg.end - cfg.start }, (_, i) => cfg.start + i), [cfg]);

  const model = useMemo(() => {
    const all = [];
    events.forEach((s) => all.push(...occurrencesInRange(s, days[0], days[6])));
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

  // Cuộn tới vị trí giờ hiện tại khi mở app, bấm "Hôm nay" hoặc đổi khung giờ
  useEffect(() => {
    const el = scrollRef.current;
    if (!el) return;
    const top = nowVisible ? ((nowMin - gridStart) / 60) * HOUR_H - 140 : 0;
    el.scrollTo({ top: Math.max(0, top), behavior: scrollSignal === 0 ? 'auto' : 'smooth' });
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [scrollSignal, hoursKey]);

  const handleColClick = (e, iso) => {
    const rect = e.currentTarget.getBoundingClientRect();
    const y = e.clientY - rect.top;
    let mins = gridStart + Math.floor((y / HOUR_H) * 2) * 30; // làm tròn xuống 30 phút
    mins = Math.max(gridStart, Math.min(mins, 23 * 60 + 30));
    onSlotClick(iso, minToTime(mins), minToTime(Math.min(mins + 60, 23 * 60 + 59)));
  };

  const bodyHeight = hours.length * HOUR_H;

  return (
    <div className="grid-card">
      {(model.hidden > 0 || model.conflicts > 0) && (
        <div className="grid-notes">
          {model.conflicts > 0 && (
            <span className="note-chip"><Icon name="TriangleAlert" size={14} /> {model.conflicts} sự kiện trùng giờ trong tuần này</span>
          )}
          {model.hidden > 0 && (
            <span className="note-chip">
              <Icon name="Clock" size={14} /> {model.hidden} sự kiện nằm ngoài khung giờ đang chọn
              {hoursKey !== '0-23' && <button type="button" onClick={onShow24h}>Xem 24h</button>}
            </span>
          )}
        </div>
      )}
      <div className="grid-scroll" ref={scrollRef}>
        <div className="grid-inner" style={{ '--hour-h': `${HOUR_H}px` }}>
          <div className="grid-head">
            <div className="head-corner" />
            {days.map((d, i) => {
              const isToday = toISODate(d) === todayISO;
              return (
                <div key={i} className={`day-head${isToday ? ' today' : ''}`} aria-current={isToday ? 'date' : undefined}>
                  <div className="dow">{WEEKDAYS[i]}</div>
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
            {model.cols.map((col) => {
              const isToday = col.iso === todayISO;
              return (
                <div key={col.iso} className={`day-col${isToday ? ' today' : ''}`} onClick={(e) => handleColClick(e, col.iso)}>
                  {col.laid.map((it) => {
                    const top = ((it.s - gridStart) / 60) * HOUR_H;
                    const h = Math.max(((it.e - it.s) / 60) * HOUR_H - 2, 20);
                    const w = 100 / it.cols;
                    const compact = h < 38;
                    return (
                      <button key={it.key} type="button" className={`event${it.conflict ? ' conflict' : ''}${compact ? ' compact' : ''}`}
                        style={{
                          top, height: h, left: `calc(${it.col * w}% + 2px)`, width: `calc(${w}% - 4px)`,
                          '--ev-color': `var(--cat-${it.category})`, '--ev-bg': `var(--cat-${it.category}-bg)`,
                        }}
                        title={`${it.title}\n${it.startTime} – ${it.endTime} · ${catLabel(it.category)}${it.conflict ? '\n⚠ Trùng giờ' : ''}`}
                        aria-label={`${it.title}, ${fmtDMY(it.date)}, ${it.startTime} đến ${it.endTime}, ${catLabel(it.category)}${it.conflict ? ', trùng giờ' : ''}`}
                        onClick={(e) => { e.stopPropagation(); onCardClick(it.seriesId, it.date); }}>
                        <span className="ev-title">{it.title}</span>
                        <span className="ev-time">{it.startTime} – {it.endTime}</span>
                        {h >= 64 && (
                          <span className="ev-meta">
                            {it.kind === 'weekly' && <Icon name="Repeat" size={12} />}
                            {it.remindMin > 0 && <Icon name="Bell" size={12} />}
                            {it.conflict && <Icon name="TriangleAlert" size={12} />}
                            {catLabel(it.category)}
                          </span>
                        )}
                      </button>
                    );
                  })}
                  {isToday && nowVisible && (
                    <div className="now-line" style={{ top: ((nowMin - gridStart) / 60) * HOUR_H }}><span className="now-dot" /></div>
                  )}
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
   Component: EmailSyncPanel (nhắc qua email — Google Apps Script)
   ============================================================ */
function EmailSyncPanel({ settings, status, onSave, onToggle, onTest, onSyncNow, onForce }) {
  const [url, setUrl] = useState(settings.syncUrl);
  const [token, setToken] = useState(settings.syncToken);
  const [showToken, setShowToken] = useState(false);
  const urlId = React.useId();
  const tokenId = React.useId();
  const dirty = url.trim() !== settings.syncUrl || token.trim() !== settings.syncToken;
  const ready = !dirty && settings.syncUrl && settings.syncToken;

  return (
    <div className="sync-panel">
      <p className="hint">Khi tab đã đóng, email nhắc được gửi từ Google Apps Script của bạn. URL và token chỉ lưu trong trình duyệt này.</p>
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
        <span>Bật nhắc qua email</span>
      </label>
      <div className={`sync-status ${status.state}`} role="status">{status.message}</div>
      <div className="row">
        <button type="button" className="btn btn-sm" disabled={!ready} onClick={onTest}><Icon name="Send" size={15} /> Gửi thử email</button>
        <button type="button" className="btn btn-sm" disabled={!ready || !settings.syncEnabled} onClick={onSyncNow}><Icon name="RefreshCw" size={15} /> Đồng bộ ngay</button>
      </div>
      {status.canForce && (
        <button type="button" className="btn btn-danger btn-sm btn-block" style={{ marginTop: 8 }} onClick={onForce}>
          Ghi đè bản trên máy chủ bằng bản của máy này
        </button>
      )}
      {dirty && <p className="hint" style={{ marginTop: 6 }}>Hãy bấm "Lưu" trước khi gửi thử hoặc đồng bộ.</p>}
    </div>
  );
}

/* ============================================================
   Component: Sidebar
   ============================================================ */
function Sidebar(props) {
  const {
    open, onClose, data, perm, onToggleNotify, onTestChime, onUpdateSettings, onExport, onImportFile,
    onEditSeries, onDeleteSeries, syncStatus, onSaveSync, onToggleSync, onTestEmail, onSyncNow, onForceSync,
  } = props;
  const { settings, events } = data;
  const [query, setQuery] = useState('');
  const fileRef = useRef(null);

  const notifyActive = perm === 'granted' && settings.notifyOn;
  let notifyLabel = 'Bật thông báo';
  let notifyBadge = null;
  if (perm === 'unsupported') notifyLabel = 'Không hỗ trợ thông báo';
  else if (perm === 'denied') { notifyLabel = 'Thông báo bị chặn'; notifyBadge = <span className="status-badge bad">Đã chặn</span>; }
  else if (notifyActive) { notifyLabel = 'Thông báo đang bật'; notifyBadge = <span className="status-badge good">Bật</span>; }

  const groups = useMemo(() => {
    const q = fold(query.trim());
    const filtered = events.filter((s) => !q || fold(s.title).includes(q));
    const sorted = [...filtered].sort((a, b) => a.startTime.localeCompare(b.startTime) || a.title.localeCompare(b.title, 'vi'));
    return CATEGORIES.map((c) => ({ ...c, items: sorted.filter((s) => s.category === c.id) })).filter((g) => g.items.length);
  }, [events, query]);

  return (
    <aside className={`sidebar${open ? ' open' : ''}`} aria-label="Bảng điều khiển">
      <div className="sidebar-head">
        <div className="brand"><Icon name="CalendarDays" size={20} /> <span>Thời gian biểu</span></div>
        <button type="button" className="icon-btn only-mobile" aria-label="Đóng bảng điều khiển" onClick={onClose}><Icon name="X" /></button>
      </div>
      <div className="sidebar-scroll">
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
          <h3>Lịch trình ({events.length})</h3>
          <input type="search" placeholder="Tìm theo tiêu đề…" aria-label="Tìm sự kiện" value={query} onChange={(e) => setQuery(e.target.value)} />
          {events.length === 0 && <div className="empty-note" style={{ marginTop: 12 }}>Chưa có sự kiện nào. Bấm "Thêm sự kiện" hoặc bấm vào ô trống trên lưới.</div>}
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

        <details className="panel">
          <summary>Nhắc qua email (khi đóng tab)</summary>
          <EmailSyncPanel settings={settings} status={syncStatus} onSave={onSaveSync} onToggle={onToggleSync}
            onTest={onTestEmail} onSyncNow={onSyncNow} onForce={onForceSync} />
        </details>
      </div>
    </aside>
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
  const [weekStart, setWeekStart] = useState(() => startOfWeek(new Date()));
  const [now, setNow] = useState(() => new Date());
  const [scrollSignal, setScrollSignal] = useState(0);
  const [sidebarOpen, setSidebarOpen] = useState(false);
  const [modal, setModal] = useState(null);       // { mode }
  const [scopeAsk, setScopeAsk] = useState(null); // { seriesId, date }
  const [confirm, setConfirm] = useState(null);
  const [importAsk, setImportAsk] = useState(null);
  const [toasts, setToasts] = useState([]);
  const [perm, setPerm] = useState(getPerm);
  const systemDark = useSystemDark();
  const settings = data.settings;
  const resolvedTheme = settings.theme || (systemDark ? 'dark' : 'light');

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
    setData((d) => ({ ...d, events: fn(d.events), updatedAt: Date.now() }));
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
          if (o.remindMin <= 0) return;
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

  const doSync = useCallback(async (force) => {
    const d = dataRef.current;
    const s = d.settings;
    if (!(s.syncEnabled && s.syncUrl && s.syncToken)) return;
    if (!navigator.onLine) { setSyncStatus({ state: 'offline', message: 'Đang chờ có mạng để đồng bộ.' }); return; }
    if (syncRef.current.busy) { syncRef.current.again = true; return; }
    syncRef.current.busy = true;
    setSyncStatus({ state: 'syncing', message: 'Đang đồng bộ…' });
    try {
      const res = await postToScript(s.syncUrl, {
        action: 'sync', token: s.syncToken, updatedAt: d.updatedAt, force: !!force,
        events: buildReminderPayload(d.events),
      });
      if (res.ok) {
        if (dataRef.current.updatedAt === d.updatedAt) { try { localStorage.removeItem(DIRTY_KEY); } catch (e) { /* bỏ qua */ } }
        const at = Date.now();
        updateSettings({ lastSync: at });
        setSyncStatus({ state: 'ok', message: `Đã đồng bộ lúc ${fmtClock(at)} (${res.count != null ? res.count : 0} lượt nhắc)` });
      } else if (res.error === 'stale') {
        setSyncStatus({ state: 'error', canForce: true, message: 'Máy chủ đang có bản mới hơn bản trên máy này. Bấm nút bên dưới nếu muốn ghi đè.' });
      } else if (res.error === 'forbidden') {
        setSyncStatus({ state: 'error', message: 'Token không đúng. Kiểm tra lại token trong Script Properties.' });
      } else {
        setSyncStatus({ state: 'error', message: `Máy chủ báo lỗi: ${res.error || 'không rõ'}` });
      }
    } catch (e) {
      setSyncStatus({ state: 'error', message: e.message });
    } finally {
      syncRef.current.busy = false;
      if (syncRef.current.again) { syncRef.current.again = false; syncRef.current.timer = setTimeout(() => doSync(false), 1500); }
    }
  }, [updateSettings]);

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
    const days = Array.from({ length: 7 }, (_, i) => toISODate(addDays(weekStart, i)));
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
    mutateEvents((list) => {
      if (mode.type === 'new') return [...list, formToSeries(form, null)];
      const idx = list.findIndex((s) => s.id === mode.seriesId);
      if (idx < 0) return list;
      const s = list[idx];
      const next = [...list];
      if (mode.scope === 'all') {
        next[idx] = formToSeries(form, s);
      } else if (mode.scope === 'this') {
        next[idx] = {
          ...s, updatedAt: nowTs,
          exceptions: {
            ...s.exceptions,
            [mode.occDate]: {
              title: form.title.trim(), category: form.category, startTime: form.startTime,
              endTime: form.endTime, remindMin: Number(form.remindMin),
            },
          },
        };
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
        Object.keys(moved).forEach((k) => { if (k >= tail.rangeStart && k <= tail.rangeEnd) tail.exceptions[k] = 'deleted'; });
        if (prevEnd < s.rangeStart) next.splice(idx, 1, tail);
        else next.splice(idx, 1, { ...s, rangeEnd: prevEnd, exceptions: kept, updatedAt: nowTs }, tail);
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
      if (how === 'replace') return imp.events;
      const map = new Map(list.map((s) => [s.id, s]));
      imp.events.forEach((s) => {
        const cur = map.get(s.id);
        if (!cur || s.updatedAt >= cur.updatedAt) map.set(s.id, s);
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

  /* ----- Điều hướng tuần ----- */
  const shiftWeek = (n) => setWeekStart((w) => addDays(w, n * 7));
  const goToday = () => { setWeekStart(startOfWeek(new Date())); setScrollSignal((n) => n + 1); };
  const weekLabel = `${fmtDM(toISODate(weekStart))} – ${fmtDMY(toISODate(addDays(weekStart, 6)))}`;

  const modalSeries = modal && modal.mode.type === 'edit' ? data.events.find((s) => s.id === modal.mode.seriesId) : null;

  return (
    <div className="app">
      <div className="main">
        <header className="toolbar">
          <div className="toolbar-left">
            <button type="button" className="icon-btn only-mobile bordered" aria-label="Mở bảng điều khiển" onClick={() => setSidebarOpen(true)}><Icon name="Menu" /></button>
            <h1 className="app-title">Thời gian biểu</h1>
          </div>
          <div className="toolbar-nav">
            <button type="button" className="icon-btn bordered" aria-label="Tuần trước" onClick={() => shiftWeek(-1)}><Icon name="ChevronLeft" /></button>
            <button type="button" className="btn" onClick={goToday}>Hôm nay</button>
            <button type="button" className="icon-btn bordered" aria-label="Tuần sau" onClick={() => shiftWeek(1)}><Icon name="ChevronRight" /></button>
            <span className="week-label" aria-live="polite">{weekLabel}</span>
          </div>
          <div className="toolbar-right">
            <select aria-label="Khung giờ hiển thị" value={settings.hours} onChange={(e) => updateSettings({ hours: e.target.value })}>
              {Object.keys(HOUR_OPTIONS).map((k) => <option key={k} value={k}>{HOUR_OPTIONS[k].label}</option>)}
            </select>
            <button type="button" className="icon-btn bordered" aria-label={resolvedTheme === 'dark' ? 'Chuyển sang giao diện Sáng' : 'Chuyển sang giao diện Tối'}
              onClick={() => updateSettings({ theme: resolvedTheme === 'dark' ? 'light' : 'dark' })}>
              <Icon name={resolvedTheme === 'dark' ? 'Sun' : 'Moon'} />
            </button>
            <button type="button" className="btn btn-primary" onClick={() => openNew()}>
              <Icon name="Plus" size={16} /> <span className="label">Thêm sự kiện</span>
            </button>
          </div>
        </header>
        <div className="grid-wrap">
          <WeekGrid weekStart={weekStart} events={data.events} hoursKey={settings.hours} now={now} scrollSignal={scrollSignal}
            onSlotClick={(date, startTime, endTime) => openNew({ date, startTime, endTime })}
            onCardClick={openOccurrence} onShow24h={() => updateSettings({ hours: '0-23' })} />
        </div>
      </div>

      <div className={`sidebar-backdrop${sidebarOpen ? ' open' : ''}`} onClick={() => setSidebarOpen(false)} />
      <Sidebar open={sidebarOpen} onClose={() => setSidebarOpen(false)} data={data} perm={perm}
        onToggleNotify={toggleNotify} onTestChime={() => AudioEngine.chime(settings.volume)}
        onUpdateSettings={updateSettings} onExport={exportData} onImportFile={importFile}
        onEditSeries={editSeries} onDeleteSeries={requestDeleteSeries}
        syncStatus={syncStatus} onSaveSync={saveSyncSettings} onToggleSync={toggleSync}
        onTestEmail={testEmail} onSyncNow={() => doSync(false)} onForceSync={() => doSync(true)} />

      {modal && (modal.mode.type === 'new' || modalSeries) && (
        <EventModal mode={modal.mode} series={modalSeries} onSave={saveForm}
          onDelete={requestDeleteFromModal} onClose={() => setModal(null)} />
      )}
      {scopeAsk && (
        <ScopeDialog date={scopeAsk.date} onClose={() => setScopeAsk(null)}
          onPick={(scope) => { setModal({ mode: { type: 'edit', seriesId: scopeAsk.seriesId, occDate: scopeAsk.date, scope } }); setScopeAsk(null); }} />
      )}
      {confirm && <ConfirmDialog {...confirm} onClose={() => setConfirm(null)} />}
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

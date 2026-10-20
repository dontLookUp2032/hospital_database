// NUMA Performance Bottleneck Simulator - backend
// Run:  npm install && npm start   ->  http://localhost:3000
//
// Model (all times in virtual milliseconds):
//  - Two NUMA nodes, each with a small pool of worker threads and its own queue.
//  - Each department's data lives on one "home" node (ER, ICU -> 0 ; OPD, Pediatrics -> 1).
//  - A query touches N memory accesses. If the worker runs on the data's home node every
//    access costs localNs, otherwise remoteNs. Service time = N * cost.
//  - Latency = queue wait + service time. Slow (remote) service keeps workers busy longer,
//    so queues build up: that is how a small per-access penalty becomes a big triage delay.
//  - Broken mode: the dispatcher ignores data placement, so only ~40% of queries land on the
//    home node. Fixed mode: queries are routed to the owner node (small spill-over remains).

const express = require('express');
const path = require('path');

// ---------- helpers ----------
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function percentile(arr, p) {
  if (!arr.length) return 0;
  const s = Float64Array.from(arr).sort();
  return s[Math.min(s.length - 1, Math.floor((p / 100) * s.length))];
}

const mean = (a) => (a.length ? a.reduce((x, y) => x + y, 0) / a.length : 0);
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, Number(v)));

// ---------- configuration ----------
const DEPTS = {
  ER:  { home: 0, critical: true,  accesses: 8000,  weight: 30 },
  ICU: { home: 0, critical: true,  accesses: 12000, weight: 20 },
  OPD: { home: 1, critical: false, accesses: 10000, weight: 30 },
  PED: { home: 1, critical: false, accesses: 9000,  weight: 20 },
};
const DEPT_NAMES = Object.keys(DEPTS);
const TOTAL_WEIGHT = DEPT_NAMES.reduce((s, d) => s + DEPTS[d].weight, 0);

const DEFAULTS = {
  rate: 1200,            // queries per second (all departments)
  localNs: 100,          // cost of one local memory access
  remoteNs: 300,         // cost of one remote memory access
  workersPerNode: 2,
  brokenLocalProb: 0.4,  // chance a query lands on its data's node in Broken mode
  fixedLocalProb: 0.9,   // same, in Fixed mode
  priority: true,        // critical (ER/ICU) queries jump the queue
  maxQueue: 4000,        // per node; beyond this queries are dropped
};

const WINDOW_MS = 3000;  // sliding window for the "live" numbers

// ---------- stats ----------
const newStats = () => ({
  n: 0, sumLat: 0, crit: 0, sumCritWait: 0, sumCritLat: 0,
  localAcc: 0, totAcc: 0, samples: [], seen: 0, seconds: 0,
});

function addStat(s, r, rand) {
  s.n++; s.sumLat += r.latency;
  if (r.critical) { s.crit++; s.sumCritWait += r.wait; s.sumCritLat += r.latency; }
  s.totAcc += r.accesses; if (r.local) s.localAcc += r.accesses;
  s.seen++;
  if (s.samples.length < 20000) s.samples.push(r.latency);
  else { const j = Math.floor(rand() * s.seen); if (j < 20000) s.samples[j] = r.latency; }
}

function summarize(s) {
  return {
    count: s.n,
    avgLatencyMs: s.n ? s.sumLat / s.n : 0,
    p95Ms: percentile(s.samples, 95),
    localPct: s.totAcc ? (100 * s.localAcc) / s.totAcc : 0,
    throughput: s.seconds ? s.n / s.seconds : 0,
    triageDelayMs: s.crit ? s.sumCritWait / s.crit : 0,
    criticalLatencyMs: s.crit ? s.sumCritLat / s.crit : 0,
  };
}

function compareFigures(b, f) {
  if (!b.count || !f.count || !f.avgLatencyMs) return null;
  return {
    slowdownPct: ((b.avgLatencyMs - f.avgLatencyMs) / f.avgLatencyMs) * 100,
    improvementPct: ((b.avgLatencyMs - f.avgLatencyMs) / b.avgLatencyMs) * 100,
    triageImprovementPct: b.triageDelayMs
      ? ((b.triageDelayMs - f.triageDelayMs) / b.triageDelayMs) * 100 : 0,
  };
}

// ---------- simulation engine ----------
class Sim {
  constructor(seed = 42, cfg = {}, recordEvents = false) {
    this.cfg = { ...DEFAULTS, ...cfg };
    this.rand = mulberry32(seed);
    this.mode = 'broken';
    this.now = 0;
    this.nextArrival = null;
    this.nodes = [0, 1].map(() => ({
      queue: [],
      workers: Array(this.cfg.workersPerNode).fill(0), // time each worker becomes free
    }));
    this.done = [];          // recent completed queries (for the sliding window)
    this.stats = { broken: newStats(), fixed: newStats() };
    this.series = [];
    this.lastSec = 0;
    this.dropped = 0;
    this.recordEvents = recordEvents;
    this.events = [];
  }

  expo(ratePerMs) { return -Math.log(1 - this.rand()) / ratePerMs; }

  pickDept() {
    let x = this.rand() * TOTAL_WEIGHT;
    for (const d of DEPT_NAMES) { x -= DEPTS[d].weight; if (x < 0) return d; }
    return DEPT_NAMES[0];
  }

  // Generate a query and dispatch it to a worker node according to the active mode.
  arrive(at) {
    const dept = this.pickDept();
    const def = DEPTS[dept];
    const pLocal = this.mode === 'fixed' ? this.cfg.fixedLocalProb : this.cfg.brokenLocalProb;
    const worker = this.rand() < pLocal ? def.home : 1 - def.home;
    const node = this.nodes[worker];
    if (node.queue.length >= this.cfg.maxQueue) { this.dropped++; return; }
    node.queue.push({
      dept, home: def.home, worker, critical: def.critical, arrival: at, mode: this.mode,
      accesses: Math.round(def.accesses * (0.8 + 0.4 * this.rand())),
    });
  }

  // Let a node's workers start as many queued queries as fit before `end`.
  drain(node, end) {
    const w = node.workers, q = node.queue;
    while (q.length) {
      let wi = 0;
      for (let i = 1; i < w.length; i++) if (w[i] < w[wi]) wi = i;
      const startAt = Math.max(w[wi], q[0].arrival);
      if (startAt >= end) break;

      // Pick the next query: the oldest one, or the oldest critical one if priority is on.
      let idx = 0;
      if (this.cfg.priority) {
        for (let i = 0; i < q.length && q[i].arrival <= startAt; i++) {
          if (q[i].critical) { idx = i; break; }
        }
      }
      const job = q.splice(idx, 1)[0];

      const local = job.worker === job.home;
      const service = (job.accesses * (local ? this.cfg.localNs : this.cfg.remoteNs)) / 1e6; // ms
      const finish = startAt + service;
      w[wi] = finish;

      const rec = {
        finish, worker: job.worker, local, critical: job.critical, accesses: job.accesses,
        wait: startAt - job.arrival, service, latency: finish - job.arrival,
      };
      this.done.push(rec);
      addStat(this.stats[job.mode], rec, this.rand);

      if (this.recordEvents && Math.random() < 0.08) {
        this.events.push({ home: job.home, worker: job.worker, critical: job.critical });
        if (this.events.length > 80) this.events.shift();
      }
    }
  }

  step(dtMs) {
    const end = this.now + dtMs;
    const rate = this.cfg.rate / 1000;
    if (this.nextArrival === null) this.nextArrival = this.now + this.expo(rate);
    while (this.nextArrival <= end) {
      this.arrive(this.nextArrival);
      this.nextArrival += this.expo(rate);
    }
    this.nodes.forEach((n) => this.drain(n, end));
    this.now = end;
    this.stats[this.mode].seconds += dtMs / 1000;
    this.done = this.done.filter((r) => r.finish >= end - WINDOW_MS);
    const sec = Math.floor(end / 1000);
    if (sec > this.lastSec) { this.lastSec = sec; this.pushSeries(); }
  }

  // Live numbers over the last few seconds of virtual time.
  metrics() {
    const lo = this.now - WINDOW_MS;
    const rs = this.done.filter((r) => r.finish <= this.now && r.finish >= lo);
    const span = Math.max(0.5, Math.min(WINDOW_MS, this.now) / 1000);
    const lat = rs.map((r) => r.latency);
    const crit = rs.filter((r) => r.critical);
    const tot = rs.reduce((s, r) => s + r.accesses, 0);
    const loc = rs.reduce((s, r) => s + (r.local ? r.accesses : 0), 0);
    const localPct = tot ? (100 * loc) / tot : 0;
    const util = [0, 1].map((n) => {
      const busy = rs.filter((r) => r.worker === n).reduce((s, r) => s + r.service, 0);
      return Math.min(1, busy / (span * 1000 * this.cfg.workersPerNode));
    });
    return {
      avgLatencyMs: mean(lat),
      p95Ms: percentile(lat, 95),
      localPct,
      remotePct: tot ? 100 - localPct : 0,
      throughput: rs.length / span,
      triageDelayMs: mean(crit.map((r) => r.wait)),
      queueLen: this.nodes.map((n) => n.queue.length),
      util,
    };
  }

  pushSeries() {
    const m = this.metrics();
    this.series.push({
      t: Math.round(this.now / 1000), mode: this.mode,
      avg: m.avgLatencyMs, p95: m.p95Ms, triage: m.triageDelayMs, local: m.localPct,
    });
    if (this.series.length > 90) this.series.shift();
  }
}

// ---------- headless benchmark (same idea as the report's experiment procedure) ----------
function runBenchmark({ seconds, runs, cfg }) {
  const out = {};
  for (const mode of ['broken', 'fixed']) {
    const results = [];
    for (let r = 0; r < runs; r++) {
      const sim = new Sim(1000 + r, cfg);
      sim.mode = mode;
      for (let i = 0; i < seconds * 10; i++) sim.step(100);
      results.push(summarize(sim.stats[mode]));
    }
    const keys = Object.keys(results[0]);
    out[mode] = Object.fromEntries(keys.map((k) => [k, mean(results.map((r) => r[k]))]));
  }
  const L = cfg.localNs, R = cfg.remoteNs;
  const analytic = (p) => p * L + (1 - p) * R;   // average cost of one access, in ns
  out.analytic = {
    brokenNsPerAccess: analytic(cfg.brokenLocalProb),
    fixedNsPerAccess: analytic(cfg.fixedLocalProb),
  };
  out.comparison = compareFigures(out.broken, out.fixed);
  out.params = { seconds, runs, rate: cfg.rate };
  return out;
}

// ---------- live simulation + API ----------
let live = new Sim(Date.now() & 0xffff, {}, true);
let last = Date.now();
setInterval(() => {
  const t = Date.now();
  const dt = Math.min(t - last, 300);   // virtual time runs 1:1 with real time
  last = t;
  live.step(dt);
}, 100);

const app = express();

// Allow the GitHub Pages website to contact this backend
app.use((req, res, next) => {
  res.header(
    'Access-Control-Allow-Origin',
    'https://dontlookup2032.github.io'
  );
  res.header(
    'Access-Control-Allow-Methods',
    'GET, POST, OPTIONS'
  );
  res.header(
    'Access-Control-Allow-Headers',
    'Content-Type'
  );

  if (req.method === 'OPTIONS') {
    return res.sendStatus(204);
  }

  next();
});

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));
app.get('/api/metrics', (req, res) => {
  const events = live.events.splice(0).slice(-40);
  res.json({
    mode: live.mode,
    cfg: live.cfg,
    uptimeSec: live.now / 1000,
    dropped: live.dropped,
    live: live.metrics(),
    series: live.series,
    events,
  });
});

app.get('/api/compare', (req, res) => {
  const b = summarize(live.stats.broken), f = summarize(live.stats.fixed);
  res.json({ broken: b, fixed: f, comparison: compareFigures(b, f) });
});

app.post('/api/mode', (req, res) => {
  const mode = req.body && req.body.mode;
  if (mode !== 'broken' && mode !== 'fixed') return res.status(400).json({ error: 'mode must be "broken" or "fixed"' });
  live.mode = mode;
  res.json({ mode });
});

app.post('/api/config', (req, res) => {
  const b = req.body || {};
  const c = live.cfg;
  if (b.rate !== undefined) c.rate = clamp(b.rate, 100, 3000);
  if (b.remoteNs !== undefined) c.remoteNs = clamp(b.remoteNs, 100, 600);
  if (b.localNs !== undefined) c.localNs = clamp(b.localNs, 50, 300);
  if (b.priority !== undefined) c.priority = !!b.priority;
  res.json(c);
});

app.post('/api/reset', (req, res) => {
  live = new Sim(Date.now() & 0xffff, live.cfg, true);
  res.json({ ok: true });
});

app.get('/api/benchmark', (req, res) => {
  const seconds = clamp(req.query.seconds || 60, 10, 120);
  const runs = clamp(req.query.runs || 3, 1, 5);
  res.json(runBenchmark({ seconds, runs, cfg: { ...live.cfg } }));
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => console.log(`NUMA simulator running at http://localhost:${PORT}`));

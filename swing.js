/* Loop swing model — swing sessions, me-vs-me baselines, today vs normal (swing and shots), the evidence graph and pre-registered
   experiments. Mirrors pipeline/swing_model.py (tests_swing.py checks they agree).

   Sessions come from the swing harness (swing/swing_lab.py → schema loop.swing/1): per swing the events, the view, handedness and
   tiered measurements, each with its evidence kind (OBSERVED / ESTIMATED / UNKNOWN), a 1-σ measurement uncertainty and a confidence.
   Nothing here measures a body: it compares measurements that were made elsewhere, and it says when the numbers are too thin.

   Evidence words (the brief's hierarchy): OBSERVED — measured directly (a marked position, an event time); ESTIMATED — computed from a
   model (strokes from the curve, inches from a body scale); INFERRED — a conclusion from several observations (today's miss has moved);
   PREDICTED — a statistical prediction (the engine's best target given today's pattern); UNKNOWN — not enough evidence, said as such. */
(function () {
  const D = window.LOOP_DATA, E = window.LoopEngine, LG = window.LoopLedger;
  const SCHEMA = "loop.swing/1";
  // the measurements Loop shows, in the order it shows them; view = where they can be measured; tier from the harness
  const METRICS = {
    tempo_ratio: { label: "Tempo (backswing : downswing)", unit: ":1", tier: 1, view: "any", dp: 2 },
    backswing_s: { label: "Backswing time", unit: "s", tier: 1, view: "any", dp: 3 },
    downswing_s: { label: "Downswing time", unit: "s", tier: 1, view: "any", dp: 3 },
    pelvis_lead_s: { label: "Pelvis starts down before the hands reach the top", unit: "s", tier: 2, view: "face-on", dp: 3 },
    head_sway_impact_in: { label: "Head sway at impact (toward target +)", unit: "in", tier: 2, view: "face-on", dp: 1 },
    head_sway_top_in: { label: "Head sway at the top", unit: "in", tier: 2, view: "face-on", dp: 1 },
    pelvis_sway_top_in: { label: "Pelvis sway at the top", unit: "in", tier: 2, view: "face-on", dp: 1 },
    pelvis_sway_impact_in: { label: "Pelvis sway at impact", unit: "in", tier: 2, view: "face-on", dp: 1 },
    chest_sway_top_in: { label: "Chest sway at the top", unit: "in", tier: 2, view: "face-on", dp: 1 },
    head_lift_impact_in: { label: "Head rise at impact (up +)", unit: "in", tier: 2, view: "any", dp: 1 },
    side_bend_impact_deg: { label: "Side bend at impact", unit: "°", tier: 2, view: "face-on", dp: 1 },
    pelvis_thrust_impact_in: { label: "Pelvis toward the ball at impact (early extension +)", unit: "in", tier: 2, view: "down-the-line", dp: 1 },
    spine_angle_change_deg: { label: "Spine angle change, address → impact (standing up −)", unit: "°", tier: 2, view: "down-the-line", dp: 1 },
    head_thrust_impact_in: { label: "Head toward the ball at impact", unit: "in", tier: 2, view: "down-the-line", dp: 1 },
    shoulder_turn_proxy_top_deg: { label: "Shoulder turn proxy at the top", unit: "°", tier: 3, view: "face-on", dp: 0 },
    hip_turn_proxy_top_deg: { label: "Hip turn proxy at the top", unit: "°", tier: 3, view: "face-on", dp: 0 },
  };
  const NEVER = { club_path_deg: "club path", face_angle_deg: "face angle", attack_angle_deg: "attack angle", launch_angle_deg: "launch angle", club_speed_mph: "club speed", ball_speed_mph: "ball speed" };
  // Today mode's shrinkage is empirical Bayes (dayModel): τ0 is the prior day-to-day spread of your miss (share of carry) until 6 rounds
  // carry 4+ shots in a club group, σ0 the shot-to-shot spread before 10 deviations exist (the model's own, about 8% of carry).
  const RULES = { minTodaySwings: 3, minBaseSwings: 10, minBaseSessions: 2, zDifferent: 2.0, minTodayShots: 3, minShiftYd: 4,
    tau0: 0.02, sigma0: 0.08, tauMin: 0.005, tauMax: 0.06, minRoundsTau: 6, minRoundShots: 4 };

  // ---------- small statistics (the Python mirror implements the same) ----------
  const mean = a => a.length ? a.reduce((s, x) => s + x, 0) / a.length : null;
  const median = a => { if (!a.length) return null; const b = a.slice().sort((x, y) => x - y); const m = b.length >> 1; return b.length % 2 ? b[m] : (b[m - 1] + b[m]) / 2; };
  const sd = a => { if (a.length < 2) return null; const m = mean(a); return Math.sqrt(a.reduce((s, x) => s + (x - m) * (x - m), 0) / (a.length - 1)); };
  const mad = a => { const m = median(a); if (m == null || a.length < 2) return null; return 1.4826 * median(a.map(x => Math.abs(x - m))); };
  const r3 = x => x == null || !isFinite(x) ? null : Math.round(x * 1000) / 1000;
  function rng(seed) { let a = seed >>> 0 || 1; return () => { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }

  // ---------- sessions ----------
  function sessionId(s) { return "sw_" + ((s.source && s.source.sha1) || "") + "_" + ((s.source && s.source.created) || s.imported || ""); }
  function normalize(json) {
    if (!json || json.schema !== SCHEMA) throw new Error("not a Loop swing session (schema " + (json && json.schema) + ")");
    const s = JSON.parse(JSON.stringify(json));
    s.id = s.id || sessionId(s);
    s.date = s.date || (s.source && s.source.created ? String(s.source.created).slice(0, 10) : null);
    s.golfer = s.golfer || "unknown";
    s.swings = (s.swings || []).filter(w => w && w.metrics);
    return s;
  }
  // a swing's absolute time (ms): the video's creation time + the impact's time in the clip (null when the video carries no time)
  function swingTime(s, w) { const c = s.source && s.source.created; if (!c) return null; const t0 = Date.parse(c); return isNaN(t0) ? null : t0 + 1000 * (w.t_impact || 0); }
  // per-metric numbers of one session, by view: { view: { key: {n, mean, sd, sigma} } }
  function sessionStats(s, mine) {
    const out = {};
    for (const w of s.swings) {
      if (mine && w.excluded) continue;
      const v = w.view || "other";
      for (const k in w.metrics) {
        const m = w.metrics[k]; if (!m || !m.available || m.value == null) continue;
        const b = ((out[v] = out[v] || {})[k] = out[v][k] || { vals: [], sig: [] }); b.vals.push(m.value); if (m.sigma != null) b.sig.push(m.sigma);
      }
    }
    for (const v in out) for (const k in out[v]) { const b = out[v][k]; out[v][k] = { n: b.vals.length, mean: r3(mean(b.vals)), sd: r3(sd(b.vals)), sigma: r3(median(b.sig)), vals: b.vals }; }
    return out;
  }

  // ---------- me vs me: the baseline and today against it ----------
  // baseline over sessions (golfer "me" only): per view and metric — the centre (median of session means), the swing-to-swing spread
  // within a session (pooled SD), the day-to-day spread of session means (robust SD, needs 3 sessions) and the measurement σ.
  function baseline(sessions, opts) {
    const exclude = opts && opts.exclude; const per = {};
    for (const s of sessions) {
      if (s.golfer !== "me" || (exclude && s.id === exclude)) continue;
      const st = sessionStats(s, true);
      for (const v in st) for (const k in st[v]) { const b = ((per[v] = per[v] || {})[k] = per[v][k] || { means: [], vals: [], sig: [], within: [], sessions: [] }); const x = st[v][k];
        b.means.push(x.mean); b.vals.push(...x.vals); if (x.sigma != null) b.sig.push(x.sigma); if (x.n >= 2) b.within.push([x.sd, x.n]); b.sessions.push({ id: s.id, date: s.date, n: x.n, mean: x.mean }); }
    }
    const out = {};
    for (const v in per) for (const k in per[v]) {
      const b = per[v][k]; const dfw = b.within.reduce((s, [, n]) => s + n - 1, 0);
      const within = dfw > 0 ? Math.sqrt(b.within.reduce((s, [sdv, n]) => s + sdv * sdv * (n - 1), 0) / dfw) : sd(b.vals);
      (out[v] = out[v] || {})[k] = { nSessions: b.means.length, nSwings: b.vals.length, center: r3(median(b.means)), within: r3(within), between: b.means.length >= 3 ? r3(mad(b.means)) : null,
        sigma: r3(median(b.sig)), sessions: b.sessions };
    }
    return out;
  }
  // one metric of a session against the baseline. Different only when (a) there is enough of both, (b) the gap is beyond what the
  // swing-to-swing spread and the day-to-day spread explain (|z| ≥ 2), and (c) the gap is bigger than the measurement can resolve.
  function compareMetric(b, t) {
    if (!t || !t.n) return { verdict: "not measured", evidence: "UNKNOWN" };
    if (!b || b.nSwings < RULES.minBaseSwings || b.nSessions < RULES.minBaseSessions) return { verdict: "baseline forming", evidence: "UNKNOWN", today: t.mean, n: t.n, need: `your normal needs ${RULES.minBaseSwings} swings over ${RULES.minBaseSessions} sessions in this view (have ${b ? b.nSwings : 0} over ${b ? b.nSessions : 0})` };
    if (t.n < RULES.minTodaySwings) return { verdict: "too few swings today", evidence: "UNKNOWN", today: t.mean, normal: b.center, n: t.n, need: `${RULES.minTodaySwings} swings` };
    const w = b.within != null ? b.within : (t.sd || 0); const tau = b.between != null ? b.between : 0;
    const se = Math.sqrt(tau * tau + (w * w) / t.n + (w * w) / Math.max(1, b.nSwings));
    const delta = t.mean - b.center; const z = se > 0 ? delta / se : 0;
    const sig = b.sigma != null ? b.sigma : (t.sigma || 0); const mdc = 1.96 * Math.sqrt(2) * sig / Math.sqrt(t.n);
    const different = Math.abs(z) >= RULES.zDifferent && Math.abs(delta) > mdc;
    return { verdict: different ? (delta > 0 ? "higher than normal" : "lower than normal") : "within your normal", evidence: different ? "INFERRED" : "OBSERVED",
      today: r3(t.mean), normal: r3(b.center), delta: r3(delta), z: r3(z), mdc: r3(mdc), n: t.n, nBase: b.nSwings, nSessions: b.nSessions };
  }
  function todayVsNormal(sessions, today) {
    const base = baseline(sessions, { exclude: today.id }); const st = sessionStats(today, true); const out = {};
    for (const v in st) for (const k in st[v]) if (METRICS[k]) (out[v] = out[v] || {})[k] = compareMetric(base[v] && base[v][k], st[v][k]);
    return { base, out };
  }

  // ---------- swing ↔ shot: link swings to the shots they produced ----------
  // A swing filmed on the course is linked to the marked shot whose time is nearest within 3 minutes before the next mark (a mark is
  // made before the shot; the video of that shot follows it). A session with no shot within reach links to the rounds of its day.
  function linkShots(s, rounds) {
    const links = []; const dayRounds = rounds.filter(r => !r.sample && s.date && r.date === s.date).map(r => r.id);
    for (const w of s.swings) {
      const tw = swingTime(s, w); let best = null;
      if (tw != null) for (const r of rounds) { if (r.sample) continue; for (const hn in (r.holes || {})) { const shots = r.holes[hn].shots || [];
        shots.forEach((sh, i) => { if (!sh.t) return; const ts = Date.parse(sh.t); const next = shots[i + 1] && shots[i + 1].t ? Date.parse(shots[i + 1].t) : ts + 10 * 60000;
          const dt = (tw - ts) / 1000; if (dt >= -20 && dt <= 180 && tw <= next + 20000 && (!best || Math.abs(dt) < Math.abs(best.dt))) best = { swing: w.index, round: r.id, hole: +hn, shot: i, dt: Math.round(dt) }; }); } }
      links.push(best || { swing: w.index, round: null, day: dayRounds });
    }
    return links;
  }

  // ---------- what was observed together: the strike, the place, the shot ----------
  // Two clocks in the video itself say whether a ball was struck (the harness: clocks.ball = the ball leaving, clocks.sound = the strike
  // sound). A swing with neither is a practice swing. Neither is guessed: an unchecked swing stays "not checked".
  function strikeOf(w) {
    const c = (w && w.clocks) || {}; const b = (c.ball || {}).found, s = (c.sound || {}).strike;
    if (b === "yes" && s === "yes") return { verdict: "struck (ball left, strike heard)", kind: "OBSERVED", struck: true };
    if (b === "yes") return { verdict: "struck (ball left)", kind: "OBSERVED", struck: true };
    if (s === "yes") return { verdict: "struck (strike heard)", kind: "OBSERVED", struck: true };
    if (b === "none" && s === "none") return { verdict: "no ball left, no strike heard: a practice swing", kind: "OBSERVED", struck: false };
    if (b === "none" || s === "none") return { verdict: b === "none" ? "ball not seen leaving (sound unsure)" : "no strike heard (ball unsure)", kind: "UNKNOWN", struck: null };
    return { verdict: "not checked", kind: "UNKNOWN", struck: null };
  }
  // where a session was filmed, in four words: a Loop tee box, elsewhere on a hole, near a course (range, practice area, back yard), away
  function spotKind(s) { const w = (s && s.where) || {}; if (w.hole && w.spot === "tee") return "tee"; if (w.hole) return "hole"; if (w.course) return "near"; if (w.lat != null) return "away"; return "unknown"; }
  // one record per swing: when, who, where (course, hole, spot, the plan's club there), whether a ball was struck, the timing, and the
  // marked shot it belongs to when a round of that moment exists — otherwise outcome "unknown". This is the association layer: Loop
  // stores what it saw together and claims nothing about cause.
  function associations(sessions, rounds) {
    const out = [];
    for (const s of sessions) { const links = linkShots(s, rounds || []); const w = s.where || {};
      for (const sw of s.swings) { const L = links.find(x => x.swing === sw.index); const m = sw.metrics || {}; const g = k => m[k] && m[k].available ? m[k].value : null;
        out.push({ session: s.id, swing: sw.index, date: s.date || null, time: swingTime(s, sw), golfer: s.golfer, course: w.course || null, courseName: w.course_name || null, hole: w.hole || null, spot: w.spot || null,
          spotKind: spotKind(s), dM: w.d_m == null ? null : w.d_m, clubHint: w.club_hint ? w.club_hint.club : null, club: s.club || null, strike: strikeOf(sw), view: sw.view || null, excluded: !!sw.excluded,
          downswing: g("downswing_s"), tempo: g("tempo_ratio"), tempoSigma: m.tempo_ratio ? m.tempo_ratio.sigma : null, addressUnstable: !!(sw.sampling && sw.sampling.address_unstable),
          shot: L && L.round ? { round: L.round, hole: L.hole, shot: L.shot, dt: L.dt } : null, outcome: L && L.round ? "linked shot" : "unknown" }); } }
    return out;
  }

  // ---------- today vs normal from the shots themselves (the ledger) ----------
  const GROUPS = { Driver: "driver", "3-wood": "woods", Hybrid: "woods", "4-iron": "long irons", "5-iron": "long irons", "6-iron": "mid irons", "7-iron": "mid irons", "8-iron": "mid irons", "9-iron": "short irons", PW: "short irons", GW: "wedges", SW: "wedges", LW: "wedges" };
  function clubGroup(c) { return GROUPS[c] || null; }
  function shotRows(analyses) {
    const out = [];
    // the lateral miss against the line the engine gave for the shot (offAim); shots with no such line (lay-ups) are left out
    for (const a of analyses) { if (!a || a.sample) continue; for (const hn in a.holes) for (const s of a.holes[hn].shots) {
      const club = s.clubUsed || s.clubAssumed; if (s.offAim == null || !club || club === "partial wedge" || s.onGreen) continue; const g = clubGroup(club); if (!g) continue;
      const carry = (D.clubs.find(c => c.name === club) || {}).carry || 150;
      out.push({ round: a.id, date: a.date, hole: +hn, i: s.i, club, group: g, lat: s.offAim, latPct: s.offAim / carry, latLine: s.offLat, censored: !!s.offAimCensored, cat: s.cat }); } }
    return out;
  }
  // How much your days differ, from your own rounds (empirical Bayes). σ: the shot-to-shot spread of the lateral miss within a round
  // (pooled MAD around each round's median); τ: the spread of the rounds' medians beyond what σ explains. Today's median is shrunk toward
  // normal by k = (π/2)·σ²/τ² shots (the median's sampling variance against the day-to-day variance). Until 6 rounds hold 4+ shots of
  // the group, τ is the prior τ0 — so a few early shots barely move the target unless your own rounds show that your days really differ.
  function dayModel(pastRows) {
    const byR = {}; for (const r of pastRows) (byR[r.round] = byR[r.round] || []).push(r.latPct);
    const devs = [], meds = [], ns = [];
    for (const id in byR) { const a = byR[id];
      if (a.length >= 3) { const m = median(a); const d = a.map(x => Math.abs(x - m)).sort((x, y) => x - y); if (a.length % 2) d.shift(); for (const x of d) devs.push(x); }
      if (a.length >= RULES.minRoundShots) { meds.push(median(a)); ns.push(a.length); } }
    const sigma = devs.length >= 10 ? 1.4826 * median(devs) : RULES.sigma0;
    let tau = RULES.tau0, from = "prior";
    if (meds.length >= RULES.minRoundsTau) { const v = sd(meds) * sd(meds) - (Math.PI / 2) * sigma * sigma / mean(ns); tau = Math.min(RULES.tauMax, Math.max(RULES.tauMin, Math.sqrt(Math.max(0, v)))); from = "your rounds"; }
    return { sigma, tau, k: (Math.PI / 2) * sigma * sigma / (tau * tau), from, rounds: meds.length, sigmaFrom: devs.length >= 10 ? "your rounds" : "prior" };
  }
  // today's pattern per club group against the same group's normal (past real rounds), shrunk toward normal: shift = n/(n+k)·(today − normal)
  function todayShots(todayAnalysis, history) {
    const today = shotRows([todayAnalysis]); const past = shotRows(history.filter(a => a && a.id !== (todayAnalysis && todayAnalysis.id)));
    const out = {};
    for (const g of new Set(today.map(r => r.group))) {
      const t = today.filter(r => r.group === g), p = past.filter(r => r.group === g);
      const tl = t.map(r => r.latPct), pl = p.map(r => r.latPct);
      const normal = pl.length >= 6 ? median(pl) : 0;   // no history: the pin or fairway line (the engine's chosen line sits within a few yards of it)
      const dm = dayModel(p); const raw = median(tl) - normal; const shift = t.length / (t.length + dm.k) * raw;
      const carry = (D.clubs.find(c => GROUPS[c.name] === g) || {}).carry || 150;
      const spreadT = t.length >= 4 ? mad(tl) : null, spreadN = pl.length >= 8 ? mad(pl) : null;
      out[g] = { n: t.length, nNormal: p.length, todayMedPct: r3(median(tl)), normalMedPct: r3(normal), shiftPct: r3(shift), shiftYd: r3(shift * carry), rawShiftYd: r3(raw * carry),
        k: r3(dm.k), tau: r3(dm.tau), sigma: r3(dm.sigma), tauFrom: dm.from, sigmaFrom: dm.sigmaFrom, nRoundsTau: dm.rounds,
        spreadRatio: spreadT != null && spreadN ? r3(spreadT / spreadN) : null, normalFrom: pl.length >= 6 ? "your rounds" : "the model (no history yet)",
        enough: t.length >= RULES.minTodayShots && Math.abs(shift * carry) >= RULES.minShiftYd };
    }
    return out;
  }
  // the engine's parameters for today: the pattern shifted by today's (shrunk) offset for the club that is about to be hit
  function todayParams(P, ts, club) {
    const g = clubGroup(club); const x = g && ts[g]; if (!x || !x.enough) return null;
    return Object.assign({}, P, { lat_bias: (P.lat_bias || 0) + x.shiftPct });
  }

  // ---------- experiments: pre-registered hypotheses, tested only when the data allow ----------
  // Two-sided permutation test on the difference of means (deterministic seed), with a bootstrap 90% interval for the difference.
  function permutationTest(a, b, iters, seed) {
    const all = a.concat(b), na = a.length; const obs = mean(a) - mean(b); const R = rng(seed || 7); let ge = 0; const n = iters || 2000;
    const arr = all.slice();
    for (let it = 0; it < n; it++) { for (let i = arr.length - 1; i > 0; i--) { const j = Math.floor(R() * (i + 1)); const t = arr[i]; arr[i] = arr[j]; arr[j] = t; }
      const d = mean(arr.slice(0, na)) - mean(arr.slice(na)); if (Math.abs(d) >= Math.abs(obs) - 1e-12) ge++; }
    return { diff: obs, p: (ge + 1) / (n + 1) };
  }
  function bootstrapCI(a, b, iters, seed) {
    const R = rng((seed || 7) + 1); const n = iters || 1000; const ds = [];
    for (let it = 0; it < n; it++) { const ra = a.map(() => a[Math.floor(R() * a.length)]), rb = b.map(() => b[Math.floor(R() * b.length)]); ds.push(mean(ra) - mean(rb)); }
    ds.sort((x, y) => x - y); return [ds[Math.floor(0.05 * n)], ds[Math.floor(0.95 * n)]];
  }
  // H1 (shots only, testable from rounds): a day's early tee-shot miss persists — on days whose first tee shots miss right of normal, the
  // rest of that day's full shots also miss right (and left with left). If it does not hold, adapting the target to "today" chases noise.
  // H2 (swing → shot): on days when your warm-up tempo is outside your normal range, that day's full shots miss wider (lateral spread).
  const HYPOTHESES = [
    { id: "H1-persist", registered: "2026-10-07", statement: "A day's early miss persists: when your first 4 tee shots miss right of your normal, your other full shots that day miss right too (and left with left).",
      x: "the median lateral miss (% of carry) of the day's first 4 tee shots, against your normal", y: "the median lateral miss of the day's later full shots, against your normal",
      test: "permutation test, days with an early miss beyond ±1.5% of carry (right vs left), two-sided α = 0.05; 90% bootstrap interval", minPerGroup: 4, alpha: 0.05,
      decides: "whether Loop may move today's target from today's early shots (Today mode)" },
    { id: "H2-tempo-spread", registered: "2026-10-07", statement: "When your tempo on the day is outside your normal range, your full shots that day spread wider.",
      x: "the day's swing session tempo ratio against your normal (|z| ≥ 2 = outside)", y: "the robust spread (MAD) of that day's lateral misses, % of carry",
      test: "permutation test, outside vs within days, two-sided α = 0.05", minPerGroup: 4, alpha: 0.05,
      decides: "whether a tempo reading before a round should widen the engine's pattern for that day" },
    { id: "H3-tee-vs-elsewhere", registered: "2026-10-07", statement: "Your downswing on a tee box differs from your downswing elsewhere (range, practice area, back yard).",
      x: "where the swing was filmed, from the phone's position: on a Loop tee box, or anywhere else", y: "the downswing time (top to impact, s) — the one timing the harness reads the same at 30 and 240 fps; your real-time, non-excluded swings only",
      test: "permutation test on the difference of means, tee vs elsewhere, two-sided α = 0.05; 90% bootstrap interval; the swing is the unit (sessions are one swing each)", minPerGroup: 4, alpha: 0.05,
      decides: "whether a range session's timing can stand in for the course (Today mode's swing line) or the course itself must be filmed" },
  ];
  function evalH1(analyses) {
    const rows = shotRows(analyses); const byDay = {};
    for (const r of rows) (byDay[r.round] = byDay[r.round] || []).push(r);
    const allTee = rows.filter(r => r.cat === "tee").map(r => r.latPct); const normal = allTee.length ? median(allTee) : 0;
    const right = [], left = [];
    for (const id in byDay) { const d = byDay[id].sort((x, y) => x.hole - y.hole || x.i - y.i); const tee = d.filter(r => r.cat === "tee"); if (tee.length < 6) continue;
      const early = tee.slice(0, 4).map(r => r.latPct); const laterRows = d.filter(r => !tee.slice(0, 4).includes(r)); if (laterRows.length < 4) continue;
      const e = median(early) - normal, l = median(laterRows.map(r => r.latPct)) - normal;
      if (e > 0.015) right.push(l); else if (e < -0.015) left.push(l); }
    return evalGroups(HYPOTHESES[0], right, left, "days with an early right miss", "days with an early left miss", "% of carry");
  }
  function evalH2(sessions, analyses) {
    const base = baseline(sessions); const outside = [], within = [];
    const rowsByDate = {}; for (const r of shotRows(analyses)) (rowsByDate[r.date] = rowsByDate[r.date] || []).push(r.latPct);
    for (const s of sessions) { if (s.golfer !== "me" || !s.date || !rowsByDate[s.date] || rowsByDate[s.date].length < 6) continue;
      const tv = todayVsNormal(sessions, s).out; let z = null; for (const v in tv) if (tv[v].tempo_ratio && tv[v].tempo_ratio.z != null) z = tv[v].tempo_ratio.z;
      if (z == null) continue; const spread = mad(rowsByDate[s.date]); (Math.abs(z) >= 2 ? outside : within).push(spread); }
    return evalGroups(HYPOTHESES[1], outside, within, "days outside your tempo range", "days within it", "% of carry (spread)");
  }
  function evalH3(sessions) {
    const rows = associations(sessions, []).filter(r => r.golfer === "me" && !r.excluded && r.strike.struck !== false && r.downswing != null && r.spotKind !== "unknown");
    const tee = rows.filter(r => r.spotKind === "tee").map(r => r.downswing), other = rows.filter(r => r.spotKind !== "tee").map(r => r.downswing);
    return evalGroups(HYPOTHESES[2], tee, other, "swings on a tee box", "swings elsewhere", "s", fmtMs);
  }
  function evalGroups(h, a, b, la, lb, unit, fmt) {
    const F = fmt || fmtN;
    const res = { id: h.id, statement: h.statement, groups: [{ label: la, n: a.length, mean: r3(mean(a)) }, { label: lb, n: b.length, mean: r3(mean(b)) }], unit, registered: h.registered, evaluated: new Date().toISOString().slice(0, 10) };
    if (a.length < h.minPerGroup || b.length < h.minPerGroup) { res.status = "insufficient"; res.evidence = "UNKNOWN"; res.text = `Not testable yet: ${a.length} ${la} and ${b.length} ${lb}; the test needs ${h.minPerGroup} of each. Nothing is concluded.`; return res; }
    const pt = permutationTest(a, b, 4000, 11), ci = bootstrapCI(a, b, 2000, 11);
    res.diff = r3(pt.diff); res.p = r3(pt.p); res.ci90 = ci.map(r3);
    res.status = pt.p < h.alpha ? "supported" : "not supported"; res.evidence = pt.p < h.alpha ? "INFERRED" : "OBSERVED";
    res.text = pt.p < h.alpha ? `Supported for you: ${la} average ${F(mean(a))} vs ${F(mean(b))} for ${lb} (difference ${F(pt.diff)}, 90% interval ${F(ci[0])} to ${F(ci[1])}, p = ${pt.p.toFixed(3)}, n = ${a.length} + ${b.length}).`
      : `Not supported (yet): ${la} average ${F(mean(a))} vs ${F(mean(b))} for ${lb} — difference ${F(pt.diff)} (90% interval ${F(ci[0])} to ${F(ci[1])}), p = ${pt.p.toFixed(2)}, n = ${a.length} + ${b.length}. Loop does not act on it.`;
    return res;
  }
  function fmtN(x) { return x == null || !isFinite(x) ? "–" : (x > 0 ? "+" : "") + (Math.abs(x) < 1 ? (x * 100).toFixed(1) + "%" : x.toFixed(2)); }
  function fmtMs(x) { return x == null || !isFinite(x) ? "–" : (x > 0 ? "+" : "") + (x * 1000).toFixed(0) + " ms"; }

  // ---------- the evidence graph ----------
  // Nodes and edges built from the record. Every edge carries its evidence (the numbers), n, a confidence, a timestamp and a source.
  function conf(n, needed) { return n >= 2 * needed ? "solid" : n >= needed ? "some" : n >= 1 ? "thin" : "none"; }
  function graph(ctx) {
    const nodes = [], edges = []; const now = new Date().toISOString();
    const node = (id, type, label, extra) => { if (!nodes.find(n => n.id === id)) nodes.push(Object.assign({ id, type, label }, extra || {})); return id; };
    const edge = (from, to, relation, e) => edges.push(Object.assign({ from, to, relation, timestamp: e.timestamp || now, source: e.source }, e));
    // 1. decisions → the alternative the engine priced → expected values → what happened (from the ledger)
    for (const a of ctx.analyses || []) { if (!a || a.sample) continue; for (const hn in a.holes) for (const s of a.holes[hn].shots) { if (s.sg_dec == null || !s.alt) continue;
      const d = node(`dec:${a.id}:${hn}:${s.i}`, "DECISION", `${a.date} hole ${hn} shot ${s.i + 1}: ${s.cat === "tee" ? s.clubUsed : s.intent === "go" ? "went for the green" : "laid up"}`, { round: a.id });
      const alt = node(`alt:${a.id}:${hn}:${s.i}`, "ALTERNATIVE", s.alt.what);
      edge(d, alt, "priced against", { evidence: { chosenE: s.E_intent, altE: s.alt.E, decisionCost: s.sg_dec }, n: 1, confidence: "model", kind: "ESTIMATED", source: "engine simulation (ledger.js)", timestamp: a.date });
      const res = node(`res:${a.id}:${hn}:${s.i}`, "OUTCOME", `shot result ${s.sg_exec != null ? (s.sg_exec >= 0 ? "+" : "") + s.sg_exec.toFixed(2) : "–"} against the choice`);
      edge(d, res, "then played", { evidence: { execution: s.sg_exec, sg: s.sg }, n: 1, confidence: "observed", kind: "OBSERVED", source: "marked positions (ledger.js)", timestamp: a.date }); } }
    // 2. swing observations → shot pattern → outcome → strokes gained (sessions on a day with a round, or linked shot by shot)
    for (const s of ctx.sessions || []) { if (s.golfer !== "me") continue; const tv = todayVsNormal(ctx.sessions, s).out;
      for (const v in tv) for (const k in tv[v]) { const c = tv[v][k]; if (!c || c.verdict === "not measured") continue;
        const sw = node(`sw:${s.id}:${v}:${k}`, "SWING_OBSERVATION", `${s.date || "undated"} ${METRICS[k] ? METRICS[k].label : k} (${v}): ${c.verdict}`, { session: s.id, metric: k, view: v });
        const rounds = (ctx.analyses || []).filter(a => a && !a.sample && a.date === s.date);
        for (const a of rounds) { const rows = shotRows([a]); const sp = node(`pat:${a.id}`, "SHOT_PATTERN", `${a.date} full-shot misses: median ${fmtN(median(rows.map(r => r.latPct)))} of carry (n ${rows.length})`, { round: a.id });
          edge(sw, sp, "same day as", { evidence: { swing: c, shots: rows.length }, n: Math.min(c.n || 0, rows.length), confidence: conf(Math.min(c.n || 0, rows.length), 10), kind: "OBSERVED", source: "swing harness + ledger", timestamp: s.date, association: "co-occurrence only, not cause" });
          const out = node(`sg:${a.id}`, "STROKES_GAINED", `${a.date} ${a.sgTotal != null ? (a.sgTotal >= 0 ? "+" : "") + a.sgTotal.toFixed(1) : "–"} against the engine`, { round: a.id });
          edge(sp, out, "scored", { evidence: { sg: a.sgTotal, cats: a.cats }, n: a.nScored, confidence: conf(a.nComplete, 9), kind: "ESTIMATED", source: "ledger.js (curve-priced positions)", timestamp: a.date }); } } }
    // 2b. swing sessions → the hole they were filmed on (the phone's position against Loop's map): co-location, with the strike checked
    //     in the video; the shot's outcome stays unknown until a marked round of that moment links it
    for (const s of ctx.sessions || []) { const w = s.where; if (!w || !w.hole) continue;
      const hid = node(`ctx:${w.course}:${w.hole}`, "HOLE_CONTEXT", `${w.course_name || w.course} hole ${w.hole}${w.club_hint ? ` (the plan's club: ${w.club_hint.club})` : ""}`, { course: w.course, hole: w.hole });
      const sws = s.swings.filter(x => !x.excluded); const struck = sws.filter(x => strikeOf(x).struck === true).length;
      const sid = node(`ses:${s.id}`, "SWING_OBSERVATION", `${s.date || "undated"} ${s.golfer === "me" ? "your" : s.golfer === "unknown" ? "an unlabelled" : s.golfer + "'s"} ${sws.length} swing${sws.length === 1 ? "" : "s"} (${w.spot})`, { session: s.id });
      edge(sid, hid, "filmed on", { evidence: { spot: w.spot, d_m: w.d_m == null ? null : w.d_m, struck, located: "OBSERVED position, INFERRED hole" }, n: sws.length, confidence: w.spot === "tee" ? "located (tee)" : "located", kind: "OBSERVED",
        source: "the video's location tag against Loop's map (where.py); the strike from the video's own clocks", timestamp: s.date, association: "co-location only; the shot's outcome is unknown until a marked round links it" }); }
    // 3. practice change → swing change → shot change → scoring change (before/after the date the practice started)
    for (const pc of ctx.practice || []) {
      const p = node(`pc:${pc.id}`, "PRACTICE_CHANGE", `${pc.date}: ${pc.what}`, pc);
      const before = (ctx.sessions || []).filter(s => s.golfer === "me" && s.date && s.date < pc.date), after = (ctx.sessions || []).filter(s => s.golfer === "me" && s.date && s.date >= pc.date);
      const key = pc.metric || "tempo_ratio"; const vals = ss => { const out = []; for (const s of ss) for (const w of s.swings) { const m = w.metrics[key]; if (m && m.available && m.value != null && !w.excluded) out.push(m.value); } return out; };
      const vb = vals(before), va = vals(after); const ok = vb.length >= 6 && va.length >= 6; const pt = ok ? permutationTest(va, vb, 2000, 5) : null;
      const swc = node(`swc:${pc.id}`, "SWING_CHANGE", `${METRICS[key] ? METRICS[key].label : key}: before ${fmtN(mean(vb))} (n ${vb.length}) → after ${fmtN(mean(va))} (n ${va.length})`);
      edge(p, swc, "changed?", { evidence: { before: { n: vb.length, mean: r3(mean(vb)) }, after: { n: va.length, mean: r3(mean(va)) }, p: pt ? r3(pt.p) : null }, n: Math.min(vb.length, va.length), confidence: ok ? (pt.p < 0.05 ? "supported" : "not supported") : "insufficient", kind: ok ? (pt.p < 0.05 ? "INFERRED" : "OBSERVED") : "UNKNOWN", source: "swing sessions", timestamp: pc.date });
      const rb = (ctx.analyses || []).filter(a => a && !a.sample && a.date < pc.date), ra = (ctx.analyses || []).filter(a => a && !a.sample && a.date >= pc.date);
      const lb = shotRows(rb).map(r => Math.abs(r.latPct)), la = shotRows(ra).map(r => Math.abs(r.latPct));
      const shc = node(`shc:${pc.id}`, "SHOT_CHANGE", `full-shot |miss|: before ${fmtN(mean(lb))} (n ${lb.length}) → after ${fmtN(mean(la))} (n ${la.length})`);
      const okS = lb.length >= 10 && la.length >= 10; const ps = okS ? permutationTest(la, lb, 2000, 6) : null;
      edge(swc, shc, "then the shots?", { evidence: { before: lb.length, after: la.length, p: ps ? r3(ps.p) : null }, n: Math.min(lb.length, la.length), confidence: okS ? (ps.p < 0.05 ? "supported" : "not supported") : "insufficient", kind: okS ? "OBSERVED" : "UNKNOWN", source: "ledger", timestamp: pc.date });
      const sgb = rb.map(a => a.sgTotal).filter(x => x != null), sga = ra.map(a => a.sgTotal).filter(x => x != null);
      const scc = node(`scc:${pc.id}`, "SCORING_CHANGE", `strokes gained a round: before ${fmtN(mean(sgb))} (${sgb.length}) → after ${fmtN(mean(sga))} (${sga.length})`);
      const okR = sgb.length >= 4 && sga.length >= 4; const pr = okR ? permutationTest(sga, sgb, 2000, 7) : null;
      edge(shc, scc, "then the scores?", { evidence: { before: sgb.length, after: sga.length, p: pr ? r3(pr.p) : null }, n: Math.min(sgb.length, sga.length), confidence: okR ? (pr.p < 0.05 ? "supported" : "not supported") : "insufficient", kind: okR ? "OBSERVED" : "UNKNOWN", source: "ledger", timestamp: pc.date, looksVsPlays: okS || ok ? lookVsPlay(ok && pt.p < 0.05, okR && pr.p < 0.05) : null });
    }
    return { nodes, edges };
  }
  // the distinction the brief asks for: a change that shows in the swing is not the same as a change that shows in the scores
  function lookVsPlay(swingChanged, scoresChanged) { return swingChanged && !scoresChanged ? "looks different, does not (yet) play better" : swingChanged && scoresChanged ? "looks and plays different" : !swingChanged && scoresChanged ? "plays different, the swing measurement did not move" : "neither has moved"; }

  window.LoopSwing = { SCHEMA, METRICS, NEVER, RULES, HYPOTHESES, normalize, sessionStats, baseline, compareMetric, todayVsNormal, linkShots, swingTime, shotRows, dayModel, todayShots, todayParams,
    clubGroup, permutationTest, bootstrapCI, evalH1, evalH2, evalH3, evalGroups, graph, lookVsPlay, median, mad, mean, sd, fmtN, fmtMs, strikeOf, spotKind, associations };
})();

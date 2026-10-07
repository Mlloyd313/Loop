/* Loop ledger — strokes gained against Loop's own engine, from the ball positions you mark during a round.
   Mirrors pipeline/ledger.py (same accounting; tests.py checks they agree).

   The idea: the engine already prices any point of any hole for your pattern on the measured ground (E = expected strokes to hole
   out from there, including penalties). A round is a chain of positions p1 (tee) → p2 → … → holed. Each shot is worth
       SG_i = E(p_i) − E(p_i+1) − strokes_i          (strokes_i = 1 + any penalty taken on the way to p_i+1)
   and the chain telescopes:  Σ SG_i = E(tee) − score.  Where the engine offered a choice (which tee club; go for the green or lay up)
   the shot's SG splits into what the DECISION cost (E_engine's best − E_what you chose, ≤ 0) and what the EXECUTION earned
   (E_what you chose − E(next) − strokes). Nothing here is a swing diagnosis: Loop sees where the ball went, not how you swung. */
(function () {
  const D = window.LOOP_DATA, E = window.LoopEngine, L = E.L, YD = E.YD;
  const CATS = ["tee", "approach", "layup", "short", "putt", "finish"];
  const CAT_LABEL = { tee: "tee shots", approach: "approach shots", layup: "lay-ups", short: "short game (inside 50)", putt: "putting", finish: "finishing (unresolved)", decision: "decisions" };

  // ---------- small helpers ----------
  function distYd(a, b) { return Math.hypot(a[0] - b[0], a[1] - b[1]) / YD; }
  // lateral (+ right) and depth (+ long) of `to`, relative to the line from `from` toward `target`; yards
  function offsets(from, to, target) {
    const vx = target[0] - from[0], vy = target[1] - from[1]; const L0 = Math.hypot(vx, vy) || 1; const ux = vx / L0, uy = vy / L0;
    const dx = to[0] - from[0], dy = to[1] - from[1]; const along = dx * ux + dy * uy; const lat = -dx * uy + dy * ux;   // right-hand normal (−uy, ux): +y is right in the frame
    return { lat: lat / YD, depth: (along - L0) / YD, along: along / YD };
  }
  function median(a) { if (!a.length) return null; const b = a.slice().sort((x, y) => x - y); const m = b.length >> 1; return b.length % 2 ? b[m] : (b[m - 1] + b[m]) / 2; }
  function mad(a) { const m = median(a); if (m == null) return null; return median(a.map(x => Math.abs(x - m))) * 1.4826; }   // robust σ
  function round2(x) { return x == null || isNaN(x) ? null : Math.round(x * 100) / 100; }
  function lieWord(l) { return ({ 0: "desert", 1: "fairway", 2: "rough", 3: "green", 4: "sand", 5: "water", 6: "another green", 7: "waste area", 8: "scrub", 9: "tee" })[l] || "?"; }
  function clubNames(P) { const names = D.clubs.map(c => c.name); for (const c of (P.clubsOverride || [])) if (!names.includes(c.name)) names.push(c.name); return names; }

  // Which club covers this distance from this lie? Nearest total; "partial wedge" below three quarters of the shortest club.
  function inferClub(totalYd, P, altf, fromLie, tee) {
    const lf = E.LIEFX[fromLie] || E.LIEFX[1]; const rows = [];
    for (const name of clubNames(P)) { if (name === "Driver" && !tee) continue; const cp = E.clubParams(name, P, altf); rows.push({ name, total: cp.carry * lf.carry + cp.roll }); }
    rows.sort((a, b) => a.total - b.total);
    if (totalYd < rows[0].total * 0.75) return { name: "partial wedge", total: totalYd, conf: "partial" };
    let bi = 0; for (let i = 1; i < rows.length; i++) if (Math.abs(rows[i].total - totalYd) < Math.abs(rows[bi].total - totalYd)) bi = i;
    const d = Math.abs(rows[bi].total - totalYd);
    const gapLo = bi > 0 ? (rows[bi].total - rows[bi - 1].total) / 2 : 15, gapHi = bi < rows.length - 1 ? (rows[bi + 1].total - rows[bi].total) / 2 : 25;
    return { name: rows[bi].name, total: rows[bi].total, conf: d <= Math.min(gapLo, gapHi) * 0.6 ? "likely" : "uncertain", d };
  }

  // ---------- one hole ----------
  // rec = { shots: [{x, y, src, acc, t, lie?, club?, intent?, pen?}], score, putts }   (shot = the position the ball was played FROM; shot 1 is the tee)
  function analyzeHole(c, h, rec, P) {
    const shots = (rec && rec.shots) || []; const out = { hole: h.hole, par: h.par, card: h.card, score: rec && rec.score != null ? rec.score : null, putts: rec && rec.putts != null ? rec.putts : null, shots: [], flags: [], E_tee: null, sgTotal: null, sgSum: null, cats: {}, marks: shots.length };
    if (h.nodata || !h.grid || (h.src && h.src.fairway === "none" && h.par !== 3)) { out.kind = "unpriced"; out.flags.push("the engine does not price this hole (no measured line or surfaces)"); return out; }
    const altf = 1 + P.alt_rule / 100 * (c.alt_ft - P.home_ft) / 1000;
    const H = E.decodeHole(h); E.applyPin(H, P);
    const planClub = rec && rec.planClub !== undefined ? rec.planClub : h.plan && h.plan.club;
    const r = E.runHole(c, h, P, { n: 800, planClub });
    out.kind = r.kind; out.E_tee = r.E; out.planE = r.planE != null ? r.planE : null; out.planClub = planClub || null;
    out.pick = r.kind === "tee" ? { club: r.pick.club, aim: r.pick.aim, window: r.pick.window } : { club: r.approach ? r.approach.club : null };
    if (r.E == null) { out.kind = "unpriced"; out.flags.push("no expectation for this hole"); return out; }
    const k = shots.length; const penTotal = shots.reduce((s, x) => s + (x.pen || 0), 0); out.penalties = penTotal;
    let u = null;   // unmarked strokes after the last marked shot
    if (out.score != null) { u = out.score - k - penTotal; out.scoreUsed = out.score; if (u < 0) { out.flags.push(`score ${out.score} is below the ${k} marked strokes and ${penTotal} penalt${penTotal === 1 ? "y" : "ies"}; using ${k + penTotal}`); out.scoreUsed = k + penTotal; u = 0; } }
    // pass 1: every position's expectation
    const S = shots.map((s, i) => {
      const isTee = i === 0; const pos = isTee ? [0, 0] : [s.x, s.y];
      const inFrame = isTee || (pos[0] >= h.frame.x0 - 60 && pos[0] <= h.frame.x1 + 60 && Math.abs(pos[1]) <= h.frame.w + 60);
      const gridLie = isTee ? L.TEE : E.lieAt(H, pos[0], pos[1]); let lie = s.lie != null ? s.lie : gridLie;
      // A position you played from is playable: the engine's "desert/water = a stroke and a drop" rule is for landings. Your penalty flag
      // is the only thing that charges a penalty stroke, so a marked lie in desert or water is priced as a rough lie (wider, shorter), not twice.
      const playedFromHazard = lie === L.DESERT || lie === L.WATER; if (playedFromHazard) lie = L.ROUGH;
      const rYd = distYd(pos, H.pin);
      const o = { i, pos: [round2(pos[0]), round2(pos[1])], lie, gridLie, lieSet: s.lie != null, playedFromHazard, rYd: Math.round(rYd), rFt: Math.round(rYd * 3), onGreen: lie === L.GREEN, pen: s.pen || 0, src: s.src || null, acc: s.acc != null ? Math.round(s.acc) : null, t: s.t || null, club: s.club || null, intentSet: s.intent || null, flags: [] };
      if (isTee && s.x != null && s.y != null && Math.hypot(s.x, s.y) > 40) o.flags.push(`marked ${Math.round(Math.hypot(s.x, s.y) / YD)} yd from the mapped tee; priced from the tee`);
      if (!inFrame) o.flags.push("off this hole's map — not priced");
      if (s.acc > 12) o.flags.push(`GPS fix ±${Math.round(s.acc)} m`);
      if (!inFrame) { o.E = null; return o; }
      if (isTee) { o.E = r.E; o._tee = r; return o; }
      // The chain value of a position is its price — the baseline for its lie and plays-like distance plus the penalty terms — exactly what
      // the engine charges every simulated landing and what the price map paints. (The simulated approach from a spot is systematically a
      // little more optimistic than the curve inside 200 yd; pricing positions by simulation would credit every tee shot and debit every
      // approach by that difference. Simulation is used where two options are compared: tee clubs, go vs lay-up.)
      const pr = E.priceAt(h, pos, P, lie); o.E = pr.E; o.plays = Math.round(pr.plays);
      if (o.onGreen) return o;
      const a = E.approach(h, pos, P, altf, { n: 600, keep: 0, fromLie: lie }); o._app = a;
      o.engineClub = a.club; o.simE = a.best ? a.best.E : null; o.simOn = a.best ? a.best.odds.green : null; o.E_go = o.simE;
      if (rYd >= 160 && h.par >= 4) { const gl = E.goVsLay(h, pos, P, altf, { n: 600, keep: 0, fromLie: lie }); if (gl && gl.lay) { o._gl = gl; o.E_lay = gl.lay.E; o.layLeave = gl.lay.leave; o.E_go = gl.go.best ? gl.go.best.E : null; } }
      return o;
    });
    // pass 2: strokes gained per shot, decision and execution
    const cats = {}; for (const cc of CATS.concat(["decision"])) cats[cc] = { sg: 0, n: 0 };
    let allScored = k > 0;
    for (let i = 0; i < k; i++) {
      const o = S[i], nx = S[i + 1], last = i === k - 1;
      let E_next, strokes;
      if (!last) { if (nx.E == null) { o.sg = null; o.flags.push("next position off the map — not scored"); allScored = false; continue; } E_next = nx.E; strokes = 1 + (nx.pen || 0); }
      else if (u != null) { E_next = 0; strokes = 1 + u; o.tail = u; }
      else { o.sg = null; o.unresolved = "hole not finished"; allScored = false; continue; }
      if (o.E == null) { o.sg = null; allScored = false; continue; }
      // category
      let cat = i === 0 ? (h.par === 3 ? "approach" : "tee") : o.onGreen ? "putt" : o.rYd <= 50 ? "short" : "approach";
      // club: set by you, else inferred from how far the ball went (not after a penalty: the drop hides the shot)
      if (!o.onGreen && nx && !(nx.pen > 0) && nx.E != null) { const inf = inferClub(distYd([S[i].pos[0], S[i].pos[1]], nx.pos), P, altf, o.lie, i === 0); o.clubInferred = inf.name; o.clubConf = inf.conf; }
      o.clubUsed = o.club || o.clubInferred || null;
      // the shot's whole worth: the chain
      o.sg = o.E - E_next - strokes; o.E_next = E_next; o.strokes = strokes;
      // decision layer: the engine's best option against the one you took, both priced the same way; execution is the rest
      o.sg_dec = null;
      if (cat === "tee") {
        const club = o.clubUsed;
        if (club && club !== "partial wedge") {
          let po = o._tee.options.find(x => x.club === club);
          if (!po) { const extra = E.teeOptions(h, P, altf, { n: 800, keep: 0, clubs: [club] }); po = extra[0]; }
          o.E_intent = po.best.E; o.sg_dec = r.E - o.E_intent; o.engineClub = r.pick.club; o.engineE = r.E; o.alt = club === r.pick.club ? null : { what: r.pick.club + " (the engine's pick)", E: r.E };
        } else { o.E_intent = r.E; o.flags.push("club unknown — the decision is not separated from the swing"); }
      } else if (o.E_lay != null) {
        let intent = o.intentSet;
        if (!intent) {
          if (o.E_go == null) intent = "lay";
          else if (nx && !(nx.pen > 0) && nx.E != null) { const trav = distYd(S[i].pos, nx.pos); intent = (trav >= o.rYd - 30 || nx.onGreen || nx.rYd <= 45) ? "go" : "lay"; }
          else if (o.club) { const cp = E.clubParams(o.club, P, altf); intent = cp.carry + cp.roll >= o.rYd - 30 ? "go" : "lay"; }
        }
        if (intent) { o.intent = intent; o.E_intent = intent === "go" ? o.E_go : o.E_lay; const bestE = Math.min(o.E_go == null ? 1e9 : o.E_go, o.E_lay); o.sg_dec = bestE - o.E_intent; o.alt = intent === "go" ? { what: "laying up to " + o.layLeave, E: o.E_lay } : { what: "going for the green", E: o.E_go }; if (intent === "lay") cat = "layup"; }
        else { o.E_intent = o.E; o.flags.push("go or lay-up unknown — the decision is not separated"); }
      } else o.E_intent = o.E;
      o.sg_exec = o.sg - (o.sg_dec || 0);
      if (last && u != null && u > 0 && !o.onGreen) { cat = "finish"; o.unresolved = `${1 + u} strokes from here to the cup, none of them marked after this one`; }
      if (o.onGreen && last && u != null) o.putts = 1 + u;
      o.cat = cat;
      if (nx) { o.nextR = nx.rYd; o.nextFt = nx.rFt; o.nextLie = nx.playedFromHazard ? nx.gridLie : nx.lie; o.nextPen = nx.pen || 0; }
      // where the ball went, for patterns (not after a penalty)
      if (nx && nx.E != null && !(nx.pen > 0)) {
        o.resultLie = nx.lie;
        if (i === 0 && h.par !== 3) { const seg = h.line.length > 2 ? h.line[1] : H.basePin; const off = offsets([0, 0], nx.pos, seg); o.offLat = round2(off.lat); o.total = Math.round(off.along); }
        else if (!o.onGreen) { const off = offsets(S[i].pos, nx.pos, H.pin); o.offLat = round2(off.lat); if (cat !== "layup") o.offDepth = round2(off.depth); o.total = Math.round(distYd(S[i].pos, nx.pos)); }
        else o.next_rFt = nx.rFt;
      }
      cats[cat].sg += o.sg_exec; cats[cat].n++;
      if (o.sg_dec != null) { cats.decision.sg += o.sg_dec; cats.decision.n++; }
    }
    // putts: marked first putt + unmarked tail; or entered
    const lastS = S[k - 1];
    if (lastS && lastS.onGreen && u != null) { out.puttsInferred = 1 + u; if (out.putts != null && out.putts !== out.puttsInferred) out.flags.push(`you entered ${out.putts} putts but the marks say ${out.puttsInferred}`); }
    out.sgSum = allScored ? S.reduce((s, o) => s + (o.sg || 0), 0) : null;
    out.sgTotal = (out.scoreUsed != null) ? r.E - out.scoreUsed : null;
    out.complete = allScored && out.scoreUsed != null;
    for (const cc in cats) { cats[cc].sg = round2(cats[cc].sg); } out.cats = cats;
    out.shots = S.map(o => { const q = {}; for (const key in o) if (key[0] !== "_") q[key] = typeof o[key] === "number" ? round2(o[key]) : o[key]; return q; });
    return out;
  }

  // ---------- a round ----------
  function roundParams(round) { return Object.assign({}, D.defaults, round.P || {}); }
  function holesToAnalyze(round) { const c = D.courses.find(x => x.key === round.course); if (!c) return []; return c.holes.filter(h => { const rec = round.holes && round.holes[h.hole]; return rec && ((rec.shots && rec.shots.length) || rec.score != null); }); }
  function analyzeRound(round, opts) {
    const c = D.courses.find(x => x.key === round.course); if (!c) return null;
    const P = roundParams(round); const holes = {};
    for (const h of holesToAnalyze(round)) holes[h.hole] = analyzeHole(c, h, round.holes[h.hole], P);
    return assemble(round, holes, opts);
  }
  // assemble() turns per-hole analyses into the round's record (the app computes the holes in time slices, then calls this)
  function assemble(round, holes, opts) {
    const c = D.courses.find(x => x.key === round.course); if (!c) return null;
    const P = roundParams(round); let E_sum = 0, score_sum = 0, nScored = 0, nMarked = 0, nComplete = 0;
    const cats = {}; for (const cc of CATS.concat(["decision"])) cats[cc] = { sg: 0, n: 0 };
    const flags = [];
    for (const h of c.holes) {
      const a = holes[h.hole]; if (!a) continue;
      if (a.marks) nMarked++;
      if (a.kind === "unpriced") { if (a.score != null) score_sum += a.score; continue; }
      if (a.scoreUsed != null) { nScored++; score_sum += a.scoreUsed; E_sum += a.E_tee; }
      if (a.complete) { nComplete++; for (const cc in cats) { cats[cc].sg += a.cats[cc].sg || 0; cats[cc].n += a.cats[cc].n || 0; } }
      for (const f of a.flags) flags.push({ hole: h.hole, text: f });
      for (const s of a.shots) for (const f of s.flags) flags.push({ hole: h.hole, shot: s.i + 1, text: f });
    }
    for (const cc in cats) cats[cc].sg = round2(cats[cc].sg);
    const res = { id: round.id, course: c.key, courseName: c.club === c.name ? c.name : c.club + " — " + c.name, date: round.date, name: round.name || null, sample: !!round.sample, legacy: !!round.legacy, holes, nScored, nMarked, nComplete, nHoles: Object.keys(holes).length, score: nScored ? score_sum : null, E_tee: nScored ? round2(E_sum) : null, sgTotal: nScored ? round2(E_sum - score_sum) : null, cats, flags, P: { wind_mph: P.wind_mph, wind_from: P.wind_from, temp_f: P.temp_f, setting: P.setting, pin: P.pin, baseline: P.baseline, disp: P.disp } };
    res.patterns = patterns(res); res.review = review(res, opts && opts.history || []);
    return res;
  }

  // ---------- patterns over the shots of one analysis (or several, when fed a merged list) ----------
  function allShots(res) { const out = []; for (const hn in res.holes) for (const s of res.holes[hn].shots) if (s.sg != null) out.push(Object.assign({ hole: +hn }, s)); return out; }
  function share(arr, pred) { const n = arr.length; if (!n) return { n: 0, p: null, k: 0 }; const k = arr.filter(pred).length; return { n, k, p: k / n }; }
  function patterns(res) {
    const shots = allShots(res); const p = {};
    const appr = shots.filter(s => (s.cat === "approach" || s.cat === "short") && s.offLat != null && s.offDepth != null);
    p.approach = { n: appr.length, right: share(appr, s => s.offLat > 5), left: share(appr, s => s.offLat < -5), short: share(appr, s => s.offDepth < -8), long: share(appr, s => s.offDepth > 8), onGreen: share(appr, s => s.resultLie === L.GREEN), medLat: round2(median(appr.map(s => s.offLat))), medDepth: round2(median(appr.map(s => s.offDepth))) };
    const tees = shots.filter(s => s.cat === "tee" && s.offLat != null);
    p.tee = { n: tees.length, right: share(tees, s => s.offLat > 10), left: share(tees, s => s.offLat < -10), fairway: share(tees, s => s.resultLie === L.FAIRWAY || s.resultLie === L.TEE), trouble: share(tees, s => [L.DESERT, L.WATER, L.SAND, L.SCRUB, L.WASTE].includes(s.resultLie)), medLat: round2(median(tees.map(s => s.offLat))), medTotal: Math.round(median(tees.map(s => s.total)) || 0) };
    // decisions
    const teeDec = shots.filter(s => s.cat === "tee" && s.sg_dec != null); const golay = shots.filter(s => (s.cat === "approach" || s.cat === "layup") && s.E_lay != null && s.sg_dec != null);
    p.decisions = { teeN: teeDec.length, teeFollowed: teeDec.filter(s => s.clubUsed === s.engineClub).length, teeCost: round2(teeDec.reduce((a, s) => a + s.sg_dec, 0)), golayN: golay.length, golayFollowed: golay.filter(s => s.sg_dec > -0.01).length, golayCost: round2(golay.reduce((a, s) => a + s.sg_dec, 0)) };
    // per club: measured totals and offline, execution SG
    const byClub = {};
    for (const s of shots) { const name = s.clubUsed; if (!name || s.cat === "putt") continue; const b = byClub[name] = byClub[name] || { n: 0, totals: [], lats: [], sg: 0, right: 0, left: 0, nLat: 0 }; b.n++; b.sg += s.sg_exec; if (s.total != null) b.totals.push(s.total); if (s.offLat != null) { b.lats.push(s.offLat); b.nLat++; if (s.offLat > 5) b.right++; if (s.offLat < -5) b.left++; } }
    p.clubs = Object.keys(byClub).map(name => { const b = byClub[name]; return { club: name, n: b.n, sg: round2(b.sg), sgPer: round2(b.sg / b.n), medTotal: Math.round(median(b.totals) || 0), latSigma: round2(mad(b.lats)), medLat: round2(median(b.lats)), right: b.right, left: b.left, nLat: b.nLat }; }).sort((a, b) => b.n - a.n);
    // putting
    const putts = shots.filter(s => s.cat === "putt"); p.putting = { n: putts.length, sg: round2(putts.reduce((a, s) => a + s.sg_exec, 0)), firstPuttMedFt: Math.round(median(putts.filter(s => s.putts != null || s.next_rFt != null).map(s => s.rFt)) || 0), threePutts: putts.filter(s => s.putts != null && s.putts >= 3).length };
    // distance bands for approaches (execution per shot)
    const bands = [[50, 100, "50–100"], [100, 150, "100–150"], [150, 200, "150–200"], [200, 400, "200+"]];
    p.bands = bands.map(([lo, hi, label]) => { const ss = shots.filter(s => (s.cat === "approach") && s.rYd >= lo && s.rYd < hi); return { label, n: ss.length, sg: round2(ss.reduce((a, s) => a + s.sg_exec, 0)), sgPer: round2(ss.length ? ss.reduce((a, s) => a + s.sg_exec, 0) / ss.length : null), onGreen: share(ss, s => s.resultLie === L.GREEN) }; });
    return p;
  }

  // ---------- the review: every sentence carries the numbers it was made from; thin evidence says so ----------
  function conf(n) { return n >= 10 ? "solid" : n >= 4 ? "some" : n >= 1 ? "thin" : "none"; }
  function fmt(x, d = 2) { return x == null || isNaN(x) ? "–" : (x > 0 ? "+" : "") + (+x).toFixed(d); }
  function whereTo(s) {
    if (s.E_next === 0) return s.onGreen ? `holed in ${s.putts} putt${s.putts === 1 ? "" : "s"}` : `${s.strokes} stroke${s.strokes === 1 ? "" : "s"} from there to the cup`;
    if (s.nextPen) return `a penalty — dropped at ${s.nextR} yd in the ${lieWord(s.nextLie)}`;
    if (s.nextLie === L.GREEN) return `to ${s.nextFt} ft`;
    if (s.nextLie != null) return `to ${s.nextR} yd in the ${lieWord(s.nextLie)}`;
    return "to the next position";
  }
  function shotText(s, hole) { const where = s.i === 0 ? "the tee" : `${s.rYd} yd${s.onGreen ? " (" + s.rFt + " ft)" : ""}, ${s.playedFromHazard ? lieWord(s.gridLie) + " (played)" : lieWord(s.lie)}`; const club = s.clubUsed && !s.onGreen ? ` with ${s.clubUsed}${s.club ? "" : s.clubInferred ? " (inferred)" : ""}` : ""; return `Hole ${hole}, shot ${s.i + 1} from ${where}${club}, ${whereTo(s)}: ${fmt(s.sg)} (expected ${s.E.toFixed(2)} from there${s.E_next ? `, ${s.E_next.toFixed(2)} from the next spot` : ""}).`; }
  function review(res, history) {
    const R = { sections: [] }; const shots = allShots(res); const p = res.patterns; const add = (key, title, lines, n, evidence) => R.sections.push({ key, title, lines, n, confidence: conf(n), evidence: evidence || [] });
    if (!res.nScored) { add("empty", "Nothing to review yet", ["Mark your shots and enter each hole's score; the review is built only from those numbers."], 0); return R; }
    const complete = res.nComplete;
    const catRows = CATS.map(cc => ({ cc, sg: res.cats[cc].sg || 0, n: res.cats[cc].n || 0 })).filter(x => x.n);
    const decRow = { cc: "decision", sg: res.cats.decision.sg || 0, n: res.cats.decision.n || 0 };
    const good = catRows.filter(x => x.sg >= 0.3).sort((a, b) => b.sg - a.sg), bad = catRows.filter(x => x.sg <= -0.3).sort((a, b) => a.sg - b.sg);
    const scored = shots.filter(s => s.sg != null).sort((a, b) => b.sg - a.sg);
    // 1 what went well
    { const lines = []; for (const g of good) lines.push(`${CAT_LABEL[g.cc]}: ${fmt(g.sg)} strokes against the engine over ${g.n} shot${g.n === 1 ? "" : "s"}.`); for (const s of scored.slice(0, 2)) if (s.sg > 0.3) lines.push(shotText(s, s.hole)); if (!lines.length) lines.push(complete ? "No category or shot beat the engine's expectation by 0.3 or more." : "Not enough completed holes to say."); add("well", "What went well", lines, scored.length); }
    // 2 what cost strokes
    { const lines = []; for (const b of bad) lines.push(`${CAT_LABEL[b.cc]}: ${fmt(b.sg)} over ${b.n} shot${b.n === 1 ? "" : "s"} (${fmt(b.sg / b.n)} a shot).`); if (decRow.n && decRow.sg <= -0.15) lines.push(`Decisions the engine priced differently cost ${fmt(decRow.sg)} over ${decRow.n} choice${decRow.n === 1 ? "" : "s"}.`); for (const s of scored.slice(-3).reverse()) if (s.sg < -0.5) lines.push(shotText(s, s.hole)); if (!lines.length) lines.push(complete ? "No category lost 0.3 or more to the engine." : "Not enough completed holes to say."); add("cost", "What cost you strokes", lines, scored.length); }
    // 3 biggest pattern
    { const cands = []; const a = p.approach;
      if (a.n >= 4) { for (const [key, label] of [["right", "right of the target"], ["left", "left of the target"], ["short", "short of the pin"], ["long", "long of the pin"]]) if (a[key].p >= 0.6) cands.push({ score: a[key].p * a.n, text: `${a[key].k} of ${a.n} approach shots finished ${label} (median ${key === "right" || key === "left" ? Math.abs(a.medLat) + " yd " + (a.medLat > 0 ? "right" : "left") : Math.abs(a.medDepth) + " yd " + (a.medDepth < 0 ? "short" : "long")}).`, n: a.n }); }
      const t = p.tee; if (t.n >= 4) { if (t.trouble.p >= 0.3) cands.push({ score: t.trouble.p * t.n, text: `${t.trouble.k} of ${t.n} tee shots found sand, water or desert; the engine's picks expected far fewer.`, n: t.n }); for (const [key, label] of [["right", "right"], ["left", "left"]]) if (t[key].p >= 0.6) cands.push({ score: t[key].p * t.n, text: `${t[key].k} of ${t.n} tee shots finished ${label} of the fairway's line by more than 10 yd (median ${Math.abs(t.medLat)} yd ${t.medLat > 0 ? "right" : "left"}).`, n: t.n }); }
      const d = p.decisions; if (d.teeN >= 4 && d.teeFollowed / d.teeN <= 0.6 && d.teeCost <= -0.3) cands.push({ score: -d.teeCost * 4, text: `You took the engine's tee club on ${d.teeFollowed} of ${d.teeN} holes; the other ${d.teeN - d.teeFollowed} choices cost ${fmt(d.teeCost)} together.`, n: d.teeN });
      if (d.golayN >= 2 && d.golayCost <= -0.4) cands.push({ score: -d.golayCost * 4, text: `Go-or-lay-up calls that went against the engine cost ${fmt(d.golayCost)} over ${d.golayN} shots.`, n: d.golayN });
      const pt = p.putting; if (pt.n >= 6 && pt.threePutts >= 2) cands.push({ score: pt.threePutts * 2, text: `${pt.threePutts} three-putts in ${pt.n} marked first putts (putting ${fmt(pt.sg)} against the green curve).`, n: pt.n });
      cands.sort((x, y) => y.score - x.score);
      add("pattern", "Biggest pattern", cands.length ? [cands[0].text].concat(cands.slice(1, 3).map(x => "Also: " + x.text)) : [`No pattern clears the bar yet (${a.n} approach shots, ${t.n} tee shots with a known result; a pattern needs 4 and a 60% share).`], Math.max(a.n, t.n)); }
    // 4 most important mistake
    { const worst = scored.length ? scored[scored.length - 1] : null; add("mistake", "Most important mistake", worst && worst.sg < -0.3 ? [shotText(worst, worst.hole)] : ["No single shot cost more than 0.3 against the engine."], worst ? 1 : 0); }
    // 5/6 best and worst decision
    { const dec = shots.filter(s => s.sg_dec != null && s.alt); const worst = dec.slice().sort((a, b) => a.sg_dec - b.sg_dec)[0];
      const followed = shots.filter(s => s.sg_dec != null && s.sg_dec > -0.01 && s.alt && s.alt.E != null && s.E_intent != null).map(s => Object.assign({ gain: s.alt.E - s.E_intent }, s)).sort((a, b) => b.gain - a.gain)[0];
      add("bestdec", "Best decision", followed && followed.gain > 0.1 ? [`Hole ${followed.hole}, shot ${followed.i + 1}: you ${followed.cat === "tee" ? "hit " + followed.clubUsed : followed.intent === "go" ? "went for the green" : "laid up"}, the engine's call; ${followed.alt.what} was priced ${fmt(followed.gain)} worse.`] : ["No choice where the alternative was clearly worse (by 0.1) is on record."], followed ? 1 : 0);
      add("worstdec", "Worst decision", worst && worst.sg_dec < -0.1 ? [`Hole ${worst.hole}, shot ${worst.i + 1}: you ${worst.cat === "tee" ? "hit " + worst.clubUsed : worst.intent === "go" ? "went for the green" : "laid up"} from ${worst.i === 0 ? "the tee" : worst.rYd + " yd"}; the engine priced ${worst.alt.what} ${fmt(-worst.sg_dec)} better (${worst.E_intent.toFixed(2)} vs ${worst.alt.E.toFixed(2)}).${worst.sg_exec != null ? " The shot itself then went " + fmt(worst.sg_exec) + " against that choice's expectation." : ""}`] : ["No decision cost more than 0.1 against the engine's pricing."], worst ? 1 : 0); }
    // 7 club pattern
    { const rows = p.clubs.filter(x => x.n >= 3 && x.club !== "partial wedge").sort((a, b) => a.sgPer - b.sgPer); const lines = rows.slice(0, 3).map(x => `${x.club}: ${fmt(x.sg)} over ${x.n} shots (${fmt(x.sgPer)} each)${x.nLat >= 3 ? `, ${x.right} right / ${x.left} left of the line` : ""}${x.medTotal ? `, median ${x.medTotal} yd` : ""}.`); add("club", "Club pattern", lines.length ? lines : ["No club has three full shots with a known result yet (partial wedges are not a club)."], rows.length ? rows[0].n : 0); }
    // 8 miss pattern
    { const a = p.approach, t = p.tee; const lines = []; if (a.n) lines.push(`Approaches (${a.n}): ${a.onGreen.k} on the green; ${a.right.k} right, ${a.left.k} left (beyond 5 yd); ${a.short.k} short, ${a.long.k} long (beyond 8 yd); median ${fmt(a.medLat, 0)} yd lateral, ${fmt(a.medDepth, 0)} yd deep.`); if (t.n) lines.push(`Tee shots (${t.n}): ${t.fairway.k} fairways, ${t.trouble.k} in trouble; median ${fmt(t.medLat, 0)} yd from the fairway's line, ${t.medTotal} yd total.`); if (!lines.length) lines.push("No shots with a known result yet."); add("miss", "Miss pattern", lines, a.n + t.n); }
    // 9 practice priority — the category/band with the largest total loss, stated as a target to practise to, never a swing diagnosis
    { const cands = p.bands.filter(b => b.n >= 3 && b.sg < 0).map(b => ({ text: `Approach shots from ${b.label}: ${fmt(b.sg)} over ${b.n} (${fmt(b.sgPer)} each; ${b.onGreen.k} of ${b.n} on the green). Loop sees where the ball finished, not the swing — practise to a target and log where each one lands.`, loss: b.sg, n: b.n }));
      if (p.putting.n >= 4 && p.putting.sg < -0.5) cands.push({ text: `Putting: ${fmt(p.putting.sg)} over ${p.putting.n} marked first putts (median first putt ${p.putting.firstPuttMedFt} ft; ${p.putting.threePutts} three-putts).`, loss: p.putting.sg, n: p.putting.n });
      const sh = res.cats.short; if (sh.n >= 3 && sh.sg < -0.5) cands.push({ text: `Short game inside 50 yd: ${fmt(sh.sg)} over ${sh.n} shots.`, loss: sh.sg, n: sh.n });
      cands.sort((x, y) => x.loss - y.loss);
      add("practice", "Practice priority", cands.length ? [cands[0].text] : ["Nothing stands out enough to prescribe; log another round."], cands.length ? cands[0].n : 0); }
    // 10 next-round plan — the holes where the choice was priced against you
    { const dec = shots.filter(s => s.sg_dec != null && s.sg_dec <= -0.1).sort((a, b) => a.sg_dec - b.sg_dec).slice(0, 4); const lines = dec.map(s => `Hole ${s.hole}: ${s.cat === "tee" ? `take ${s.engineClub} off the tee (you hit ${s.clubUsed}; ${fmt(-s.sg_dec)})` : s.intent === "go" ? `lay up to ${s.layLeave} from ${s.rYd} (${fmt(-s.sg_dec)})` : `go for the green from ${s.rYd} (${fmt(-s.sg_dec)})`}.`); if (!lines.length) lines.push(complete ? "Your choices matched the engine's pricing within 0.1 everywhere it had a say; play the same lines." : "Not enough completed holes to plan from."); add("next", "Next-round plan", lines, dec.length); }
    // 11 memory: the same miss as before?
    { const a = p.approach; const lines = []; if (a.n >= 5) for (const hprev of history) { if (!hprev || hprev.id === res.id || !hprev.patterns) continue; const b = hprev.patterns.approach; if (!b || b.n < 5) continue; for (const key of ["right", "left", "short", "long"]) if (a[key].p >= 0.6 && b[key].p >= 0.6) lines.push(`This looks like ${hprev.date} at ${hprev.courseName}: ${b[key].k} of ${b.n} approaches finished ${key} that day too.`); } if (lines.length) add("memory", "Seen before", lines.slice(0, 2), a.n); }
    return R;
  }

  // ---------- the player model across rounds (real rounds only) ----------
  function playerModel(analyses) {
    const real = analyses.filter(a => a && !a.sample && a.nComplete > 0); const merged = { holes: {} }; let idx = 0;
    for (const a of real) for (const hn in a.holes) merged.holes[(idx++) + ":" + hn] = a.holes[hn];
    const p = real.length ? patterns(merged) : null;
    const trend = real.slice().sort((a, b) => (a.date || "").localeCompare(b.date || "")).map(a => ({ date: a.date, course: a.courseName, score: a.score, E: a.E_tee, sg: a.sgTotal, cats: Object.fromEntries(CATS.concat(["decision"]).map(cc => [cc, a.cats[cc].sg])) }));
    // measured clubs: enough shots to trust a carry (10) — offered, never applied silently
    const measured = p ? p.clubs.filter(x => x.n >= 10 && x.medTotal > 0 && x.club !== "partial wedge").map(x => ({ club: x.club, n: x.n, total: x.medTotal, latSigma: x.latSigma })) : [];
    return { rounds: real.length, holes: real.reduce((s, a) => s + a.nComplete, 0), shots: p ? allShots(merged).length : 0, patterns: p, trend, measured };
  }

  // ---------- a simulated round (benchmark data and the sample in the empty state; never stored as yours) ----------
  function simulateRound(courseKey, P0, seed, opts) {
    const c = D.courses.find(x => x.key === courseKey); const P = Object.assign({}, D.defaults, P0 || {}); const altf = 1 + P.alt_rule / 100 * (c.alt_ft - P.home_ft) / 1000;
    let a = (seed || 1) >>> 0; const rand = () => { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };
    const pick = arr => arr[Math.floor(rand() * arr.length)];
    const round = { id: "sim_" + courseKey + "_" + (seed || 1), course: courseKey, date: (opts && opts.date) || new Date().toISOString().slice(0, 10), started: new Date().toISOString(), tees: c.tees, P: { wind_mph: P.wind_mph, wind_from: P.wind_from, temp_f: P.temp_f, setting: P.setting, pin: P.pin }, sample: true, name: "Sample round — simulated by the engine, not your golf", holes: {} };
    const gr = E.lut(P.baseline, "green_ft");
    for (const h of c.holes) {
      if (h.nodata || !h.grid || (h.src.fairway === "none" && h.par !== 3)) continue;
      const H = E.decodeHole(h); E.applyPin(H, P); const shots = [{ x: 0, y: 0, src: "sim" }]; let pos = [0, 0]; let pen = 0; let holed = false; let putts = 0; let guard = 0;
      // tee shot: the engine's pick, except every third hole where a plan club exists and differs (a decision to price)
      if (h.par !== 3) { const r = E.runHole(c, h, P, { n: 800 }); let club = r.pick.club; if (h.plan && h.plan.club && h.plan.club !== club && h.hole % 3 === 0) club = h.plan.club; const o = r.options.find(x => x.club === club) || E.teeOptions(h, P, altf, { n: 800, keep: 120, clubs: [club] })[0]; const s = pick(o.best.sample); pos = [s[0], s[1]]; }
      else { const ap = E.approach(h, [0, 0], P, altf, { n: 600, keep: 120 }); if (!ap.best) continue; const s = pick(ap.best.sample); pos = [s[0], s[1]]; }
      while (!holed && guard++ < 10) {
        // penalty: the ball is in water or desert → drop back toward where it came from, one stroke
        let lie = E.lieAt(H, pos[0], pos[1]); const prev = shots[shots.length - 1]; let penHere = 0;
        if (lie === L.WATER || lie === L.DESERT) { const px = prev.x, py = prev.y; for (let step = 5; step <= 80; step += 5) { const t = step / Math.hypot(pos[0] - px, pos[1] - py); if (t >= 1) break; const q = [pos[0] + (px - pos[0]) * t, pos[1] + (py - pos[1]) * t]; const ql = E.lieAt(H, q[0], q[1]); if (ql !== L.WATER && ql !== L.DESERT) { pos = q; lie = ql; break; } } penHere = 1; pen++; }
        shots.push({ x: Math.round(pos[0] * 10) / 10, y: Math.round(pos[1] * 10) / 10, src: "sim", pen: penHere });
        const rYd = distYd(pos, H.pin);
        if (lie === L.GREEN) { const exp = E.baseAt(gr, rYd * 3); putts = Math.max(1, Math.floor(exp) + (rand() < exp - Math.floor(exp) ? 1 : 0)); holed = true; break; }
        if (rYd <= 50) {
          // a chip or pitch: the engine prices these from the curve, not from a landing model, so the sample does too — on the green
          // most of the time, at a distance that grows with the shot; otherwise just off it in the rough
          const onP = lie === L.FAIRWAY ? 0.85 : lie === L.SAND ? 0.65 : 0.72; const dir = [(H.pin[0] - pos[0]) / (rYd * YD), (H.pin[1] - pos[1]) / (rYd * YD)];
          if (rand() < onP) { const ft = Math.max(1, rYd * 0.3 * (0.5 + rand())); const ang = rand() * 2 * Math.PI; pos = [H.pin[0] + Math.cos(ang) * ft / 3 * YD, H.pin[1] + Math.sin(ang) * ft / 3 * YD]; if (E.lieAt(H, pos[0], pos[1]) !== L.GREEN) pos = [H.pin[0] + dir[0] * ft / 3 * YD * 0.5, H.pin[1] + dir[1] * ft / 3 * YD * 0.5]; }
          else { const over = 4 + rand() * 6, sgn = rand() < 0.5 ? 1 : -1; pos = [H.pin[0] + dir[0] * over * YD * sgn, H.pin[1] + dir[1] * over * YD * sgn]; }
          continue;
        }
        let ap; const gl = rYd >= 160 && h.par >= 4 ? E.goVsLay(h, pos, P, altf, { n: 500, keep: 0 }) : null;
        if (gl && gl.lay && (!gl.go.best || (gl.delta != null && gl.delta < 0 && rand() < 0.8) || rand() < 0.25)) { const cl = E.clubForDistance(Math.max(60, rYd - gl.lay.leave), P, altf, false); ap = E.approach(h, pos, P, altf, { n: 600, keep: 120, club: cl.name.replace("easy ", "") }); }
        else ap = E.approach(h, pos, P, altf, { n: 600, keep: 120 });
        if (!ap || !ap.best || !ap.best.sample) { holed = true; putts = 2; break; }
        const s = pick(ap.best.sample); pos = [s[0], s[1]];
      }
      round.holes[h.hole] = { shots, score: shots.length + pen + Math.max(0, putts - 1), putts };
    }
    return round;
  }

  window.LoopLedger = { analyzeHole, analyzeRound, assemble, roundParams, holesToAnalyze, patterns, review, playerModel, simulateRound, inferClub, offsets, shotText, whereTo, CATS, CAT_LABEL, lieWord, allShots };
})();

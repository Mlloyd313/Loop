/* Loop engine — JavaScript port of pipeline/engine.py (same model, same conventions).
   Frame: metres, +x toward the pin, +y right. Yards in the API. */
(function () {
  const YD = 0.9144;
  const L = { DESERT: 0, FAIRWAY: 1, ROUGH: 2, GREEN: 3, SAND: 4, WATER: 5, OGREEN: 6, WASTE: 7, SCRUB: 8, TEE: 9, OB: 10 };   // OB: out of bounds (session P) — stroke and distance
  const D = window.LOOP_DATA;
  if (D.defaults.oob == null) D.defaults.oob = false;   // out of bounds priced (session P): off by default
  if (D.defaults.pin_lat == null) D.defaults.pin_lat = 0;   // the tucked pin (session L): data.js built before it carries the default from its next rebuild
  if (D.defaults.desert_play == null) Object.assign(D.defaults, { desert_play: 0.6, desert_unplayable: 0.25, desert_lost: 0.15, desert_drop_extra: 0.4 });   // the desert by the Rules (session L, D-L11)
  // from-lie effects on the next shot: dispersion multiplier, carry factor, penalty strokes before the shot
  // (desert's pen is the lie's extra for a ball you are playing from the desert — found, playable, the same as scrub; the penalty cases live in
  // price(): the desert shares — session L, on Michael's word that the desert is general area everywhere, D-L11)
  const LIEFX = { 0: { disp: 1.3, carry: 0.96, pen: 0.4 }, 1: { disp: 1, carry: 1, pen: 0 }, 2: { disp: 1.3, carry: 0.96, pen: 0 }, 3: { disp: 1, carry: 1, pen: 0 }, 4: { disp: 1.6, carry: 0.92, pen: 0 },
                  5: { disp: 1.3, carry: 0.96, pen: 1 }, 6: { disp: 1.3, carry: 0.96, pen: 0 }, 7: { disp: 1.6, carry: 0.92, pen: 0 }, 8: { disp: 1.3, carry: 0.96, pen: 0.4 }, 9: { disp: 1, carry: 1, pen: 0 },
                  10: { disp: 1.3, carry: 0.96, pen: 0.4 } };   // OB: a ball someone plays from a spot the map calls out of bounds is in bounds there — a found desert ball

  // ---------- RNG (deterministic per run) ----------
  function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
  function gaussPair(rand) { let u = 0, v = 0; while (u === 0) u = rand(); v = rand(); const r = Math.sqrt(-2 * Math.log(u)); return [r * Math.cos(2 * Math.PI * v), r * Math.sin(2 * Math.PI * v)]; }

  // ---------- baselines as 1-yd lookup tables ----------
  const LUT = {};
  function lut(baseName, lie) {
    const key = baseName + "/" + lie; if (LUT[key]) return LUT[key];
    const pts = D.bases[baseName][lie]; const max = lie === "green_ft" ? 120 : 560; const t = new Float32Array(max + 1);
    for (let x = 0; x <= max; x++) t[x] = interp(pts, x);
    return LUT[key] = t;
  }
  function interp(pts, x) { if (x <= pts[0][0]) return pts[0][1]; for (let i = 1; i < pts.length; i++) { if (x <= pts[i][0]) { const [x0, y0] = pts[i - 1], [x1, y1] = pts[i]; return y0 + (y1 - y0) * (x - x0) / (x1 - x0); } } return pts[pts.length - 1][1]; }
  function baseAt(t, x) { const i = x < 0 ? 0 : x >= t.length - 1 ? t.length - 1 : x; const i0 = Math.floor(i); const f = i - i0; return i0 + 1 < t.length ? t[i0] * (1 - f) + t[i0 + 1] * f : t[i0]; }

  // ---------- corrections (the user moves a hole's green) ----------
  // overrides[courseKey:hole] = { pin: [x, y] (frame metres), poly: index into h.polys.greens or null }
  let OVERRIDES = {};
  function setOverrides(o) { OVERRIDES = o || {}; for (const c of D.courses) for (const h of c.holes) delete h._dec; }
  function overrideFor(h) { return OVERRIDES[h._key] || null; }
  function pointInPoly(x, y, poly) { let inside = false; for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) { const xi = poly[i][0], yi = poly[i][1], xj = poly[j][0], yj = poly[j][1]; if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / ((yj - yi) || 1e-9) + xi) inside = !inside; } return inside; }

  // ---------- hole decoding ----------
  function decodeHole(h) {
    if (h._dec) return h._dec;
    const g = h.grid; const lie = new Uint8Array(g.nx * g.ny); let p = 0;
    for (const run of g.rle.split(",")) { if (!run) continue; const v = parseInt(run[0], 36); const n = parseInt(run.slice(1), 16); lie.fill(v, p, p + n); p += n; }
    const e = h.elev; const raw = atob(e.b64); const z = new Float32Array(e.nx * e.ny);
    for (let i = 0; i < z.length; i++) z[i] = e.lo + raw.charCodeAt(i) * e.scale;
    let depth = 25 * YD; if (h.polys.own_green) { let mn = 1e9, mx = -1e9; for (const [x] of h.polys.own_green) { if (x < mn) mn = x; if (x > mx) mx = x; } depth = mx - mn; }
    const ln = h.line; let a = ln[ln.length - 2], b = ln[ln.length - 1];
    let basePin = h.pin.slice(), pinFt = h.pin_ft, overridden = false;
    const ov = overrideFor(h);
    if (ov && ov.pin) {
      // the old green becomes another hole's green (if it was a mapped one) or plain rough; the chosen polygon (or a 12-yd disc) becomes the green
      const oldTo = h.src && h.src.green === "osm" ? L.OGREEN : L.ROUGH;
      for (let i = 0; i < lie.length; i++) if (lie[i] === L.GREEN) lie[i] = oldTo;
      const poly = ov.poly != null && h.polys.greens[ov.poly] ? h.polys.greens[ov.poly] : null;
      for (let iy = 0; iy < g.ny; iy++) for (let ix = 0; ix < g.nx; ix++) {
        const x = h.frame.x0 + (ix + 0.5) * g.cell, y = -h.frame.w + (iy + 0.5) * g.cell;
        const on = poly ? pointInPoly(x, y, poly) : Math.hypot(x - ov.pin[0], y - ov.pin[1]) < 12 * YD;
        if (on) lie[iy * g.nx + ix] = L.GREEN;
      }
      basePin = ov.pin.slice(); overridden = true;
      if (poly) { let mn = 1e9, mx = -1e9; for (const [x] of poly) { if (x < mn) mn = x; if (x > mx) mx = x; } depth = mx - mn; } else depth = 25 * YD;
      if (ln.length <= 2) { a = ln[0]; b = basePin; }
    }
    const dl = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1;
    const H = { lie, z, nx: g.nx, ny: g.ny, cell: g.cell, enx: e.nx, eny: e.ny, ecell: e.cell, x0: h.frame.x0, w: h.frame.w, basePin, pin: basePin.slice(), dir: [(b[0] - a[0]) / dl, (b[1] - a[1]) / dl], pinFt, teeFt: h.tee_ft, depth, overridden, cardPA: h.desert_rule === "penalty_area", desertPA: h.desert_rule === "penalty_area" };   // the club's card's desert rule (session P); desertPA as priced (applyPin)
    if (overridden) { H.pinFt = zAt(H, basePin[0], basePin[1]); H.basePinFt = H.pinFt; }
    return h._dec = H;
  }
  // pin position: front / middle / back = a third of the green's depth along the last segment of the hole line; pin_lat = yards beside
  // that line (+ right, − left, as seen from the fairway; 0 = on the line), the tucked pin (session L). The pin's elevation is the data's
  // at the base pin and the DEM's wherever the pin is moved (mirrors engine.py apply_pin).
  function applyPin(H, P) {
    H.oob = !!P.oob;   // out of bounds priced (session P: a setting, off by default — P-E1b)
    H.desertPA = !!H.cardPA && P.desert_by !== "rules";   // the card's desert rule unless asked to price the Rules instead (the rules block's comparison)
    if (H.basePinFt == null) H.basePinFt = H.pinFt;
    const s = P.pin === "front" ? -1 : P.pin === "back" ? 1 : 0; const d = s * H.depth / 3; const lat = (+P.pin_lat || 0) * YD;
    H.pin[0] = H.basePin[0] + H.dir[0] * d - H.dir[1] * lat; H.pin[1] = H.basePin[1] + H.dir[1] * d + H.dir[0] * lat;
    H.pinFt = (d === 0 && lat === 0) ? H.basePinFt : zAt(H, H.pin[0], H.pin[1]);
  }
  // out of bounds is stored over the cell's own lie (10–19, session P): priced as out of bounds only when the player turns it on (P.oob, set by applyPin)
  function lieAt(H, x, y) { const ix = ((x - H.x0) / H.cell) | 0, iy = ((y + H.w) / H.cell) | 0; if (ix < 0 || ix >= H.nx || iy < 0 || iy >= H.ny) return L.DESERT; const v = H.lie[iy * H.nx + ix]; return v < L.OB ? v : H.oob ? L.OB : v - L.OB; }
  function zAt(H, x, y) {
    let fx = (x - H.x0) / H.ecell - 0.5, fy = (y + H.w) / H.ecell - 0.5;
    let ix = Math.floor(fx), iy = Math.floor(fy); if (ix < 0) ix = 0; if (ix > H.enx - 2) ix = H.enx - 2; if (iy < 0) iy = 0; if (iy > H.eny - 2) iy = H.eny - 2;
    let tx = fx - ix, ty = fy - iy; if (tx < 0) tx = 0; if (tx > 1) tx = 1; if (ty < 0) ty = 0; if (ty > 1) ty = 1;
    const z = H.z, i = iy * H.enx + ix;
    return z[i] * (1 - tx) * (1 - ty) + z[i + 1] * tx * (1 - ty) + z[i + H.enx] * (1 - tx) * ty + z[i + H.enx + 1] * tx * ty;
  }

  // ---------- clubs ----------
  function clubParams(name, P, altf) {
    const c = D.clubs.find(c => c.name === name) || (P.clubsOverride || []).find(c => c.name === name);
    const over = (P.clubsOverride || []).find(c => c.name === name);
    const carry0 = over ? over.carry : c.carry; const rf = over && over.roll_firm != null ? over.roll_firm : c.roll_firm; const rs = over && over.roll_soft != null ? over.roll_soft : c.roll_soft;
    const carry = carry0 * altf * (1 + P.temp_pct_per_10f / 100 * (P.temp_f - 70) / 10);
    return { name, carry, roll: P.setting === "firm" ? rf : rs, latPct: over && over.lat_pct != null ? over.lat_pct : P.lat_pct, distPct: over && over.dist_pct != null ? over.dist_pct : P.dist_pct };
  }
  function clubForDistance(totalYd, P, altf, tee) {
    const rows = [];
    for (const c of D.clubs) { if (c.name === "Driver" && !tee) continue; const cp = clubParams(c.name, P, altf); rows.push([cp.carry + cp.roll, cp]); }
    rows.sort((a, b) => a[0] - b[0]);
    if (totalYd >= rows[rows.length - 1][0]) { const r = Object.assign({}, rows[rows.length - 1][1]); r.shortBy = totalYd - rows[rows.length - 1][0]; return r; }
    if (totalYd <= rows[0][0]) { const k = totalYd / rows[0][0], r = rows[0][1]; return Object.assign({}, r, { name: "easy " + r.name, carry: r.carry * k, roll: r.roll * k }); }
    for (let i = 1; i < rows.length; i++) if (rows[i][0] >= totalYd) {
      const a = rows[i - 1], b = rows[i], t = (totalYd - a[0]) / (b[0] - a[0]);
      return Object.assign({}, t > 0.5 ? b[1] : a[1], { carry: a[1].carry + t * (b[1].carry - a[1].carry), roll: a[1].roll + t * (b[1].roll - a[1].roll) });
    }
  }
  function descentK(P, name, yds) {
    const A = P.angles; let a;
    if (name) a = name === "Driver" ? A.driver : (name === "3-wood" || name === "Hybrid") ? A.wood : (/[45]/.test(name)) ? A.long : A.mid;
    else a = yds > 235 ? A.wood : yds > 195 ? A.long : yds > 150 ? A.mid : A.wedge;
    return 1 / Math.tan(a * Math.PI / 180);
  }
  function windComponents(P, compass) { if (!(P.wind_mph > 0)) return [0, 0]; const rel = (P.wind_from - compass) * Math.PI / 180; return [P.wind_mph * Math.cos(rel), P.wind_mph * Math.sin(rel)]; }

  // ---------- one shot batch ----------
  // Returns typed arrays px, py (metres) for n shots from ball toward aimDeg with the club.
  function shoot(H, ball, aimDeg, club, n, rand, P, bearing, out, fromLieGiven) {
    const a = aimDeg * Math.PI / 180, dx = Math.cos(a), dy = Math.sin(a), nx = -Math.sin(a), ny = Math.cos(a);
    const [head, cross] = windComponents(P, (bearing || 0) + aimDeg);
    const wf = head > 0 ? 1 - P.head_pct_per_mph / 100 * head : 1 + P.tail_pct_per_mph / 100 * (-head);
    const carryW = club.carry * wf, drift = -P.cross_yd_per_mph * cross * Math.pow(club.carry / 300, 2);
    // lie you are playing from: rough and sand widen the pattern and cost carry (fairway, tee and green are neutral).
    // The ledger passes the lie it recorded (or the player corrected) as fromLieGiven; otherwise the grid decides.
    const fromTee = ball[0] === 0 && ball[1] === 0; const fromLie = fromLieGiven != null ? fromLieGiven : fromTee ? L.TEE : lieAt(H, ball[0], ball[1]); const lf = LIEFX[fromLie] || LIEFX[1];
    const sLat = Math.max(2.5, club.carry * club.latPct * P.disp * lf.disp), sDist = Math.max(2.0, club.carry * club.distPct * P.disp * lf.disp);
    const k = descentK(P, club.name.replace("easy ", ""), club.carry + club.roll);
    const bias = (P.lat_bias || 0) * club.carry;   // yards, + = right: a day's (or a player's) offset of the whole pattern (Omega G)
    const z0 = zAt(H, ball[0], ball[1]);
    const px = out.px, py = out.py;
    for (let i = 0; i < n; i++) {
      const good = rand() > P.q_miss; const [g1, g2] = gaussPair(rand);
      let z = g1 > 0 ? g1 * (1 + P.skew_right) : g1;
      const lat = (good ? z * sLat : z * sLat * P.miss_lat_mult) + drift + bias;
      let dist = (good ? carryW + g2 * sDist : carryW - P.miss_short_pct * club.carry + g2 * sDist * P.miss_dist_mult) * lf.carry;
      let x = ball[0] + dx * dist * YD + nx * lat * YD, y = ball[1] + dy * dist * YD + ny * lat * YD;
      for (let it = 0; it < 2; it++) { const zl = zAt(H, x, y); const tot = dist + k * (z0 - zl) / 3; x = ball[0] + dx * tot * YD + nx * lat * YD; y = ball[1] + dy * tot * YD + ny * lat * YD; if (it === 1) dist = tot; }
      px[i] = x + dx * club.roll * YD; py[i] = y + dy * club.roll * YD;
    }
  }
  // The three outcomes of a desert ball as shares that sum to 1: played as it lies, unplayable (a stroke and a drop), lost (stroke and distance).
  function desertShares(P) {
    const a = Math.max(0, +(P.desert_play != null ? P.desert_play : 1)), b = Math.max(0, +(P.desert_unplayable || 0)), c = Math.max(0, +(P.desert_lost || 0)); const t = a + b + c;
    return t <= 0 ? [1, 0, 0] : [a / t, b / t, c / t];
  }
  // Price n landings: returns mean strokes-to-hole-out (incl. penalties), odds, remaining/plays medians. extra = the lie you play from (its
  // strokes, inside the expectation). A desert landing is the Rules' three outcomes by their shares: played (rough + scrub_extra), unplayable
  // (1 + rough + desert_drop_extra), lost (1 + the same shot again — stroke and distance — solved as a fixed point: E = (1 + mean s + extra) / (1 − mean w)).
  function price(H, px, py, n, P, base, keep, extra) {
    const fw = lut(base, "fairway"), rg = lut(base, "rough"), sd = lut(base, "sand"), gr = lut(base, "green_ft");
    const kW = descentK(P, null, 250), kL = descentK(P, null, 200), kM = descentK(P, null, 170), kWe = descentK(P, null, 100);
    const [dp, du, dl] = desertShares(P); const dPlay = P.scrub_extra, dDrop = P.desert_drop_extra != null ? P.desert_drop_extra : P.scrub_extra;
    let sum = 0, wsum = 0; const cnt = new Float64Array(11); const rem = new Float32Array(n), plays = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const x = px[i], y = py[i]; const lie = lieAt(H, x, y); cnt[lie]++;
      const r = Math.hypot(x - H.pin[0], y - H.pin[1]) / YD; const dz = H.pinFt - zAt(H, x, y);
      const k = r > 235 ? kW : r > 195 ? kL : r > 150 ? kM : kWe; let pl = r + k * dz / 3; if (pl < 5) pl = 5;
      rem[i] = r; plays[i] = pl; let s;
      switch (lie) {
        case L.GREEN: s = baseAt(gr, r * 3); break;
        case L.FAIRWAY: case L.TEE: s = baseAt(fw, pl); break;
        case L.ROUGH: case L.OGREEN: s = baseAt(rg, pl); break;
        case L.SAND: case L.WASTE: s = baseAt(sd, pl); break;
        case L.SCRUB: s = baseAt(rg, pl) + P.scrub_extra; break;
        case L.WATER: s = baseAt(rg, pl) + 1; break;
        case L.OB: s = 1; wsum += 1; break;   // out of bounds: stroke and distance — the penalty stroke here, the shot again in the fixed point below
        default: { const rd = baseAt(rg, pl);
          if (H.desertPA) s = dp * (rd + dPlay) + (du + dl) * (rd + 1);   // the club's card (session P): not played → a stroke and a drop at the grass line, no stroke and distance
          else { s = dp * (rd + dPlay) + du * (rd + dDrop) + du + dl; wsum += dl; } }
      }
      if (lie !== L.GREEN && lie !== L.OB && r < 50) s += P.short_game_extra || 0;   // his chips, pitches and bunker shots vs the scratch curve (no chip from out of bounds)
      sum += s;
    }
    const odds = { green: cnt[L.GREEN] / n, fairway: (cnt[L.FAIRWAY] + cnt[L.TEE]) / n, rough: (cnt[L.ROUGH] + cnt[L.OGREEN]) / n, sand: (cnt[L.SAND] + cnt[L.WASTE]) / n, water: cnt[L.WATER] / n, desert: (cnt[L.DESERT] + cnt[L.SCRUB]) / n, oob: cnt[L.OB] / n };
    const res = { E: (1 + sum / n + (extra || 0)) / (1 - Math.min(0.95, wsum / n)), odds, rem: median(rem), plays: median(plays) };
    if (keep) { res.sample = []; for (let i = 0; i < Math.min(n, keep); i++) res.sample.push([px[i], py[i], lieAt(H, px[i], py[i])]); }
    return res;
  }
  function median(a) { const b = Float32Array.from(a).sort(); return b[b.length >> 1]; }
  // The price of one position: the same rule price() applies to every simulated landing (baseline by lie and plays-like distance, plus the
  // penalty terms), so a hole's expectation, its price map and the ledger's chain all speak the same currency. lieGiven overrides the grid.
  function priceAt(h, pos, P, lieGiven) {
    const H = decodeHole(h); applyPin(H, P); const base = P.baseline;
    const lie = lieGiven != null ? lieGiven : (pos[0] === 0 && pos[1] === 0 ? L.TEE : lieAt(H, pos[0], pos[1]));
    const r = Math.hypot(pos[0] - H.pin[0], pos[1] - H.pin[1]) / YD; const dz = H.pinFt - zAt(H, pos[0], pos[1]);
    const k = descentK(P, null, r); let pl = r + k * dz / 3; if (pl < 5) pl = 5; let s;
    switch (lie) {
      case L.GREEN: s = baseAt(lut(base, "green_ft"), r * 3); break;
      case L.FAIRWAY: case L.TEE: s = baseAt(lut(base, "fairway"), pl); break;
      case L.ROUGH: case L.OGREEN: s = baseAt(lut(base, "rough"), pl); break;
      case L.SAND: case L.WASTE: s = baseAt(lut(base, "sand"), pl); break;
      case L.SCRUB: s = baseAt(lut(base, "rough"), pl) + P.scrub_extra; break;
      case L.WATER: s = baseAt(lut(base, "rough"), pl) + 1; break;
      default: s = baseAt(lut(base, "rough"), pl) + P.scrub_extra;   // DESERT (and OB: a ball played from there is in bounds whatever the map says): a found, playable ball (the lie's extra, no penalty)
    }
    if (lie !== L.GREEN && r < 50) s += P.short_game_extra || 0;
    return { E: s, r, plays: pl, dz, lie };
  }

  // ---------- tee options for a par 4/5 ----------
  function teeOptions(h, P, altf, opts) {
    const H = decodeHole(h); applyPin(H, P); const n = opts && opts.n || P.n; const keep = opts && opts.keep || 120; const base = P.baseline; const bearing = h.bearing || 0;
    const buf = { px: new Float32Array(n), py: new Float32Array(n) }; const out = [];
    const clubs = (opts && opts.clubs) || D.tee_clubs;
    // scan around the fairway's own direction (first segment of the hole line), not the tee→pin line: doglegs need it
    const seg = h.line.length > 2 ? h.line[1] : H.basePin; let aim0 = Math.round(Math.atan2(seg[1], seg[0]) * 180 / Math.PI / P.aim_step) * P.aim_step; if (Math.abs(aim0) < P.aim_step) aim0 = 0;
    for (const name of clubs) {
      const club = clubParams(name, P, altf); const curve = []; let best = null;
      const aims = opts && opts.aims ? opts.aims : null;   // simulation tooling: play given aims only (the model is unchanged)
      for (let aim = aims ? aims[0] : aim0 + P.aim_min, ai = 0; aims ? ai < aims.length : aim <= aim0 + P.aim_max; aims ? (aim = aims[++ai]) : (aim += P.aim_step)) {
        const rand = mulberry32(P.seed * 1000 + 7); // common random numbers across aims and clubs
        shoot(H, [0, 0], aim, club, n, rand, P, bearing, buf);
        const r = price(H, buf.px, buf.py, n, P, base, 0); r.aim = aim; curve.push(r);
        if (!best || r.E < best.E) best = r;
      }
      // keep the landing sample of the best aim
      const rand = mulberry32(P.seed * 1000 + 7); shoot(H, [0, 0], best.aim, club, n, rand, P, bearing, buf); best = Object.assign(price(H, buf.px, buf.py, n, P, base, keep), { aim: best.aim });
      const win = curve.filter(c => c.E <= best.E + 0.05).map(c => c.aim);
      out.push({ club: name, carry: club.carry, total: club.carry + club.roll, best, curve, window: [Math.min(...win), Math.max(...win)], straight: curve.find(c => c.aim === 0) || null, aim0 });
    }
    out.sort((a, b) => a.best.E - b.best.E);
    return out;
  }

  // ---------- approach from any point ----------
  function approach(h, ball, P, altf, opts) {
    if (!h || !h.grid) return null;
    const H = decodeHole(h); applyPin(H, P); const n = opts && opts.n || 800; const keep = opts && opts.keep || 120; const base = P.baseline; const bearing = h.bearing || 0;
    const vx = H.pin[0] - ball[0], vy = H.pin[1] - ball[1]; const distM = Math.hypot(vx, vy); const rem = distM / YD;
    const z0 = zAt(H, ball[0], ball[1]); const dz = H.pinFt - z0; const k = descentK(P, null, rem); const plays = Math.max(5, rem + k * dz / 3);
    const fromTee = ball[0] === 0 && ball[1] === 0;
    const fromLie = opts && opts.fromLie != null ? opts.fromLie : fromTee ? L.TEE : lieAt(H, ball[0], ball[1]);
    const club = opts && opts.club ? clubParams(opts.club, P, altf) : clubForDistance(plays, P, altf, fromTee);
    const pen = (LIEFX[fromLie] || LIEFX[1]).pen;   // the lie you play from: its extra strokes (desert and scrub 0.4, water 1), inside every option's expectation
    const buf = { px: new Float32Array(n), py: new Float32Array(n) }; let best = null; const options = [];
    const ux = vx / distM, uy = vy / distM, rx = -uy, ry = ux;   // r = right-hand normal in frame (right of the shot)
    const lats = opts && opts.lats || [-12, -8, -4, 0, 4, 8, 12], depths = opts && opts.depths || [-8, 0, 8];
    for (const lat of lats) for (const dep of depths) {
      const tx = H.pin[0] + rx * lat * YD + ux * dep * YD, ty = H.pin[1] + ry * lat * YD + uy * dep * YD;
      const tvx = tx - ball[0], tvy = ty - ball[1]; const tL = Math.hypot(tvx, tvy) / YD; const ang = Math.atan2(tvy, tvx) * 180 / Math.PI;
      const c = Object.assign({}, club); const scale = (tL + k * dz / 3) / Math.max(1e-6, c.carry + c.roll);
      if (c.shortBy != null && scale > 1.02) continue;
      if (c.shortBy == null) { const s = Math.min(scale, 1); c.carry *= s; c.roll *= s; }
      const rand = mulberry32(P.seed * 1000 + 99); shoot(H, ball, ang, c, n, rand, P, bearing, buf, fromLie);
      const r = price(H, buf.px, buf.py, n, P, base, 0, pen); const o = { lat, depth: dep, E: r.E, odds: r.odds, prox: r.rem * 3, ang, clubScaled: c };
      options.push(o); if (!best || r.E < best.E) best = o;
    }
    if (best) { const rand = mulberry32(P.seed * 1000 + 99); shoot(H, ball, best.ang, best.clubScaled, n, rand, P, bearing, buf, fromLie); best.sample = price(H, buf.px, buf.py, n, P, base, keep, pen).sample; }
    const fwT = lut(base, "fairway"), rgT = lut(base, "rough");
    return { from: rem, plays, dz, club: club.name, shortBy: club.shortBy || 0, best, options, fromLie, fromPen: pen, curveFairway: baseAt(fwT, plays), curveRough: baseAt(rgT, plays) };
  }

  // ---------- lay-up vs go from a point (par 5 second shots, drivable par 4s) ----------
  function goVsLay(h, ball, P, altf, opts) {
    if (!h || !h.grid) return null;
    const H = decodeHole(h); applyPin(H, P); const go = approach(h, ball, P, altf, Object.assign({ n: 800 }, opts || {}));
    const base = P.baseline; const n = 700; const buf = { px: new Float32Array(n), py: new Float32Array(n) };
    const fromLie = opts && opts.fromLie != null ? opts.fromLie : null;   // the lay-up is played from the same (recorded) lie as the go
    const vx = H.pin[0] - ball[0], vy = H.pin[1] - ball[1]; const distM = Math.hypot(vx, vy); const ux = vx / distM, uy = vy / distM, rx = -uy, ry = ux;
    const R = distM / YD; const lays = [];
    for (const leave of [80, 100, 120, 140]) {
      if (leave >= R - 25) continue;
      let bestL = null;
      for (const lat of [-10, 0, 10]) {
        const tx = H.pin[0] - ux * leave * YD + rx * lat * YD, ty = H.pin[1] - uy * leave * YD + ry * lat * YD;
        const tvx = tx - ball[0], tvy = ty - ball[1]; const tL = Math.hypot(tvx, tvy) / YD; const ang = Math.atan2(tvy, tvx) * 180 / Math.PI;
        const c = clubForDistance(tL, P, altf, false); if (c.shortBy) continue;
        const rand = mulberry32(P.seed * 1000 + 31); shoot(H, ball, ang, c, n, rand, P, h.bearing || 0, buf, fromLie);
        // price each lay-up landing with a simulated wedge from a few representative points (bucket by lie and distance)
        const buckets = {}; let pen = 0;
        for (let i = 0; i < n; i++) {
          const lie = lieAt(H, buf.px[i], buf.py[i]); const r = Math.hypot(buf.px[i] - H.pin[0], buf.py[i] - H.pin[1]) / YD;
          const key = lie + ":" + Math.round(r / 15); (buckets[key] = buckets[key] || { lie, pts: [], }).pts.push([buf.px[i], buf.py[i]]);
        }
        let Esum = 0, Wsum = 0; const shares = { fairway: 0, rough: 0, sand: 0, water: 0, desert: 0, green: 0 }; const [dp, du, dl] = desertShares(P);
        for (const key in buckets) {
          const b = buckets[key]; const m = b.pts.length; const cx = b.pts.reduce((s, p) => s + p[0], 0) / m, cy = b.pts.reduce((s, p) => s + p[1], 0) / m;
          const lie = b.lie;
          if (lie === L.OB) { Esum += 1 * m; Wsum += m; shares.oob = (shares.oob || 0) + m / n; continue; }   // out of bounds: the penalty stroke, then the lay-up again
          const a = approach(h, [cx, cy], P, altf, { n: 250, keep: 0, lats: [-6, 0, 6], depths: [0], fromLie: lie });
          let Eb = a.best ? a.best.E : 1 + a.curveRough + a.fromPen; // wedge from the bucket centre, best of three aims; the from-lie extra (water's penalty stroke, scrub's and desert's 0.4) is inside
          if (lie === L.SAND || lie === L.WASTE) Eb += Math.max(0, baseAt(lut(base, "sand"), a.plays) - baseAt(lut(base, "fairway"), a.plays));
          else if (lie === L.ROUGH || lie === L.OGREEN || lie === L.DESERT || lie === L.WATER || lie === L.SCRUB) Eb += Math.max(0, baseAt(lut(base, "rough"), a.plays) - baseAt(lut(base, "fairway"), a.plays));
          if (lie === L.DESERT && H.desertPA) Eb = dp * Eb + (du + dl) * (1 + Eb - P.scrub_extra);   // the card's rule: a ball not played is a stroke and a drop at the grass line
          else if (lie === L.DESERT) { const dDrop = P.desert_drop_extra != null ? P.desert_drop_extra : P.scrub_extra; Eb = dp * Eb + du * (1 + Eb - P.scrub_extra + dDrop) + dl * 1; Wsum += dl * m; }   // found and played, dropped (one more, on desert ground), lost (the lay-up again)
          Esum += Eb * m;
          const k2 = lie === L.FAIRWAY || lie === L.TEE ? "fairway" : (lie === L.SAND || lie === L.WASTE) ? "sand" : lie === L.WATER ? "water" : (lie === L.DESERT || lie === L.SCRUB) ? "desert" : lie === L.GREEN ? "green" : "rough";
          shares[k2] += m / n;
        }
        const E = (1 + Esum / n + go.fromPen) / (1 - Math.min(0.95, Wsum / n)); const o = { leave, lat, E, club: c.name, shares };   // the same from-lie extra the go carries; a lost lay-up is the lay-up again
        if (!bestL || E < bestL.E) bestL = o;
      }
      if (bestL) lays.push(bestL);
    }
    lays.sort((a, b) => a.E - b.E);
    return { R, go, lay: lays[0] || null, lays, delta: lays.length && go.best ? lays[0].E - go.best.E : null };
  }

  // ---------- per hole ----------
  // ---------- the corridor rule (session K, 2026-10-08): DECADE's public tee rule, priced by this engine ----------
  // "Dead zones" are penalty ground (desert, water, scrub). For each tee club, over the engine's own aim scan, the aim whose landing
  // corridor is widest: the run of non-penalty cells through the landing point, laterally (perpendicular to the aim), the least of three
  // depths (L − σ, L, L + σ with σ the pattern's distance spread); "crossed" when a depth within ±1.5 σ has more than 60 % penalty cells
  // across that corridor. The rule's line is toward the corridor's centre on the 2° grid; its price is the engine's own curve at that aim
  // (the same seeded simulation); the corridor is searched within ±10° of the fairway's own line (the landing area a golfer
  // would look at, not another hole's). The rule: the longest club whose corridor is at least minWidth yards and is not crossed; failing all,
  // the widest uncrossed corridor, else the widest. options = teeOptions(h, P, altf) (so nothing is re-simulated).
  const PEN_LIES = new Set([L.DESERT, L.WATER, L.SCRUB, L.OB]);   // out of bounds added (session P)
  function corridorAt(H, aimDeg, Lm, sigmaM) {
    const a = aimDeg * Math.PI / 180, ux = Math.cos(a), uy = Math.sin(a), rx = -uy, ry = ux;
    const runAt = depthM => { const lies = []; for (let t = -160; t <= 160; t++) { lies.push(PEN_LIES.has(lieAt(H, ux * depthM + rx * t * YD, uy * depthM + ry * t * YD)) ? 0 : 1); }
      const c = 160; if (!lies[c]) return [0, 0, lies]; let lo = c, hi = c; while (lo > 0 && lies[lo - 1]) lo--; while (hi < 320 && lies[hi + 1]) hi++; return [lo - c, hi - c, lies]; };
    const [lo, hi] = runAt(Lm); const w0 = hi - lo; const ws = [w0];
    for (const d of [Lm - sigmaM, Lm + sigmaM]) { const r = runAt(d); ws.push(r[1] - r[0]); }
    let crossed = false; if (w0 > 0) for (let d = Lm - 1.5 * sigmaM; d <= Lm + 1.5 * sigmaM; d += 2 * YD) { const lies = runAt(d)[2]; let pen = 0, tot = 0; for (let t = lo; t <= hi; t++) { tot++; if (!lies[t + 160]) pen++; } if (tot > 0 && pen / tot > 0.6) { crossed = true; break; } }
    return { width: Math.min(...ws), widthAtL: w0, lo, hi, centre: (lo + hi) / 2, crossed };
  }
  function landingYd(H, P, club, aimDeg) {   // carry + roll along this aim, the engine's elevation rule applied twice
    const a = aimDeg * Math.PI / 180; let dist = club.carry; const k = 1 / Math.tan((club.name === "Driver" ? P.angles.driver : (club.name === "3-wood" || club.name === "Hybrid") ? P.angles.wood : P.angles.long) * Math.PI / 180);
    const z0 = zAt(H, 0, 0); for (let i = 0; i < 2; i++) { const zl = zAt(H, Math.cos(a) * dist * YD, Math.sin(a) * dist * YD); dist = club.carry + k * (z0 - zl) / 3; }
    return dist + club.roll;
  }
  function corridorRule(h, P, altf, options, minWidth) {
    minWidth = minWidth || 65; const H = decodeHole(h); applyPin(H, P); const aim0 = options[0].aim0; const clubs = {};
    const snap = aim => Math.max(aim0 + P.aim_min, Math.min(aim0 + P.aim_max, Math.round(aim / P.aim_step) * P.aim_step));
    for (const o of options) { const club = clubParams(o.club, P, altf); let best = null;
      for (let aim = aim0 - 10; aim <= aim0 + 10; aim += P.aim_step) {   // ±10° of the fairway's own line: the landing area a golfer would look at
        const Lyd = landingYd(H, P, club, aim); const cor = corridorAt(H, aim, Lyd * YD, P.dist_pct * club.carry * YD);
        const cand = { aim, landing: Math.round(Lyd), width: cor.width, widthAtL: cor.widthAtL, centre: cor.centre, crossed: cor.crossed };
        if (!best || cand.width > best.width || (cand.width === best.width && Math.abs(aim - aim0) < Math.abs(best.aim - aim0))) best = cand; }
      const aimRule = snap(best.aim + Math.atan2(best.centre * YD, best.landing * YD) * 180 / Math.PI); const cv = o.curve.find(x => x.aim === aimRule);
      clubs[o.club] = { landing: best.landing, width: best.width, widthAtL: best.widthAtL, centre: Math.round(best.centre), corridorAim: best.aim, crossed: best.crossed, aim: aimRule, E: cv ? cv.E : null, bestAim: o.best.aim, bestE: o.best.E }; }
    const order = D.tee_clubs.filter(n => clubs[n]); let pick = null, why = "the longest club with " + minWidth + " yd between dead zones and no hazard across its landing";
    for (const n of order) { const q = clubs[n]; if (q.width >= minWidth && !q.crossed) { pick = n; break; } }
    if (!pick) { const open = order.filter(n => !clubs[n].crossed); const pool = open.length ? open : order; pick = pool.slice().sort((x, y) => clubs[y].width - clubs[x].width)[0]; why = "no club has " + minWidth + " yd between dead zones: the widest corridor"; }
    const q = clubs[pick]; const E0 = options[0].best.E;
    return { minWidth, clubs, pick: { club: pick, aim: q.aim, E: q.E, width: q.width, landing: q.landing, why, dE: q.E == null ? null : q.E - E0 }, line: { club: "Driver", aim: aim0, E: (options.find(o => o.club === "Driver") || { curve: [] }).curve.find(x => x.aim === aim0)?.E ?? null } };
  }

  function runHole(course, h, P, opts) {
    const altf = 1 + P.alt_rule / 100 * (course.alt_ft - P.home_ft) / 1000;
    if (h.nodata) return { kind: "nodata", E: null };
    if (h.par === 3) {
      const a = approach(h, [0, 0], P, altf, Object.assign({ n: opts && opts.n || P.n }, opts || {}));
      if (h.src.green === "disc" && h.src.fairway === "none") return { kind: "par3", approach: a, E: a.curveFairway, curveOnly: true };
      return { kind: "par3", approach: a, E: a.best ? a.best.E : a.curveFairway };
    }
    if (h.src.fairway === "none") return { kind: "gated", E: null };
    const options = teeOptions(h, P, altf, opts);
    const pick = options[0]; const res = { kind: "tee", options, E: pick.best.E, pick: { club: pick.club, aim: pick.best.aim, window: pick.window } };
    const planClub = (opts && opts.planClub) || h.plan.club;
    if (planClub) { const po = options.find(o => o.club === planClub); if (po) { res.planE = po.best.E; res.planAim = po.best.aim; } }
    const sm = pick.best.sample; if (sm && sm.length) { const xs = sm.map(s => s[0]).sort((a, b) => a - b), ys = sm.map(s => s[1]).sort((a, b) => a - b); res.landing = [xs[xs.length >> 1], ys[ys.length >> 1]]; res.approach = approach(h, res.landing, P, altf, { n: 600 }); }
    return res;
  }

  for (const c of D.courses) for (const h of c.holes) h._key = c.key + ":" + h.hole;
  window.LoopEngine = { setOverrides, overrideFor, pointInPoly, decodeHole, applyPin, lieAt, zAt, clubParams, clubForDistance, teeOptions, approach, goVsLay, runHole, priceAt, corridorRule, desertShares, L, YD, LIEFX, lut, baseAt, windComponents };
})();

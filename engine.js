// Fugue State — composition engine.
// Pure JS (no DOM, no audio): plans fugues, writes subjects and countersubjects,
// and composes four-voice blocks on a 16th-note grid. Runs in the page and in Node.
// Every fugue is reproducible from its token: the plan and each block reseed the RNG.
(function (root, factory) {
  const api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.FugueEngine = api;
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // ---------- randomness ----------
  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6d2b79f5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function hash2(a, b) {
    let h = (a ^ Math.imul((b + 0x9e3779b9) | 0, 0x85ebca6b)) >>> 0;
    h = Math.imul(h ^ (h >>> 16), 0x85ebca6b);
    h = Math.imul(h ^ (h >>> 13), 0xc2b2ae35);
    return (h ^ (h >>> 16)) >>> 0;
  }
  let rnd = mulberry32(1);
  const reseed = (s) => { rnd = mulberry32(s >>> 0); };
  const R = {
    f: () => rnd(),
    int: (a, b) => a + Math.floor(rnd() * (b - a + 1)),
    pick: (a) => a[Math.floor(rnd() * a.length)],
    chance: (p) => rnd() < p,
    weighted(pairs) {
      let s = 0;
      for (const p of pairs) s += p[1];
      let x = rnd() * s;
      for (const p of pairs) { x -= p[1]; if (x <= 0) return p[0]; }
      return pairs[pairs.length - 1][0];
    },
    shuffle(a) {
      a = a.slice();
      for (let i = a.length - 1; i > 0; i--) {
        const j = Math.floor(rnd() * (i + 1));
        [a[i], a[j]] = [a[j], a[i]];
      }
      return a;
    },
  };
  const mod = (n, m) => ((n % m) + m) % m;

  // ---------- voices, keys, chords ----------
  const VOICES = [
    { name: 'Soprano', short: 'S', lo: 60, hi: 81 },
    { name: 'Alto', short: 'A', lo: 53, hi: 74 },
    { name: 'Tenor', short: 'T', lo: 47, hi: 67 },
    { name: 'Bass', short: 'B', lo: 36, hi: 60 },
  ];
  const center = (v) => (VOICES[v].lo + VOICES[v].hi) / 2;

  const SCALES = { major: [0, 2, 4, 5, 7, 9, 11], minor: [0, 2, 3, 5, 7, 8, 10] };
  const NAMES_MAJOR = ['C', 'D♭', 'D', 'E♭', 'E', 'F', 'F♯', 'G', 'A♭', 'A', 'B♭', 'B'];
  const NAMES_MINOR = ['C', 'C♯', 'D', 'E♭', 'E', 'F', 'F♯', 'G', 'G♯', 'A', 'B♭', 'B'];
  const keyName = (k) => (k.mode === 'major' ? NAMES_MAJOR : NAMES_MINOR)[k.tonic] + ' ' + k.mode;
  const sameKey = (a, b) => !!a && !!b && a.tonic === b.tonic && a.mode === b.mode;
  const domKey = (k) => ({ tonic: mod(k.tonic + 7, 12), mode: k.mode });
  function relKey(k, deg) {
    const majorDegs = k.mode === 'major' ? [0, 3, 4] : [2, 5, 6];
    return { tonic: mod(k.tonic + SCALES[k.mode][deg], 12), mode: majorDegs.includes(deg) ? 'major' : 'minor' };
  }
  // Scale degree (0 = tonic, 7 = tonic an octave up) to MIDI, tonic placed in C4..B4.
  const degMidi = (k, deg) => 60 + k.tonic + 12 * Math.floor(deg / 7) + SCALES[k.mode][mod(deg, 7)];

  const chord = (key, root, opts) => Object.assign({ key, root: mod(root, 7), sev: false, pic: false }, opts || {});
  function chordDegs(ch) {
    const d = [ch.root, ch.root + 2, ch.root + 4];
    if (ch.sev) d.push(ch.root + 6);
    return d.map((x) => mod(x, 7));
  }
  // Chromatic alteration of scale degree d inside chord ch (harmonic minor, Picardy third).
  function chordAlt(ch, d) {
    if (ch.key.mode !== 'minor') return 0;
    if (d === 6 && (ch.root === 4 || ch.root === 6)) return 1;
    if (d === 2 && ch.pic && ch.root === 0) return 1;
    return 0;
  }
  const chordPCs = (ch) => chordDegs(ch).map((d) => mod(ch.key.tonic + SCALES[ch.key.mode][d] + chordAlt(ch, d), 12));

  // Turn degree lines into MIDI, applying melodic/harmonic minor inflections from context.
  function realize(notes, harm) {
    for (let i = 0; i < notes.length; i++) {
      const n = notes[i];
      n.alt = 0;
      if (n.key.mode !== 'minor') continue;
      const d = mod(n.deg, 7), ch = harm(n.t), nx = notes[i + 1];
      const here = ch && sameKey(ch.key, n.key);
      if (d === 6) {
        if (here && (ch.root === 4 || ch.root === 6)) n.alt = 1;
        else if (nx && sameKey(nx.key, n.key) && nx.deg === n.deg + 1) n.alt = 1;
      } else if (d === 2 && here && ch.pic && ch.root === 0) n.alt = 1;
    }
    for (let i = 0; i < notes.length; i++) {
      const n = notes[i];
      if (n.key.mode !== 'minor' || mod(n.deg, 7) !== 5) continue;
      const raisedAbove = (x) => x && sameKey(x.key, n.key) && x.deg === n.deg + 1 && x.alt === 1;
      if (raisedAbove(notes[i + 1]) || raisedAbove(notes[i - 1])) {
        const ch = harm(n.t);
        const heldChordTone = n.t % 4 === 0 && ch && sameKey(ch.key, n.key) && chordDegs(ch).includes(5);
        if (!heldChordTone) n.alt = 1;
      }
    }
    for (const n of notes) n.midi = degMidi(n.key, n.deg) + n.alt;
    return notes;
  }

  // Short melodic fills from degree a toward b in n notes (a included, b excluded).
  function fills(a, b, n, cset, maxOut) {
    if (n <= 1) return [[a]];
    const res = [], seq = [a];
    const rec = () => {
      if (seq.length === n) {
        const last = seq[n - 1], fin = Math.abs(b - last);
        if (fin === 0 || fin > 2) return;
        let sc = fin === 2 ? 0.8 : 0;
        const all = seq.concat([b]);
        for (let i = 1; i < all.length; i++) {
          const iv = Math.abs(all[i] - all[i - 1]);
          if (iv === 2 && !(cset.has(mod(all[i], 7)) && cset.has(mod(all[i - 1], 7)))) sc += 3;
        }
        for (let i = 1; i < n; i++) {
          if (!cset.has(mod(seq[i], 7)) && (Math.abs(seq[i] - seq[i - 1]) !== 1 || Math.abs(all[i + 1] - seq[i]) !== 1)) sc += 4;
        }
        let turns = 0;
        for (let i = 2; i < all.length; i++) if (Math.sign(all[i] - all[i - 1]) !== Math.sign(all[i - 1] - all[i - 2])) turns++;
        sc += turns * 0.35;
        res.push({ seq: seq.slice(), sc: sc + R.f() * 0.6 });
        return;
      }
      const p = seq[seq.length - 1];
      for (const st of [-2, -1, 1, 2]) { seq.push(p + st); rec(); seq.pop(); }
    };
    rec();
    res.sort((x, y) => x.sc - y.sc);
    return res.filter((r) => r.sc < 3.5).slice(0, maxOut || 4).map((r) => r.seq);
  }

  // ---------- subjects ----------
  // Harmonic skeletons: one chord root per two-beat unit, four units per subject.
  const TEMPLATES = [
    [[0, 3, 4, 0], 4], [[0, 1, 4, 0], 3], [[0, 4, 4, 0], 1], [[0, 5, 1, 4], 1.5],
    [[0, 3, 1, 4], 1.5], [[0, 4, 5, 4], 1], [[0, 0, 4, 0], 1.5], [[0, 5, 4, 0], 2],
  ];
  const CHARACTERS = {
    stately: {
      bpm: [72, 84],
      head: [[[8], 3], [[6, 2], 3], [[4], 2], [[2, 2], 1]],
      body: [[[2, 2], 4], [[4], 2], [[1, 1, 2], 1], [[2, 1, 1], 1], [[3, 1], 1]],
    },
    running: {
      bpm: [54, 62],
      head: [[[4], 2], [[2, 2], 2], [[6, 2], 1], [[2, 1, 1], 1]],
      body: [[[1, 1, 1, 1], 5], [[2, 1, 1], 2], [[1, 1, 2], 2], [[2, 2], 1]],
    },
    dotted: {
      bpm: [60, 70],
      head: [[[3, 1], 2], [[6, 2], 2], [[4], 1], [[2, 2], 1]],
      body: [[[3, 1], 3], [[2, 2], 2], [[1, 1, 2], 1], [[4], 1], [[2, 1, 1], 1]],
    },
  };

  function genRhythm(C) {
    const out = [];
    let pos = 0, guard = 0;
    while (pos < 32 && guard++ < 500) {
      let cell;
      if (pos === 24 && R.chance(0.45)) cell = [8];
      else if (pos === 28) cell = [4];
      else cell = R.weighted(pos < 8 ? C.head : C.body);
      const len = cell.reduce((a, b) => a + b, 0);
      if ((len === 8 && pos % 8 !== 0) || pos + len > 32) continue;
      let t = pos;
      for (const d of cell) { out.push({ t, dur: d }); t += d; }
      pos += len;
    }
    if (pos !== 32) return [{ t: 0, dur: 8 }, { t: 8, dur: 4 }, { t: 12, dur: 4 }, { t: 16, dur: 4 }, { t: 20, dur: 4 }, { t: 24, dur: 8 }];
    return out;
  }

  function genPitches(rhythm, tmpl, starts) {
    const s0 = R.pick(starts), cp = R.int(10, 24), h = R.int(4, 8);
    const target = (p) => (p <= cp ? s0 + h * (p / cp) : s0 + h * (1 - (p - cp) / (32 - cp)) * 0.9);
    const out = [{ t: 0, dur: rhythm[0].dur, deg: s0 }];
    let prev = s0, prevInt = 0, prevNCT = false;
    for (let i = 1; i < rhythm.length; i++) {
      const { t, dur } = rhythm[i];
      const root = tmpl[t >> 3];
      const cset = new Set(chordDegs({ root }));
      const strong = t % 4 === 0, last = i === rhythm.length - 1;
      const opts = [];
      for (let d = prev - 7; d <= prev + 7; d++) {
        const iv = d - prev, a = Math.abs(iv), ct = cset.has(mod(d, 7));
        if (strong && !ct) continue;
        if (prevNCT && a !== 1) continue;
        let w = [0.15, 5, ct ? 3 : 0.3, ct ? 1.5 : 0, ct ? 1 : 0, ct ? 0.4 : 0, 0, ct ? 0.3 : 0][a] || 0;
        if (!ct && a > 1) w = 0;
        if (Math.abs(prevInt) >= 3) w *= Math.sign(iv) === -Math.sign(prevInt) && a <= 2 ? 3 : 0.25;
        w *= Math.exp(-Math.abs(d - target(t)) * 0.45);
        if (last) { if (!ct) w = 0; if (mod(d, 7) === root) w *= 3; if (a > 2) w *= 0.3; }
        if (d < -5 || d > 11) w = 0;
        if (w > 0) opts.push([d, w]);
      }
      if (!opts.length) return null;
      const d = R.weighted(opts);
      out.push({ t, dur, deg: d });
      prevInt = d - prev; prev = d; prevNCT = !cset.has(mod(d, 7));
    }
    return out;
  }

  function scoreSubject(notes, tmpl, mode) {
    let s = 0;
    const degs = notes.map((n) => n.deg);
    const max = Math.max(...degs), min = Math.min(...degs), span = max - min;
    if (span < 4) s += (4 - span) * 3;
    if (span > 9) s += (span - 9) * 3;
    if (degs.filter((d) => d === max).length > 1) s += 2;
    const key = { tonic: 0, mode };
    const rn = realize(notes.map((n) => ({ t: n.t, dur: n.dur, deg: n.deg, key })), (t) => chord(key, tmpl[Math.min(3, t >> 3)]));
    let steps = 0, turns = 0, lastDir = 0;
    for (let i = 1; i < notes.length; i++) {
      const iv = degs[i] - degs[i - 1], a = Math.abs(iv), semi = Math.abs(rn[i].midi - rn[i - 1].midi);
      if (a === 0) s += 1.5;
      if (a === 1) steps++;
      if (a >= 5 && a !== 7) s += 2;
      if (semi === 6) s += 3;
      if (a === 1 && semi === 3) s += 4;
      if (a >= 3 && i + 1 < notes.length) {
        const nx = degs[i + 1] - degs[i];
        if (!(Math.sign(nx) === -Math.sign(iv) && Math.abs(nx) <= 2)) s += 1.5;
      }
      const dir = Math.sign(iv);
      if (dir && lastDir && dir !== lastDir) turns++;
      if (dir) lastDir = dir;
    }
    s += Math.abs(steps / Math.max(1, notes.length - 1) - 0.68) * 8;
    for (let i = 1; i < Math.min(4, degs.length); i++) if (Math.abs(degs[i] - degs[i - 1]) >= 3) { s -= 1.2; break; }
    if (turns > notes.length * 0.6) s += 2;
    const last = degs[degs.length - 1];
    if (mod(last, 7) === 0) s -= 1;
    if (degs.length > 1 && Math.abs(last - degs[degs.length - 2]) > 2) s += 1;
    const ct = notes[degs.indexOf(max)].t;
    if (ct < 6 || ct > 26) s += 1.5;
    return s + R.f() * 0.5;
  }

  function genSubject(mode, character, starts) {
    const tmpl = R.weighted(TEMPLATES);
    const rhythm = genRhythm(CHARACTERS[character]);
    let best = null, bestScore = Infinity;
    for (let i = 0; i < 260; i++) {
      const notes = genPitches(rhythm, tmpl, starts);
      if (!notes) continue;
      const sc = scoreSubject(notes, tmpl, mode);
      if (sc < bestScore) { bestScore = sc; best = notes; }
    }
    if (!best) best = rhythm.map((r, i) => ({ t: r.t, dur: r.dur, deg: i ? [0, 2, 4, 2, 1, 0][i % 6] : starts[0] }));
    return { notes: best, harm: tmpl };
  }

  // Countersubject (and the second subject of a double fugue): 3rds/6ths/10ths above the
  // subject on every beat, invertible at the octave, chosen by dynamic programming, then
  // given a complementary rhythm.
  const CS_MOT = [1.2, 0, 0.4, 1.2, 1.8, 3, 6];
  function sampleDegs(notes, len) {
    const out = new Array(len).fill(null);
    for (const n of notes) for (let i = n.t; i < n.t + n.dur && i < len; i++) out[i] = n.deg;
    return out;
  }
  // Fourths count as perfect: inverted at the octave they become fifths.
  function diatonicParallels(A, B, from, to) {
    for (let s = Math.max(1, from); s <= to && s < A.length; s++) {
      if (A[s] == null || B[s] == null || A[s - 1] == null || B[s - 1] == null) continue;
      if (A[s] === A[s - 1] || B[s] === B[s - 1]) continue;
      const i0 = mod(B[s - 1] - A[s - 1], 7), i1 = mod(B[s] - A[s], 7);
      if ((i1 === 0 || i1 === 3 || i1 === 4) && i0 === i1) return true;
    }
    return false;
  }

  function genCS(subject, character, opts) {
    opts = opts || {};
    const sn = subject.notes, tmpl = subject.harm;
    const sDeg = sampleDegs(sn, 32);
    // Within an octave above, so dropping an octave always lands below (3rds become 6ths).
    const diffs = opts.prefer6 ? [[2, 0.7], [5, 0], [7, 6]] : [[2, 0], [5, 0], [7, 6]];
    const states = [];
    for (let j = 0; j < 8; j++) {
      const s = sDeg[j * 4], cs = new Set(chordDegs({ root: tmpl[j >> 1] }));
      const row = [];
      for (const [diff, c0] of diffs) if (cs.has(mod(s + diff, 7))) row.push({ deg: s + diff, cost: c0 });
      if (!row.length) row.push({ deg: s + 2, cost: 4 });
      states.push(row);
    }
    const dp = states.map((r) => r.map(() => ({ c: Infinity, p: 0 })));
    states[0].forEach((s, i) => { dp[0][i].c = s.cost + R.f(); });
    for (let j = 1; j < 8; j++) {
      states[j].forEach((s, i) => {
        states[j - 1].forEach((q, h) => {
          const dc = s.deg - q.deg, ds = sDeg[j * 4] - sDeg[(j - 1) * 4];
          let c = dp[j - 1][h].c + s.cost + CS_MOT[Math.min(Math.abs(dc), 6)];
          if (dc && ds) c += Math.sign(dc) === Math.sign(ds) ? 0.4 : -0.3;
          if (dc && ds && mod(q.deg - sDeg[(j - 1) * 4], 7) === 0 && mod(s.deg - sDeg[j * 4], 7) === 0) c += 40;
          c += R.f() * 0.5;
          if (c < dp[j][i].c) dp[j][i] = { c, p: h };
        });
      });
    }
    let bi = 0;
    dp[7].forEach((x, i) => { if (x.c < dp[7][bi].c) bi = i; });
    const beatDeg = new Array(8);
    for (let j = 7; j >= 0; j--) { beatDeg[j] = states[j][bi].deg; bi = dp[j][bi].p; }

    let csSamp = new Array(32).fill(null);
    for (let j = 0; j < 8; j++) for (let s = j * 4; s < j * 4 + 4; s++) csSamp[s] = beatDeg[j];
    const out = [];
    for (let j = 0; j < 8; j++) {
      const t = j * 4, a = beatDeg[j], b = j < 7 ? beatDeg[j + 1] : null;
      const k = sn.filter((n) => n.t >= t && n.t < t + 4).length;
      let n = 1;
      if (b != null) {
        if (k >= 3) n = 1;
        else if (k === 2) n = R.chance(0.35) ? 2 : 1;
        else n = R.weighted([[2, 5], [4, character === 'running' ? 3 : 1.2], [3, 1.5]]);
      }
      let chosen = [{ t, dur: 4, deg: a }];
      if (n > 1) {
        const cset = new Set(chordDegs({ root: tmpl[j >> 1] }));
        const durs = n === 2 ? [2, 2] : n === 3 ? R.pick([[2, 1, 1], [1, 1, 2]]) : [1, 1, 1, 1];
        for (const seq of fills(a, b, n, cset, 4)) {
          const cand = [];
          let tt = t;
          seq.forEach((deg, i) => { cand.push({ t: tt, dur: durs[i], deg }); tt += durs[i]; });
          const tmp = csSamp.slice();
          for (const c of cand) for (let s = c.t; s < c.t + c.dur; s++) tmp[s] = c.deg;
          if (!diatonicParallels(sDeg, tmp, t + 1, t + 4)) { chosen = cand; csSamp = tmp; break; }
        }
      }
      out.push(...chosen);
    }
    const merged = [];
    for (const n of out) {
      const p = merged[merged.length - 1];
      if (p && p.deg === n.deg && p.dur === 4 && n.dur === 4 && p.t + 4 === n.t && p.t >> 3 === n.t >> 3 && R.chance(0.7)) p.dur += 4;
      else merged.push(Object.assign({}, n));
    }
    return merged;
  }

  // Tonal answer: a dominant in the subject's head is answered by the tonic, so the answer
  // starts in the home key and slides to the dominant. The first harmony unit becomes IV of
  // the dominant key (the home tonic chord) and the countersubject's first unit is rewritten.
  function tonalAnswer(subject, cs) {
    const notes = subject.notes.map((n) => Object.assign({}, n));
    let changed = false;
    for (const n of notes) {
      const d = mod(n.deg, 7);
      if (n.t >= 8 || (d !== 0 && d !== 4)) break;
      if (d === 4) { n.deg -= 1; changed = true; }
    }
    if (!changed) return null;
    const iv = new Set(chordDegs({ root: 3 }));
    for (const n of notes) if (n.t < 8 && n.t % 4 === 0 && !iv.has(mod(n.deg, 7))) return null;
    const harm = subject.harm.slice();
    harm[0] = 3;
    const sD = sampleDegs(notes, 32), oD = sampleDegs(cs, 32);
    const head = [];
    for (const j of [0, 1]) {
      const s = sD[j * 4], orig = oD[j * 4];
      let best = null;
      for (const diff of [2, 5]) {
        const c = s + diff;
        if (iv.has(mod(c, 7)) && (best == null || Math.abs(c - orig) < Math.abs(best - orig))) best = c;
      }
      if (best == null) return null;
      head.push({ t: j * 4, dur: 4, deg: best });
    }
    if (head[0].deg === head[1].deg) { head[0].dur = 8; head.pop(); }
    return { notes, harm, cs: head.concat(cs.filter((n) => n.t >= 8).map((n) => Object.assign({}, n))) };
  }

  // Choose one chord root per unit for arbitrary lines (inversion, stretto).
  const ROOT_BIAS = [0.5, -0.4, -0.6, 0.3, 0.45, 0.1, -1.0];
  function harmonize(lineSets, nUnits) {
    const score = [];
    for (let u = 0; u < nUnits; u++) {
      const row = [];
      for (let r = 0; r < 7; r++) {
        const cs = new Set(chordDegs({ root: r }));
        let s = ROOT_BIAS[r];
        for (const line of lineSets) for (const n of line) {
          const a = Math.max(n.t, u * 8), b = Math.min(n.t + n.dur, u * 8 + 8);
          if (b <= a) continue;
          const w = (b - a) * (a % 4 === 0 ? 1.5 : 1);
          s += cs.has(mod(n.deg, 7)) ? w : -w * (a % 4 === 0 ? 1.2 : 0.4);
        }
        row.push(s);
      }
      score.push(row);
    }
    const trans = (a, b) => {
      if (b === mod(a + 3, 7)) return 1.0;
      if (a === 4 && b === 3) return -1;
      if (b === mod(a + 1, 7)) return 0.4;
      if (b === mod(a - 2, 7)) return 0.3;
      if (a === b) return -0.3;
      return 0;
    };
    const dp = score.map((row) => row.map(() => ({ v: -Infinity, p: 0 })));
    for (let r = 0; r < 7; r++) dp[0][r].v = score[0][r] + (r === 0 ? 1.5 : 0);
    for (let u = 1; u < nUnits; u++) {
      for (let r = 0; r < 7; r++) for (let q = 0; q < 7; q++) {
        const v = dp[u - 1][q].v + score[u][r] + trans(q, r);
        if (v > dp[u][r].v) dp[u][r] = { v, p: q };
      }
    }
    let br = 0;
    for (let r = 0; r < 7; r++) if (dp[nUnits - 1][r].v > dp[nUnits - 1][br].v) br = r;
    const roots = new Array(nUnits);
    for (let u = nUnits - 1; u >= 0; u--) { roots[u] = br; br = dp[u][br].p; }
    return roots;
  }

  // Which stretto distances, intervals and inversions keep strong beats consonant?
  function strettoOptions(subject) {
    const S = sampleDegs(subject.notes, 32), a0 = subject.notes[0].deg, opts = [];
    const entry = (off, shift, inv) => (t) => {
      const u = t - off;
      if (u < 0 || u >= 32 || S[u] == null) return null;
      return (inv ? 2 * a0 - S[u] : S[u]) + shift;
    };
    const pairOK = (A, B, from, to) => {
      for (let t = from; t < to; t++) {
        const a = A(t), b = B(t);
        if (a == null || b == null) continue;
        if (t % 4 === 0) { const iv = mod(a - b, 7); if (iv === 1 || iv === 6) return false; }
        if (t > from) {
          const a1 = A(t - 1), b1 = B(t - 1);
          if (a1 != null && b1 != null && a1 !== a && b1 !== b) {
            const i0 = mod(a1 - b1, 7), i1 = mod(a - b, 7);
            if (i0 === i1 && (i1 === 0 || i1 === 3 || i1 === 4)) return false;
          }
        }
      }
      return true;
    };
    const lead = entry(0, 0, false);
    for (const d of [8, 16, 24]) for (const shift of [0, 4, -3]) for (const inv of [false, true]) {
      const fol = entry(d, shift, inv);
      if (!pairOK(lead, fol, d, 32)) continue;
      opts.push({ d, shift, inv, third: null, score: d / 16 + (shift ? 0.3 : 0) + (inv ? 0.2 : 0) + R.f() * 0.4 });
      if (d <= 16) {
        for (const s3 of [0, 4, -3, 7]) {
          const th = entry(2 * d, s3, false);
          if (pairOK(lead, th, 2 * d, 32) && pairOK(fol, th, 2 * d, d + 32)) {
            opts.push({ d, shift, inv, third: { shift: s3 }, score: d / 16 - 0.6 + R.f() * 0.4 });
          }
        }
      }
    }
    return opts.sort((a, b) => a.score - b.score);
  }

  // ---------- fugue plan ----------
  const ORDERS4 = [[1, 0, 2, 3], [2, 1, 0, 3], [0, 1, 2, 3], [3, 2, 1, 0], [1, 2, 0, 3], [2, 3, 1, 0], [0, 1, 3, 2], [1, 0, 3, 2]];
  const ORDERS3 = [[1, 0, 3], [0, 1, 3], [3, 1, 0], [1, 3, 0], [0, 3, 1], [3, 0, 1]];

  function relatedKeys(k, n) {
    const degs = k.mode === 'major' ? [5, 4, 3, 1, 2] : [2, 4, 3, 5, 6];
    let pool = R.shuffle(degs);
    if (R.chance(0.6)) pool = [degs[0]].concat(pool.filter((d) => d !== degs[0]));
    return pool.slice(0, n).map((d) => relKey(k, d));
  }

  function nextKey(k, pic) {
    const r = k.tonic;
    const opts = k.mode === 'major' || pic
      ? [[{ tonic: mod(r + 7, 12), mode: 'major' }, 2], [{ tonic: mod(r + 7, 12), mode: 'minor' }, 1.5], [{ tonic: mod(r + 4, 12), mode: 'minor' }, 1.5], [{ tonic: r, mode: 'minor' }, 1]]
      : [[{ tonic: mod(r + 3, 12), mode: 'major' }, 2], [{ tonic: mod(r + 7, 12), mode: 'minor' }, 1.5], [{ tonic: mod(r + 7, 12), mode: 'major' }, 0.7], [{ tonic: r, mode: 'major' }, 1]];
    return R.weighted(opts);
  }

  // Start degrees for a subject: bit 0 = tonic, bit 1 = dominant above, bit 2 = dominant below.
  const START_DEGS = [0, 4, -3];
  function startsFromMask(mask) {
    if (!mask || mask === 7) return [0, 0, 4, -3];
    return START_DEGS.filter((_, i) => mask & (1 << i));
  }
  function maskForHeld(key, held) {
    let m = 0;
    START_DEGS.forEach((d, i) => { if (held.includes(mod(key.tonic + SCALES[key.mode][mod(d, 7)], 12))) m |= 1 << i; });
    return m || 7;
  }

  // ---------- tokens ----------
  const CHAR_CODE = { stately: 's', running: 'r', dotted: 'd' };
  const CODE_CHAR = { s: 'stately', r: 'running', d: 'dotted' };
  function tokenFor(p) {
    return 'f-' + (p.seed >>> 0).toString(36) + '-' + p.key.tonic.toString(36) + (p.key.mode === 'major' ? 'M' : 'm') +
      CHAR_CODE[p.character] + p.voices + (p.form === 'double' ? 'd' : 's') + p.startMask + p.devices + p.density;
  }
  function parseToken(str) {
    const m = /^f-([0-9a-z]{1,7})-([0-9ab])([Mm])([srd])([34])([sd])([1-7])([0-7])([0-4])$/.exec(String(str || '').trim());
    if (!m) return null;
    const seed = parseInt(m[1], 36);
    if (!(seed >= 0 && seed <= 0xffffffff)) return null;
    return {
      seed: seed >>> 0, key: { tonic: parseInt(m[2], 36), mode: m[3] === 'M' ? 'major' : 'minor' }, character: CODE_CHAR[m[4]],
      voices: +m[5], form: m[6] === 'd' ? 'double' : 'single', startMask: +m[7], devices: +m[8], density: +m[9],
    };
  }

  // p: {seed, key, character?, voices?, form?, startMask?, devices?, density?}. Auto choices
  // always draw from the RNG, so overriding one never shifts the others.
  function planFugue(p) {
    reseed(p.seed);
    const autoChar = R.weighted([['stately', 1], ['running', 1.2], ['dotted', 0.8]]);
    const autoVoices = R.chance(0.3) ? 3 : 4;
    const autoForm = R.chance(0.25) ? 'double' : 'single';
    const params = {
      seed: p.seed >>> 0, key: { tonic: p.key.tonic, mode: p.key.mode },
      character: p.character || autoChar, voices: p.voices || autoVoices, form: p.form || autoForm,
      startMask: p.startMask || 7, devices: p.devices == null ? 7 : p.devices, density: p.density == null ? 2 : p.density,
    };
    const { key, character, devices } = params;
    const C = CHARACTERS[character];
    const bpm = R.int(C.bpm[0], C.bpm[1]);
    const subject = genSubject(key.mode, character, startsFromMask(params.startMask));
    const cs = genCS(subject, character);
    const answer = tonalAnswer(subject, cs);
    const subject2 = params.form === 'double' ? genCS(subject, character === 'running' ? 'stately' : 'running', { prefer6: true }) : null;
    const all = params.voices === 4 ? [0, 1, 2, 3] : [0, 1, 3];
    const order = R.pick(params.voices === 4 ? ORDERS4 : ORDERS3);
    const canDim = subject.notes.every((n) => n.dur % 2 === 0 && n.t % 2 === 0);

    let motifUnit = 0, mostOnsets = -1;
    for (const u of R.shuffle([0, 1, 2])) {
      const n = subject.notes.filter((x) => x.t >= u * 8 && x.t < u * 8 + 8).length;
      if (n > mostOnsets) { mostOnsets = n; motifUnit = u; }
    }

    const dom = domKey(key), VN = VOICES.map((v) => v.name);
    const others = (...xs) => all.filter((v) => !xs.includes(v));
    const secs = [];
    order.forEach((v, i) => {
      secs.push({
        type: 'entry', group: 'exposition', form: i % 2 ? 'answer' : 'subject', voice: v,
        key: i % 2 ? dom : key, cs: i ? order[i - 1] : null, active: order.slice(0, i + 1),
        title: (i % 2 ? 'Answer' : 'Subject') + ' · ' + VN[v],
      });
    });
    const episode = (to, avoid, kind) => {
      const pool = kind === 'dompedal' ? others(3) : all;
      const lp = pool.filter((v) => v !== avoid);
      const lead = R.pick(lp.length ? lp : pool);
      const sp = pool.filter((v) => v !== lead && v !== avoid);
      const second = R.pick(sp.length ? sp : pool.filter((v) => v !== lead));
      const free = others(lead, second, kind === 'dompedal' ? 3 : -1);
      let rest = null;
      if (avoid != null && free.includes(avoid) && R.chance(0.6)) rest = avoid;
      else if (R.chance(0.25) && free.length > 1) rest = R.pick(free);
      if (kind === 'dompedal') {
        return { type: 'dompedal', to, key: to, units: 4, lead, second, rest: null, swap: R.chance(0.5), title: 'Dominant pedal' };
      }
      return { type: 'episode', to, key: to, units: R.pick([4, 4, 6]), lead, second, rest, swap: R.chance(0.4), title: 'Episode' };
    };
    const nMid = R.chance(0.5) ? 2 : 3;
    const midKeys = relatedKeys(key, nMid);
    let lastVoice = order[order.length - 1];

    if (params.form === 'double') {
      const o2 = R.shuffle(all);
      secs.push(episode(key, o2[0]));
      for (let i = 0; i < 3; i++) {
        const v = o2[i];
        secs.push({
          type: 'entry', group: 'exposition2', form: 'subject2', voice: v, key: i % 2 ? dom : key, cs: null,
          active: o2.slice(0, Math.min(all.length, i + 2)), title: 'Subject II · ' + VN[v],
        });
      }
      lastVoice = o2[2];
      midKeys.forEach((k) => {
        const v = R.pick(all.filter((x) => x !== lastVoice));
        const v2 = R.pick(others(v));
        secs.push(episode(k, v));
        secs.push({ type: 'entry', group: 'middle', form: 'combined', voice: v, voice2: v2, key: k, cs: null, active: all, title: 'Both subjects · ' + keyName(k) });
        lastVoice = v;
      });
    } else {
      let usedAug = false, usedDim = false;
      midKeys.forEach((k, i) => {
        const r = R.f();
        let form = 'subject';
        if (i === nMid - 1 && devices & 1 && r < 0.55) form = 'inversion';
        else if (devices & 2 && !usedAug && r > 0.72) { form = 'augmentation'; usedAug = true; }
        else if (devices & 2 && canDim && !usedDim && r > 0.45 && r <= 0.72) { form = 'diminution'; usedDim = true; }
        const pickV = R.pick(all.filter((x) => x !== lastVoice));
        const v = form === 'augmentation' && R.chance(0.7) ? 3 : pickV;
        const v2 = R.pick(others(v));
        const csV = form === 'subject' ? R.pick(others(v)) : null;
        const freeV = others(v, csV);
        const rest = form === 'subject' && freeV.length > 1 && R.chance(0.2) ? R.pick(freeV) : null;
        secs.push(episode(k, v));
        const label = { subject: 'Entry', inversion: 'Inversion', augmentation: 'Augmentation', diminution: 'Diminution' }[form];
        secs.push({
          type: 'entry', group: 'middle', form, voice: v, voice2: form === 'diminution' ? v2 : null, key: k, cs: csV,
          active: all.filter((x) => x !== rest), title: label + ' · ' + keyName(k),
        });
        lastVoice = v;
      });
    }
    secs.push(episode(key, null));
    if (R.chance(0.55)) secs.push(episode(key, null, 'dompedal'));
    const so = devices & 4 ? strettoOptions(subject) : [];
    const augEnd = R.chance(0.5);
    if (so.length) {
      const three = so.filter((o) => o.third);
      const o = three.length && R.chance(0.6) ? three[0] : so[0];
      const vs = R.shuffle(all);
      secs.push({
        type: 'stretto', key, leader: vs[0], follower: vs[1], third: o.third ? vs[2] : null, d: o.d, shift: o.shift, inv: o.inv,
        thirdShift: o.third ? o.third.shift : 0, title: o.third ? 'Stretto in three voices' : o.inv ? 'Stretto by inversion' : 'Stretto',
      });
    } else if (devices & 2 && augEnd) {
      secs.push({ type: 'entry', group: 'final', form: 'augmentation', voice: 3, key, cs: null, active: all, title: 'Augmentation · Bass' });
    } else {
      secs.push({ type: 'entry', group: 'final', form: 'subject', voice: 3, key, cs: 0, active: all, title: 'Final entry · Bass' });
    }
    secs.push({ type: 'cadence', key, pic: key.mode === 'minor' && R.chance(0.65), title: 'Pedal & cadence' });

    return {
      params, token: tokenFor(params), key, character, bpm, voices: all, form: params.form,
      subject, cs, answer, subject2, order, motifUnit, sections: secs,
    };
  }

  function sectionLength(s) {
    if (s.type === 'episode' || s.type === 'dompedal') return s.units * 8;
    if (s.type === 'stretto') return 32 + (s.third != null ? 2 * s.d : s.d);
    if (s.type === 'entry' && s.form === 'augmentation') return 64;
    return 32;
  }

  // Tempo at a step, including the closing ritardando.
  function stepBpm(b, step) {
    let bpm = b.bpm;
    if (b.rit) {
      const p = (step - b.start) / b.len;
      if (p > 0.55) bpm *= 1 - 0.2 * Math.pow((p - 0.55) / 0.45, 2);
    }
    return bpm;
  }

  // ---------- performance (humanization) ----------
  // A player's choices layered over the score: dynamics, timing, articulation, rubato.
  // Seeded by the fugue, so a replayed fugue is also played the same way. amount: 0 = strict.
  const unitHash = (seed, k) => hash2(seed >>> 0, k | 0) / 4294967296;
  const seedOf = (b) => (b && b.fugue && b.fugue.params ? b.fugue.params.seed : 0);
  const SUBJECT_TAGS = { subject: 1, answer: 1, inversion: 1, subject2: 1 };
  const SECTION_SHADE = { episode: -0.06, dompedal: 0.05, stretto: 0.06, cadence: 0.03 };

  // Velocity multiplier: metric accent, an arch over the section, melodic contour, section shading.
  function expression(n, b, amount) {
    if (!amount) return 1;
    const rel = n.start - b.start, pos = mod(rel, 16);
    const metric = pos === 0 ? 0.08 : pos === 8 ? 0.04 : pos % 4 === 0 ? 0.01 : pos % 2 === 0 ? -0.03 : -0.06;
    const arch = 0.07 * Math.sin(Math.PI * Math.min(1, Math.max(0, (rel + n.dur / 2) / b.len)));
    const contour = (n.midi - center(n.voice)) * 0.004;
    const held = n.dur >= 8 ? 0.03 : 0;
    const shade = SECTION_SHADE[b.sec && b.sec.type] || 0;
    const wobble = (unitHash(seedOf(b), n.start * 8 + n.voice + 7) - 0.5) * 0.06;
    return Math.max(0.6, Math.min(1.4, 1 + amount * (metric + arch + contour + held + shade + wobble)));
  }

  // Onset offset (seconds), relative gate (1 = the instrument's usual articulation) and
  // intonation drift (cents).
  function timing(n, b, amount) {
    if (!amount) return { dt: 0, gate: 1, cents: 0 };
    const seed = seedOf(b), k = n.start * 8 + n.voice;
    const jitter = (unitHash(seed, k) + unitHash(seed, k + 3) - 1) * 0.012;
    const lead = SUBJECT_TAGS[n.tag] ? -0.006 : n.voice === 3 ? -0.002 : 0;
    let g = 1;
    if (n.leap == null) g = n.start + n.dur >= b.start + b.len ? 0.9 : 0.94; // breath before a rest or a new section
    else if (n.leap === 0) g = 0.8;                                          // repeated note: re-strike clearly
    else if (n.leap <= 2) g = 1.04;                                          // stepwise: legato
    else if (n.leap <= 5) g = 0.97;
    else g = 0.9;                                                            // leap: detach a little
    const a = Math.min(1, amount);
    return {
      dt: amount * (jitter + lead),
      gate: 1 + (g - 1) * a,
      cents: amount * (unitHash(seed, k + 11) - 0.5) * 7,
    };
  }

  // Tempo factor for one step (> 1 is slower): a slow breathing curve, a broadened last beat
  // before each new section, and a little forward push through episodes and stretto.
  function rubato(b, step, amount) {
    if (!amount) return 1;
    const rel = step - b.start, L = b.len;
    const ph = unitHash(seedOf(b), b.start) * 2 * Math.PI;
    let f = 1 + 0.018 * amount * Math.sin((2 * Math.PI * rel) / 32 + ph);
    if (rel >= L - 4) f += 0.05 * amount * ((rel - (L - 4) + 1) / 4);
    if (b.sec && (b.sec.type === 'stretto' || b.sec.type === 'episode')) f -= 0.012 * amount;
    return f;
  }

  // ---------- block specs ----------
  const shiftNotes = (notes, dt, ddeg, key, scale) => notes.map((n) => ({
    t: (scale || 1) * n.t + dt, dur: (scale || 1) * n.dur, deg: n.deg + ddeg, key,
  }));
  const invertNotes = (notes, a, shift, dt, key) => notes.map((n) => ({ t: n.t + dt, dur: n.dur, deg: 2 * a - n.deg + shift, key }));

  function buildSpec(sec, fg, density) {
    const all = fg.voices;
    const roles = ['rest', 'rest', 'rest', 'rest'];
    const spec = {
      len: sectionLength(sec), unitLen: 8, harmony: null, roles, fixed: [], key: sec.key,
      running: fg.character === 'running', density: density == null ? 2 : density, susProb: 0.5,
    };
    const S = fg.subject, CS = fg.cs, k = sec.key;
    const fix = (voice, tag, notes) => { spec.fixed.push({ voice, segs: [{ tag, notes }] }); roles[voice] = 'fixed'; };
    if (sec.type === 'entry') {
      for (const v of sec.active) roles[v] = 'free';
      if (sec.form === 'inversion') {
        const notes = invertNotes(S.notes, S.notes[0].deg, 0, 0, k);
        spec.harmony = harmonize([notes], 4).map((r) => chord(k, r));
        fix(sec.voice, 'inversion', notes);
      } else if (sec.form === 'augmentation') {
        spec.harmony = S.harm.flatMap((r) => [chord(k, r), chord(k, r)]);
        fix(sec.voice, 'subject', shiftNotes(S.notes, 0, 0, k, 2));
      } else if (sec.form === 'diminution') {
        spec.unitLen = 4;
        spec.harmony = S.harm.concat(S.harm).map((r) => chord(k, r));
        fix(sec.voice, 'subject', S.notes.map((n) => ({ t: n.t / 2, dur: n.dur / 2, deg: n.deg, key: k })));
        fix(sec.voice2, 'subject', S.notes.map((n) => ({ t: n.t / 2 + 16, dur: n.dur / 2, deg: n.deg, key: k })));
      } else if (sec.form === 'subject2') {
        spec.harmony = S.harm.map((r) => chord(k, r));
        fix(sec.voice, 'subject2', shiftNotes(fg.subject2, 0, 0, k));
      } else if (sec.form === 'combined') {
        spec.harmony = S.harm.map((r) => chord(k, r));
        fix(sec.voice, 'subject', shiftNotes(S.notes, 0, 0, k));
        fix(sec.voice2, 'subject2', shiftNotes(fg.subject2, 0, 0, k));
      } else {
        const A = sec.form === 'answer' && fg.answer ? fg.answer : null;
        spec.harmony = (A ? A.harm : S.harm).map((r) => chord(k, r));
        fix(sec.voice, sec.form, shiftNotes(A ? A.notes : S.notes, 0, 0, k));
        if (sec.cs != null) fix(sec.cs, 'cs', shiftNotes(A ? A.cs : CS, 0, 0, k));
      }
    } else if (sec.type === 'episode' || sec.type === 'dompedal') {
      const n = sec.units;
      const chain = sec.type === 'dompedal' ? [0, 4, 0, 4] : [0, 3, 6, 2, 5, 1, 4].slice(7 - n);
      spec.harmony = chain.map((r) => chord(k, r, { sev: sec.type === 'dompedal' && r === 4 }));
      for (const v of all) roles[v] = v === sec.rest ? 'rest' : 'free';
      if (sec.type === 'dompedal') {
        roles[3] = 'pedal';
        spec.pedalMidi = 36 + mod(k.tonic + 7, 12);
      } else spec.susProb = 0.8;
      const u = fg.motifUnit, rs = S.harm[u];
      const mot = S.notes.filter((x) => x.t >= u * 8 && x.t < u * 8 + 8);
      const cfr = CS.filter((x) => x.t >= u * 8 && x.t < u * 8 + 8);
      const segA = [], segB = [];
      chain.forEach((r, i) => {
        let off = mod(r - rs, 7);
        if (off > 3) off -= 7;
        const a = { tag: 'motif', notes: shiftNotes(mot, i * 8 - u * 8, off, k) };
        const b = { tag: 'cs', notes: shiftNotes(cfr, i * 8 - u * 8, off, k) };
        if (sec.swap && i % 2) { segA.push(b); segB.push(a); } else { segA.push(a); segB.push(b); }
      });
      spec.fixed.push({ voice: sec.lead, segs: segA }, { voice: sec.second, segs: segB });
      roles[sec.lead] = roles[sec.second] = 'fixed';
    } else if (sec.type === 'stretto') {
      for (const v of all) roles[v] = 'free';
      const a0 = S.notes[0].deg;
      const lines = [shiftNotes(S.notes, 0, 0, k)];
      lines.push(sec.inv ? invertNotes(S.notes, a0, sec.shift, sec.d, k) : shiftNotes(S.notes, sec.d, sec.shift, k));
      if (sec.third != null) lines.push(shiftNotes(S.notes, 2 * sec.d, sec.thirdShift, k));
      spec.harmony = harmonize(lines, spec.len / 8).map((r) => chord(k, r));
      fix(sec.leader, 'subject', lines[0]);
      fix(sec.follower, sec.inv ? 'inversion' : 'subject', lines[1]);
      if (sec.third != null) fix(sec.third, 'subject', lines[2]);
    } else if (sec.type === 'cadence') {
      const upper = all.filter((v) => v !== 3);
      for (const v of upper) roles[v] = 'free';
      if (sec.pivot) {
        spec.harmony = [chord(k, 3), chord(k, 4, { sev: true }), chord(k, 0), chord(sec.pivot, 4, { sev: true })];
        roles[3] = 'free';
        spec.susForce = [2];
      } else {
        spec.harmony = [chord(k, 3), chord(k, 0), chord(k, 4, { sev: true }), chord(k, 0, { pic: sec.pic })];
        roles[3] = 'pedal';
        spec.pedalMidi = 36 + k.tonic;
        spec.susForce = [4];
      }
      spec.calmEnd = true;
      spec.extendEnd = sec.holdOver === false ? [] : [0, 1, 2, 3].filter((v) => v !== sec.nextFirst);
    }
    return spec;
  }

  // ---------- block composition ----------
  const UPPER_MOT = [0.4, 0, 0, 0.7, 0.9, 1.8, 5, 2.6, 4, 4.5, 7, 7, 4];
  const BASS_MOT = [0.9, 0.2, 0.2, 0.5, 0.6, 0.8, 3, 0.8, 2.2, 2.5, 5, 5, 1.2];
  const motion = (m, bass) => (m > 12 ? 10 : (bass ? BASS_MOT : UPPER_MOT)[m]);
  const DENSITY = [0.35, 0.65, 1, 1.5, 2.2];
  const BEAM = 10;

  function parallelsArr(A, onA, B, onB, from, to) {
    let n = 0;
    for (let i = Math.max(1, from); i <= to; i++) {
      if (!(onA[i] || onB[i])) continue;
      const a0 = A[i - 1], a1 = A[i], b0 = B[i - 1], b1 = B[i];
      if (a0 < 0 || a1 < 0 || b0 < 0 || b1 < 0 || a0 === a1 || b0 === b1) continue;
      const i0 = Math.abs(a0 - b0) % 12, i1 = Math.abs(a1 - b1) % 12;
      if ((i1 === 0 || i1 === 7) && i0 === i1) n++;
    }
    return n;
  }
  const parallels = (samp, onset, a, b, from, to) => parallelsArr(samp[a], onset[a], samp[b], onset[b], from, to) > 0;

  function chooseOctave(notes, v, prev, samp, onset, L) {
    let best = 0, bestC = Infinity;
    const { lo, hi } = VOICES[v];
    const tmpS = new Int16Array(L + 1), tmpOn = new Uint8Array(L + 1);
    for (let k = -3; k <= 3; k++) {
      let c = 0;
      for (const n of notes) {
        const m = n.midi + 12 * k;
        if (m < lo) c += (lo - m) * 3;
        if (m > hi) c += (m - hi) * 3;
      }
      const first = notes[0].midi + 12 * k;
      c += prev != null ? Math.abs(first - prev) * 0.12 : Math.abs(first - center(v)) * 0.08;
      tmpS.fill(-1); tmpOn.fill(0);
      for (const n of notes) {
        for (let i = n.t; i < n.t + n.dur && i < L; i++) tmpS[i + 1] = n.midi + 12 * k;
        if (n.t < L) tmpOn[n.t + 1] = 1;
      }
      for (let w = 0; w < 4; w++) {
        if (w === v) continue;
        let placed = false;
        for (let i = 1; i <= L; i++) {
          const p = samp[w][i], m = tmpS[i];
          if (p < 0) continue;
          placed = true;
          if (m >= 0 && ((w < v && m > p) || (w > v && m < p))) c += 3;
        }
        if (placed) c += parallelsArr(tmpS, tmpOn, samp[w], onset[w], 1, L) * 4;
      }
      if (c < bestC) { bestC = c; best = k; }
    }
    return best;
  }

  function comboCost(cur, prv, free, ch, pcs, prevCh, unitStart, span) {
    let c = 0;
    for (const v of free) {
      for (let w = 0; w < 4; w++) {
        if (w === v || !span[w]) continue;
        if (w > v && cur[v] < span[w][1]) c += 6;
        if (w < v && cur[v] > span[w][0]) c += 6;
      }
    }
    for (const v of free) {
      const p = cur[v], q = prv[v];
      if (q < 0) { c += Math.abs(p - center(v)) * 0.05; continue; }
      c += motion(Math.abs(p - q), v === 3);
      if (unitStart && (q - p === 1 || q - p === 2)) c -= 0.7;
      if (prevCh && sameKey(prevCh.key, ch.key)) {
        const lt = mod(prevCh.key.tonic + 11, 12);
        if ((prevCh.root === 4 || prevCh.root === 6) && mod(q, 12) === lt && (ch.root === 0 || ch.root === 5) && p !== q + 1) c += v === 0 ? 6 : 2.5;
        if (prevCh.sev && prevCh.root !== ch.root && mod(q, 12) === chordPCs(prevCh)[3] && !(q - p === 1 || q - p === 2)) c += 4;
      }
    }
    let top = -1, low = -1;
    for (let a = 0; a < 4; a++) {
      if (cur[a] < 0) continue;
      if (top < 0) top = a;
      if (low < 0 || cur[a] < cur[low]) low = a;
      for (let b = a + 1; b < 4; b++) {
        if (cur[b] < 0) continue;
        if (!free.includes(a) && !free.includes(b)) continue;
        if (cur[a] < cur[b]) c += 24; else if (cur[a] === cur[b]) c += 3;
        if (prv[a] >= 0 && cur[b] > prv[a]) c += 2;
        if (prv[b] >= 0 && cur[a] < prv[b]) c += 2;
        if (b === a + 1 && b < 3 && cur[a] - cur[b] > 12) c += (cur[a] - cur[b] - 12) * 0.6;
        if (prv[a] >= 0 && prv[b] >= 0 && prv[a] !== cur[a] && prv[b] !== cur[b]) {
          const i0 = Math.abs(prv[a] - prv[b]) % 12, i1 = Math.abs(cur[a] - cur[b]) % 12;
          if ((i1 === 0 || i1 === 7) && i0 === i1) c += Math.sign(cur[a] - prv[a]) === Math.sign(cur[b] - prv[b]) ? 30 : 14;
        }
        const iv = mod(cur[a] - cur[b], 12);
        if (!(pcs.includes(mod(cur[a], 12)) && pcs.includes(mod(cur[b], 12)))) {
          if (iv === 1 || iv === 2 || iv === 10 || iv === 11) c += 5;
          else if (iv === 6) c += 1.5;
        }
      }
    }
    // hidden fifths and octaves between the outer voices when the top voice leaps
    if (top >= 0 && low >= 0 && top !== low && (free.includes(top) || free.includes(low)) && prv[top] >= 0 && prv[low] >= 0) {
      const dt = cur[top] - prv[top], dl = cur[low] - prv[low];
      if (dt && dl && Math.sign(dt) === Math.sign(dl) && Math.abs(dt) > 2) {
        const iv = Math.abs(cur[top] - cur[low]) % 12;
        if (iv === 0 || iv === 7) c += 4;
      }
    }
    const count = {};
    for (let v = 0; v < 4; v++) if (cur[v] >= 0) { const pc = mod(cur[v], 12); count[pc] = (count[pc] || 0) + 1; }
    if (!count[pcs[1]]) c += 8;
    if (!count[pcs[0]]) c += 5;
    if (!count[pcs[2]]) c += 0.8;
    if (pcs[3] != null && !count[pcs[3]]) c += 1;
    if ((ch.root === 4 || ch.root === 6) && count[mod(ch.key.tonic + 11, 12)] > 1) c += 6;
    if (low >= 0 && free.includes(low)) {
      const pc = mod(cur[low], 12);
      if (pc === pcs[2]) c += 6;
      else if (pc === pcs[1]) c += 1.6;
      else if (pcs[3] != null && pc === pcs[3]) c += 4;
    }
    return c + R.f() * 0.6;
  }

  function composeBlock(spec, st) {
    const L = spec.len, U = spec.harmony, UL = spec.unitLen || 8;
    const harm = (t) => U[Math.max(0, Math.min(U.length - 1, Math.floor(t / UL)))];
    const lines = [[], [], [], []], samp = [], onset = [];
    for (let v = 0; v < 4; v++) {
      samp.push(new Int16Array(L + 1).fill(-1));
      onset.push(new Uint8Array(L + 1));
      if (spec.roles[v] !== 'rest' && st.sounding[v] && st.last[v] != null) samp[v][0] = st.last[v];
    }
    const write = (v, n) => {
      for (let i = n.t; i < n.t + n.dur && i < L; i++) samp[v][i + 1] = n.midi;
      if (n.t < L) onset[v][n.t + 1] = 1;
    };

    // Fixed lines (subjects, answer, countersubject, sequences), placed by octave.
    for (const fx of spec.fixed) {
      const v = fx.voice;
      let prev = st.last[v];
      for (const seg of fx.segs) {
        if (!seg.notes.length) continue;
        const notes = realize(seg.notes.map((n) => Object.assign({}, n)), harm);
        const k = chooseOctave(notes, v, prev, samp, onset, L);
        for (const n of notes) { n.midi += 12 * k; n.tag = seg.tag; lines[v].push(n); write(v, n); }
        prev = notes[notes.length - 1].midi;
      }
      lines[v].sort((a, b) => a.t - b.t);
    }
    for (let v = 0; v < 4; v++) {
      if (spec.roles[v] !== 'pedal') continue;
      const n = { t: 0, dur: L, midi: spec.pedalMidi, tag: 'pedal' };
      lines[v].push(n); write(v, n);
    }

    // Free voices: beam search over chord tones beat by beat, then embellish.
    const F = [0, 1, 2, 3].filter((v) => spec.roles[v] === 'free');
    if (F.length) {
      const nb = L / 4;
      let beam = [{ cost: 0, prev: F.map((v) => samp[v][0]), node: null }];
      const cur = new Array(4), prv = new Array(4), idx = F.map(() => 0);
      for (let b = 0; b < nb; b++) {
        const t = b * 4, ch = harm(t), pcs = chordPCs(ch), degs = chordDegs(ch);
        const prevCh = b > 0 ? harm(t - 4) : null, unitStart = t % UL === 0;
        const full = F.map((v) => {
          const list = [];
          for (const d of degs) for (let o = -4; o <= 3; o++) {
            const deg = d + 7 * o, midi = degMidi(ch.key, deg) + chordAlt(ch, d);
            if (midi >= VOICES[v].lo && midi <= VOICES[v].hi) list.push({ deg, midi });
          }
          if (!list.length) list.push({ deg: degs[0], midi: degMidi(ch.key, degs[0]) });
          return list;
        });
        const span = [];
        for (let v = 0; v < 4; v++) {
          cur[v] = samp[v][t + 1]; prv[v] = samp[v][t];
          let lo = 999, hi = -1;
          for (let s = t; s < t + 4 && s < L; s++) { const p = samp[v][s + 1]; if (p >= 0) { lo = Math.min(lo, p); hi = Math.max(hi, p); } }
          span.push(F.includes(v) || hi < 0 ? null : [lo, hi]);
        }
        const next = [];
        for (const h of beam) {
          const cands = F.map((v, i) => {
            const ref = h.prev[i] >= 0 ? h.prev[i] : center(v);
            return full[i].slice().sort((x, y) => Math.abs(x.midi - ref) - Math.abs(y.midi - ref)).slice(0, 5);
          });
          const total = cands.reduce((a, c) => a * c.length, 1);
          for (let combo = 0; combo < total; combo++) {
            let x = combo;
            for (let i = 0; i < F.length; i++) { idx[i] = x % cands[i].length; x = Math.floor(x / cands[i].length); }
            for (let i = 0; i < F.length; i++) { cur[F[i]] = cands[i][idx[i]].midi; prv[F[i]] = h.prev[i]; }
            const c = comboCost(cur, prv, F, ch, pcs, prevCh, unitStart, span);
            const pick = F.map((_, i) => cands[i][idx[i]]);
            next.push({ cost: h.cost + c, prev: pick.map((p) => p.midi), node: { parent: h.node, pick } });
          }
        }
        next.sort((a, b2) => a.cost - b2.cost);
        const seen = new Set();
        beam = [];
        for (const n of next) {
          const key = n.prev.join(',');
          if (seen.has(key)) continue;
          seen.add(key);
          beam.push(n);
          if (beam.length >= BEAM) break;
        }
      }
      const choice = F.map(() => new Array(nb));
      let node = beam[0].node;
      for (let b = nb - 1; b >= 0; b--) {
        const ch = harm(b * 4);
        node.pick.forEach((cd, i) => { choice[i][b] = { deg: cd.deg, midi: cd.midi, key: ch.key, ch }; });
        node = node.parent;
      }
      F.forEach((v, i) => {
        for (let b = 0; b < nb; b++) write(v, { t: b * 4, dur: 4, midi: choice[i][b].midi });
      });

      const okRange = (v, from, to) => {
        to = Math.min(L, to);
        for (let w = 0; w < 4; w++) {
          if (w === v) continue;
          if (parallels(samp, onset, v, w, from, to)) return false;
          for (let s = from; s <= to; s++) {
            const p = samp[w][s], q = samp[v][s];
            if (p < 0 || q < 0) continue;
            if ((w < v && q > p) || (w > v && q < p)) return false;
          }
        }
        return true;
      };
      const maxBusy = (v, t) => {
        let m = 0;
        for (let w = 0; w < 4; w++) {
          if (w === v || F.includes(w)) continue;
          let c = 0;
          for (let s = t; s < t + 4 && s < L; s++) c += onset[w][s + 1];
          m = Math.max(m, c);
        }
        return m;
      };
      // Tie the previous note over the beat and resolve it down by step.
      const trySus = (v, t, last, c0, nextSame) => {
        if (!last || last.t + last.dur !== t || last.midi === c0.midi) return false;
        const hold = nextSame ? 4 : 2;
        const susPc = mod(last.midi, 12), resPc = mod(c0.midi, 12);
        let low = -1;
        for (let w = 0; w < 4; w++) if (w !== v && samp[w][t + 1] >= 0 && (low < 0 || samp[w][t + 1] < samp[low][t + 1])) low = w;
        for (let w = 0; w < 4; w++) {
          if (w === v || w === low) continue;
          for (let s = t; s < t + hold && s < L; s++) {
            const p = samp[w][s + 1];
            if (p < 0) continue;
            const iv = mod(susPc - p, 12);
            if (iv === 1 || iv === 11 || mod(p, 12) === resPc) return false;
          }
        }
        const saved = samp[v].slice(t + 1, t + 5), savedOn = onset[v].slice(t + 1, t + 5);
        for (let s = t; s < t + hold && s < L; s++) samp[v][s + 1] = last.midi;
        onset[v][t + 1] = 0;
        if (!nextSame && t + 2 < L) onset[v][t + 3] = 1;
        if (okRange(v, t + 1, t + 5)) { last.dur += hold; return true; }
        samp[v].set(saved, t + 1);
        onset[v].set(savedOn, t + 1);
        return false;
      };
      const dn = DENSITY[spec.density == null ? 2 : spec.density] || 1;
      for (const i of R.shuffle(F.map((_, i) => i))) {
        const v = F[i], seq = [];
        let plannedSus = -1;
        for (let b = 0; b < nb; b++) {
          const c0 = choice[i][b], c1 = choice[i][b + 1], t = b * 4;
          if (b === plannedSus) {
            const nextSame = !!c1 && c1.midi === c0.midi && R.chance(0.5);
            if (trySus(v, t, seq[seq.length - 1], c0, nextSame)) {
              if (!nextSame) seq.push({ t: t + 2, dur: 2, deg: c0.deg, key: c0.key, midi: c0.midi });
              continue;
            }
          }
          let notes = [{ t, dur: 4, deg: c0.deg, key: c0.key, midi: c0.midi }];
          let wantSus = false;
          if (c1 && sameKey(c0.key, c1.key) && ((b + 1) * 4) % UL === 0) {
            const drop = c0.midi - c1.midi;
            if (drop >= 1 && drop <= 2 && !chordPCs(c1.ch).includes(mod(c0.midi, 12))) {
              const p = spec.susForce && spec.susForce.includes(b + 1) ? 0.9 : spec.susProb;
              if (R.chance(p)) { wantSus = true; plannedSus = b + 1; }
            }
          }
          if (!wantSus && c1 && sameKey(c0.key, c1.key) && !(spec.calmEnd && t >= L - 8)) {
            const busy = maxBusy(v, t);
            let n;
            if (busy >= 3) n = R.chance(0.1 * dn) ? 2 : 1;
            else if (busy === 2) n = R.chance(Math.min(0.9, 0.45 * dn)) ? 2 : 1;
            else n = R.weighted([[1, 0.2 / dn], [2, 0.55], [3, 0.15 * dn], [4, (spec.running ? 0.4 : 0.15) * dn]]);
            if (n > 1) {
              const cset = new Set(chordDegs(c0.ch));
              const durs = n === 2 ? [2, 2] : n === 3 ? R.pick([[2, 1, 1], [1, 1, 2]]) : [1, 1, 1, 1];
              for (const fs of fills(c0.deg, c1.deg, n, cset, 4)) {
                const cand = [];
                let tt = t;
                fs.forEach((deg, j) => { cand.push({ t: tt, dur: durs[j], deg, key: c0.key }); tt += durs[j]; });
                realize(cand.concat([{ t: t + 4, dur: 4, deg: c1.deg, key: c1.key }]), harm);
                cand[0].midi = c0.midi;
                if (cand.some((x) => x.midi < VOICES[v].lo - 2 || x.midi > VOICES[v].hi + 2)) continue;
                const saved = samp[v].slice(t + 1, t + 5), savedOn = onset[v].slice(t + 1, t + 5);
                for (const x of cand) write(v, x);
                if (okRange(v, t + 2, t + 5)) { notes = cand; break; }
                samp[v].set(saved, t + 1);
                onset[v].set(savedOn, t + 1);
              }
            }
          }
          seq.push(...notes);
        }
        for (const n of seq) {
          const p = lines[v][lines[v].length - 1];
          if (p && p.midi === n.midi && p.t + p.dur === n.t && n.dur === 4 && p.dur >= 4 && R.chance(0.75)) p.dur += n.dur;
          else lines[v].push(Object.assign({ tag: 'free' }, n));
        }
      }
    }

    for (let v = 0; v < 4; v++) {
      const ln = lines[v];
      if (ln.length) {
        const last = ln[ln.length - 1];
        st.last[v] = last.midi;
        st.sounding[v] = last.t + last.dur >= L;
      } else st.sounding[v] = false;
    }
    if (spec.extendEnd) {
      for (const v of spec.extendEnd) {
        const last = lines[v][lines[v].length - 1];
        if (last && last.t + last.dur >= L) last.dur += 4;
      }
    }
    const out = [];
    for (let v = 0; v < 4; v++) for (const n of lines[v]) out.push({ start: n.t, dur: n.dur, midi: n.midi, voice: v, tag: n.tag });
    return out;
  }

  // ---------- the endless stream ----------
  const START_KEYS = [{ tonic: 2, mode: 'minor' }, { tonic: 7, mode: 'minor' }, { tonic: 0, mode: 'minor' }, { tonic: 9, mode: 'minor' }, { tonic: 2, mode: 'major' }, { tonic: 5, mode: 'major' }];
  const freshState = () => ({ last: [null, null, null, null], sounding: [false, false, false, false] });

  class FugueStream {
    // opts: {seed} for a random stream, or {token} to start at a shared fugue.
    constructor(opts) {
      opts = typeof opts === 'number' ? { seed: opts } : opts || {};
      this.st = freshState();
      this.step = 0;
      this.fugueNo = 0;
      this.errors = 0;
      this.steer = {};
      this.density = 2;
      this.pending = null;
      let params = opts.token ? parseToken(opts.token) : null;
      if (params) this.density = params.density;
      else {
        const s = (opts.seed >>> 0) || 1;
        reseed(s);
        params = { seed: hash2(s, 0x5eed), key: R.pick(START_KEYS) };
      }
      this.fugue = this._plan(params);
      this.secIdx = 0;
    }
    _plan(params) {
      let f = null;
      for (let i = 0; i < 6 && !f; i++) {
        const p = i ? Object.assign({}, params, { seed: hash2(params.seed, i) }) : params;
        try { f = planFugue(p); } catch (e) { this.errors++; if (typeof console !== 'undefined') console.warn('plan failed', e); }
      }
      if (!f) throw new Error('could not plan a fugue');
      f.no = ++this.fugueNo;
      return f;
    }
    // Ask the current fugue to wind down: one episode home, then the cadence.
    requestNewFugue() {
      const fg = this.fugue, secs = fg.sections;
      const cad = secs.findIndex((s) => s.type === 'cadence');
      if (this.secIdx >= cad - 1) return false;
      const lead = fg.voices[0], second = fg.voices[fg.voices.length - 2];
      const home = { type: 'episode', to: fg.key, key: fg.key, units: 4, lead, second, rest: null, swap: false, title: 'Episode' };
      fg.sections = secs.slice(0, this.secIdx).concat([home, secs[cad]]);
      return true;
    }
    _nextParams(fg, sec) {
      if (this.pending) { const p = Object.assign({}, this.pending); this.pending = null; return p; }
      reseed(hash2(fg.params.seed, 0xcade));
      const autoKey = nextKey(sec.key, sec.pic);
      const s = this.steer || {};
      return {
        seed: hash2(fg.params.seed, 0x9e37), key: s.key || autoKey, character: s.character || null, voices: s.voices || null,
        form: s.form || null, devices: s.devices == null ? 7 : s.devices, density: this.density,
      };
    }
    next() {
      let block;
      try { block = this._compose(); } catch (e) {
        this.errors++;
        if (typeof console !== 'undefined') console.warn('block failed; playing a plain cadence instead', e);
        block = this._fallback();
      }
      block.notes = block.notes.filter((n) => Number.isFinite(n.midi) && Number.isFinite(n.start) && n.dur > 0);
      // For articulation: the interval to the next note in the same voice, when it follows directly.
      for (let v = 0; v < 4; v++) {
        const vn = block.notes.filter((n) => n.voice === v).sort((a, b) => a.start - b.start);
        vn.forEach((n, i) => { const q = vn[i + 1]; n.leap = q && q.start === n.start + n.dur ? Math.abs(q.midi - n.midi) : null; });
      }
      return block;
    }
    _compose() {
      const fg = this.fugue;
      if (this.secIdx >= fg.sections.length) throw new Error('ran past the plan');
      const sec = fg.sections[this.secIdx];
      if (this.secIdx === 0) this.st = freshState();
      let nextFugue = null;
      if (sec.type === 'cadence') {
        const held = chordPCs(chord(sec.key, 0, { pic: sec.pic }));
        const p = this._nextParams(fg, sec);
        if (!p.startMask) p.startMask = maskForHeld(p.key, held);
        nextFugue = this._plan(p);
        sec.nextFirst = nextFugue.order[0];
        const firstPc = mod(degMidi(nextFugue.key, nextFugue.subject.notes[0].deg), 12);
        if (held.includes(firstPc)) { sec.pivot = null; sec.holdOver = true; }
        else {
          sec.pivot = nextFugue.key;
          sec.holdOver = chordPCs(chord(nextFugue.key, 4, { sev: true })).includes(firstPc);
        }
      }
      reseed(hash2(fg.params.seed, 1000 + this.secIdx));
      const spec = buildSpec(sec, fg, this.density);
      const notes = composeBlock(spec, this.st);
      const block = {
        start: this.step, len: spec.len, bpm: fg.bpm, rit: sec.type === 'cadence', fugue: fg, secIdx: this.secIdx,
        sec, key: spec.key, notes: notes.map((n) => Object.assign(n, { start: n.start + this.step })),
      };
      this.step += spec.len;
      this.secIdx++;
      if (nextFugue) { this.fugue = nextFugue; this.secIdx = 0; }
      return block;
    }
    _fallback() {
      const old = this.fugue, key = (old && old.key) || { tonic: 2, mode: 'minor' };
      const notes = [];
      [0, 3, 4, 0].forEach((r, u) => {
        const pcs = chordPCs(chord(key, r));
        for (let v = 0; v < 4; v++) {
          let best = null;
          for (let m = VOICES[v].lo; m <= VOICES[v].hi; m++) {
            const pc = mod(m, 12);
            if ((v === 3 ? pc === pcs[0] : pcs.includes(pc)) && (best == null || Math.abs(m - center(v)) < Math.abs(best - center(v)))) best = m;
          }
          notes.push({ start: this.step + u * 8, dur: 8, midi: best, voice: v, tag: 'free' });
          this.st.last[v] = best;
        }
      });
      this.st.sounding = [true, true, true, true];
      const sec = { type: 'cadence', key, title: 'Cadence' };
      const block = { start: this.step, len: 32, bpm: (old && old.bpm) || 66, rit: true, fugue: old, secIdx: -1, sec, key, notes };
      this.step += 32;
      const seed = old && old.params ? hash2(old.params.seed, 0xfa11) : 7;
      this.fugue = this._plan({ seed, key });
      this.secIdx = 0;
      return block;
    }
  }

  return {
    FugueStream, VOICES, keyName, CHARACTERS, tokenFor, parseToken, sectionLength, stepBpm, expression, timing, rubato,
    _internal: { planFugue, composeBlock, buildSpec, genSubject, genCS, harmonize, strettoOptions, realize, tonalAnswer, hash2 },
  };
});

#!/usr/bin/env node
// Fugue State regression suite. Run: node test/soak.js
// Checks continuity, crash-safety, voice-leading thresholds, determinism of shared
// tokens, coverage of every fugal device, and the MIDI/zip export.
'use strict';
const E = require('../engine.js');
const X = require('../export.js');
const fs = require('fs'), os = require('os'), path = require('path');
const { execFileSync } = require('child_process');

let failures = 0;
function check(name, ok, info) {
  console.log((ok ? 'ok   ' : 'FAIL ') + name + (info ? ` (${info})` : ''));
  if (!ok) failures++;
}

const KEYS = [];
for (let t = 0; t < 12; t++) for (const mode of ['major', 'minor']) KEYS.push({ tonic: t, mode });
let rs = 12345;
const rand = () => ((rs = (Math.imul(rs, 1103515245) + 12345) >>> 0) / 4294967296);
const pick = (a) => a[Math.floor(rand() * a.length)];

function randomSteer() {
  return {
    key: rand() < 0.5 ? pick(KEYS) : null,
    character: rand() < 0.5 ? pick(['stately', 'running', 'dotted']) : null,
    voices: rand() < 0.5 ? pick([3, 4]) : null,
    form: rand() < 0.5 ? pick(['single', 'double']) : null,
    devices: rand() < 0.3 ? Math.floor(rand() * 8) : 7,
  };
}

// Play a stream for n fugues, recording every note into one continuous grid.
function run(stream, fugues, opts) {
  opts = opts || {};
  const stats = { blocks: 0, steps: 0, gaps: 0, bad: 0, out: 0, parallels: 0, crossings: 0, cover: {} };
  const notes = [];
  let prevEnd = 0;
  const seen = new Set();
  const bump = (k) => { stats.cover[k] = (stats.cover[k] || 0) + 1; };
  while (stream.fugueNo <= fugues) {
    if (opts.chaos && rand() < 0.04) stream.requestNewFugue();
    if (opts.chaos && rand() < 0.03) stream.steer = randomSteer();
    if (opts.chaos && rand() < 0.03) stream.density = Math.floor(rand() * 5);
    const b = stream.next();
    stats.blocks++;
    if (b.start !== prevEnd) throw new Error(`block starts at ${b.start}, previous ended at ${prevEnd}`);
    if (b.len % 4) throw new Error(`block length ${b.len} is not whole beats`);
    prevEnd = b.start + b.len;
    const s = b.sec, fg = b.fugue;
    bump(s.type === 'entry' ? 'entry:' + s.form : s.type);
    if (s.type === 'stretto') { if (s.third != null) bump('stretto:three'); if (s.inv) bump('stretto:inverted'); }
    if (s.type === 'cadence' && s.pivot) bump('cadence:pivot');
    if (fg && !seen.has(fg)) { seen.add(fg); bump('fugue:' + fg.form); bump('voices:' + fg.voices.length); if (fg.answer) bump('answer:tonal'); }
    // Suspension signature: a free note tied over a beat, released 2 steps later onto a note
    // a step below in the same voice. (Quarter-length ties can't be told from merged ties.)
    for (let v = 0; v < 4; v++) {
      const vn = b.notes.filter((n) => n.voice === v).sort((x, y) => x.start - y.start);
      let found = false;
      for (let j = 0; j + 1 < vn.length; j++) {
        const p = vn[j], q = vn[j + 1], beat = p.start + p.dur - 2;
        if (p.tag === 'free' && beat % 4 === 0 && p.start < beat && q.start === p.start + p.dur && (p.midi - q.midi === 1 || p.midi - q.midi === 2)) { bump('suspension'); found = true; }
      }
      if (found && s.type === 'cadence') bump('suspension:cadence-voice');
    }
    if (s.type === 'cadence' && b.notes.some((p) => p.tag === 'free' && (p.start + p.dur - 2) % 4 === 0 && p.start < p.start + p.dur - 2 &&
      b.notes.some((q) => q.voice === p.voice && q.start === p.start + p.dur && (p.midi - q.midi === 1 || p.midi - q.midi === 2)))) bump('suspension:cadence-block');
    for (const n of b.notes) {
      if (![n.midi, n.start, n.dur].every(Number.isFinite) || n.dur <= 0) { stats.bad++; continue; }
      const V = E.VOICES[n.voice];
      if (n.midi < V.lo - 5 || n.midi > V.hi + 5) stats.out++;
      notes.push(n);
    }
  }
  const end = prevEnd;
  const grid = [0, 1, 2, 3].map(() => new Int16Array(end).fill(-1));
  const on = [0, 1, 2, 3].map(() => new Uint8Array(end));
  const cover = new Uint8Array(end);
  for (const n of notes) {
    for (let i = n.start; i < n.start + n.dur && i < end; i++) { cover[i] = 1; grid[n.voice][i] = n.midi; }
    if (n.start < end) on[n.voice][n.start] = 1;
  }
  for (let i = 0; i < end; i++) if (!cover[i]) stats.gaps++;
  for (let a = 0; a < 4; a++) for (let c = a + 1; c < 4; c++) for (let i = 1; i < end; i++) {
    const a0 = grid[a][i - 1], a1 = grid[a][i], b0 = grid[c][i - 1], b1 = grid[c][i];
    if (a1 >= 0 && b1 >= 0 && a1 < b1) stats.crossings++;
    if (!(on[a][i] || on[c][i])) continue;
    if (a0 < 0 || a1 < 0 || b0 < 0 || b1 < 0 || a0 === a1 || b0 === b1) continue;
    const i0 = Math.abs(a0 - b0) % 12, i1 = Math.abs(a1 - b1) % 12;
    if ((i1 === 0 || i1 === 7) && i0 === i1) stats.parallels++;
  }
  stats.steps = end;
  stats.errors = stream.errors;
  return stats;
}

const t0 = Date.now();

// 1. Breadth: many seeds, with steering, density changes and new-fugue requests mixed in.
const total = { steps: 0, gaps: 0, bad: 0, out: 0, parallels: 0, crossings: 0, errors: 0, cover: {} };
let thrown = 0;
for (let i = 0; i < 50; i++) {
  try {
    const st = run(new E.FugueStream({ seed: 1000 + i * 7919 }), 6, { chaos: i % 2 === 1 });
    for (const k of ['steps', 'gaps', 'bad', 'out', 'parallels', 'crossings', 'errors']) total[k] += st[k];
    for (const [k, v] of Object.entries(st.cover)) total.cover[k] = (total.cover[k] || 0) + v;
  } catch (e) { thrown++; console.log('  seed', 1000 + i * 7919, e.stack); }
}
check('breadth: no exceptions', thrown === 0, `${thrown} streams threw`);
check('breadth: no recovered block failures', total.errors === 0, `${total.errors} fallbacks`);
check('breadth: no silent steps', total.gaps === 0, `${total.gaps} of ${total.steps}`);
check('breadth: no invalid notes', total.bad === 0);
check('breadth: notes within voice ranges', total.out / total.steps < 0.002, `${total.out} outliers`);
const parRate = total.steps / Math.max(1, total.parallels);
check('voice leading: parallel 5ths/8ves at most 1 per 400 steps', parRate >= 400, `1 per ${Math.round(parRate)} steps`);
const crossRate = total.crossings / total.steps;
check('voice leading: crossings under 1% of voice-pair steps', crossRate < 0.01, (crossRate * 100).toFixed(2) + '%');
const need = ['entry:subject', 'entry:answer', 'entry:inversion', 'entry:augmentation', 'entry:diminution', 'entry:subject2', 'entry:combined',
  'episode', 'dompedal', 'stretto', 'stretto:three', 'stretto:inverted', 'cadence', 'cadence:pivot', 'fugue:double', 'fugue:single', 'voices:3', 'voices:4', 'answer:tonal'];
const missing = need.filter((k) => !(total.cover[k] >= 3));
const sus = total.cover.suspension || 0, cadB = total.cover['suspension:cadence-block'] || 0, cads = total.cover.cadence || 1;
check('suspensions: at least 1 per 12 bars, and in 60% of cadences', sus / (total.steps / 16) >= 1 / 12 && cadB / cads >= 0.6, `${sus} suspensions, about 1 per ${Math.round(total.steps / Math.max(1, sus) / 16)} bars; cadences with one: ${cadB}/${cads} (${Math.round(100 * cadB / cads)}%)`);
check('coverage: every device composed at least 3 times', missing.length === 0, missing.length ? 'missing ' + missing.join(', ') : Object.entries(total.cover).map(([k, v]) => k + '=' + v).join(' '));

// 2. Depth: one stream two hundred fugues long, with chaos.
try {
  const st = run(new E.FugueStream({ seed: 4242 }), 200, { chaos: true });
  check('depth: 200 fugues without gaps or fallbacks', st.gaps === 0 && st.errors === 0 && st.bad === 0, `${st.blocks} blocks, ${st.steps} steps, ${(st.steps / 4 / 66 / 60).toFixed(1)} h at ♩=66`);
} catch (e) { check('depth: 200 fugues', false, e.message); }

// 3. Determinism: a fugue reached mid-stream equals the same fugue started from its token.
const norm = (blocks) => JSON.stringify(blocks.map((b) => [b.len, b.sec.title, b.notes.map((n) => [n.start - blocks[0].start, n.dur, n.midi, n.voice, n.tag])]));
let detOk = 0;
for (let i = 0; i < 6; i++) {
  const a = new E.FugueStream({ seed: 77 + i });
  while (!(a.fugue.no === 3 && a.secIdx === 0)) a.next();
  const fgA = a.fugue, token = fgA.token, A = [];
  while (a.fugue === fgA) A.push(a.next());
  const b = new E.FugueStream({ token }), fgB = b.fugue, B = [];
  while (b.fugue === fgB) B.push(b.next());
  if (norm(A) === norm(B)) detOk++;
  else console.log('  mismatch for token', token);
}
check('determinism: token replays the fugue note for note', detOk === 6, `${detOk}/6`);

// 4. Tokens round-trip; junk is rejected.
let tokOk = true;
for (let i = 0; i < 200; i++) {
  const p = { seed: Math.floor(rand() * 4294967296), key: pick(KEYS), character: pick(['stately', 'running', 'dotted']), voices: pick([3, 4]),
    form: pick(['single', 'double']), startMask: 1 + Math.floor(rand() * 7), devices: Math.floor(rand() * 8), density: Math.floor(rand() * 5) };
  const back = E.parseToken(E.tokenFor(p));
  if (JSON.stringify(back) !== JSON.stringify(p)) { tokOk = false; console.log('  token mismatch', E.tokenFor(p)); break; }
}
check('tokens: encode/decode round trip', tokOk);
check('tokens: junk rejected', ['', 'f-', 'f-zz-2mr4s77', 'f-zz-2xr4s772', 'hello', 'f-abc-2mr4s7724', 'f-abc-cmr4s772'].every((t) => E.parseToken(t) === null));

// 5. Humanization: bounded, deterministic, absent in strict mode.
{
  const s1 = new E.FugueStream({ seed: 31337 }), bl = [];
  while (s1.fugueNo <= 2) bl.push(s1.next());
  let ok = true, strictOk = true, varied = new Set(), worst = '';
  for (const b of bl) for (const n of b.notes) {
    for (const amt of [0.6, 1.1]) {
      const e = E.expression(n, b, amt), t = E.timing(n, b, amt), r = E.rubato(b, n.start, amt);
      if (!(e >= 0.6 && e <= 1.4 && Math.abs(t.dt) <= 0.03 && t.gate >= 0.75 && t.gate <= 1.06 && Math.abs(t.cents) <= 8 && r >= 0.9 && r <= 1.12)) { ok = false; worst = JSON.stringify({ e, t, r, tag: n.tag }); }
      if (amt === 0.6) varied.add(Math.round(e * 100));
    }
    const z = E.timing(n, b, 0);
    if (E.expression(n, b, 0) !== 1 || z.dt !== 0 || z.gate !== 1 || E.rubato(b, n.start, 0) !== 1) strictOk = false;
  }
  check('humanization: within musical bounds', ok, worst || `${varied.size} distinct dynamic levels`);
  check('humanization: strict mode is exactly on the grid', strictOk);
  const s2 = new E.FugueStream({ seed: 31337 }), bl2 = [];
  while (s2.fugueNo <= 2) bl2.push(s2.next());
  const sig = (bs) => bs.map((b) => b.notes.map((n) => [E.expression(n, b, 1.1).toFixed(5), E.timing(n, b, 1.1).dt.toFixed(6), E.rubato(b, n.start, 1.1).toFixed(5)]).join()).join('|');
  check('humanization: the same fugue is performed the same way', sig(bl) === sig(bl2));
}

// 5. Export: the zip passes `unzip -t` and the MIDI inside parses.
try {
  const s = new E.FugueStream({ seed: 99 });
  const out = X.fugueZip(E, s.fugue.token, { instrument: 'strings', link: 'https://example.invalid/#' + s.fugue.token, feel: 0.6 });
  const file = path.join(os.tmpdir(), 'fugue-state-test.zip');
  fs.writeFileSync(file, out.data);
  let unzipOk = true;
  try { execFileSync('unzip', ['-tq', file]); } catch (e) { unzipOk = false; }
  check('export: zip passes unzip -t', unzipOk, out.filename);
  const z = out.data, at = Buffer.from(z).indexOf('MThd');
  const dv = new DataView(z.buffer, z.byteOffset + at);
  const hdrLen = dv.getUint32(4), format = dv.getUint16(8), ntr = dv.getUint16(10);
  let p = 8 + hdrLen, tracks = 0, okChunks = true;
  while (tracks < ntr) {
    const id = String.fromCharCode(...z.slice(at + p, at + p + 4));
    if (id !== 'MTrk') { okChunks = false; break; }
    p += 8 + dv.getUint32(p + 4);
    tracks++;
  }
  check('export: MIDI header and track chunks parse', hdrLen === 6 && format === 1 && ntr >= 4 && okChunks, `${ntr} tracks`);
  const vels = new Set();
  for (let i = at; i + 2 < z.length; i++) if ((z[i] & 0xf0) === 0x90 && z[i + 1] < 128 && z[i + 2] > 0 && z[i + 2] < 128) vels.add(z[i + 2]);
  check('export: MIDI velocities carry the phrasing', vels.size >= 12, `${vels.size} distinct velocities`);
} catch (e) { check('export', false, e.stack); }

console.log(`\n${failures ? failures + ' FAILED' : 'all passed'} in ${((Date.now() - t0) / 1000).toFixed(1)}s`);
process.exit(failures ? 1 : 0);

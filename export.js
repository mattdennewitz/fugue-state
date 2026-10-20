// Fugue State — exports. Pure JS (no DOM): a format-1 MIDI writer, a stored (uncompressed)
// zip writer, and a plain-text analysis of one fugue. Runs in the page and in Node.
(function (root, factory) {
  const api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.FugueExport = api;
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  const PPQ = 480, TICKS_PER_STEP = PPQ / 4;
  const enc = (s) => new TextEncoder().encode(s);

  // ---------- MIDI ----------
  function vlq(n) {
    const out = [n & 0x7f];
    while ((n >>>= 7)) out.unshift((n & 0x7f) | 0x80);
    return out;
  }
  const u32 = (n) => [(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255];
  const u16 = (n) => [(n >>> 8) & 255, n & 255];
  const meta = (type, bytes) => [0xff, type, ...vlq(bytes.length), ...bytes];
  const text = (type, s) => meta(type, Array.from(enc(s)));

  function chunk(type, data) { return [...Array.from(enc(type)), ...u32(data.length), ...data]; }
  function track(events) {
    events.sort((a, b) => a.tick - b.tick || a.order - b.order);
    const out = [];
    let last = 0;
    for (const e of events) { out.push(...vlq(e.tick - last), ...e.bytes); last = e.tick; }
    out.push(0, ...meta(0x2f, []));
    return chunk('MTrk', out);
  }

  // Key signature: sharps (+) or flats (-) for each major tonic pitch class.
  const SF_MAJOR = [0, -5, 2, -3, 4, -1, 6, 1, -4, 3, -2, 5];
  function keySig(key) {
    const sf = key.mode === 'major' ? SF_MAJOR[key.tonic] : SF_MAJOR[(key.tonic + 3) % 12];
    return meta(0x59, [sf & 0xff, key.mode === 'minor' ? 1 : 0]);
  }

  const PROGRAMS = {
    organ: [19, 19, 19, 19],        // church organ
    harpsichord: [6, 6, 6, 6],
    strings: [40, 40, 41, 42],      // violin, violin, viola, cello
    sine: [73, 73, 73, 73],         // flute is General MIDI's nearest thing to a sine
  };
  const VELOCITY = { subject: 100, answer: 100, inversion: 100, subject2: 100, motif: 92, cs: 86, pedal: 80, free: 72 };

  // blocks: one fugue's composed blocks (from FugueStream.next()); E: FugueEngine.
  function buildMidi(E, blocks, opts) {
    opts = opts || {};
    const origin = blocks[0].start;
    const T = (step) => Math.round((step - origin) * TICKS_PER_STEP);
    const fg = blocks[0].fugue;
    const programs = PROGRAMS[opts.instrument] || PROGRAMS.organ;

    const ctl = [];
    let order = 0;
    const push = (list, tick, bytes) => list.push({ tick, bytes, order: order++ });
    push(ctl, 0, text(0x03, 'Fugue in ' + E.keyName(fg.key)));
    push(ctl, 0, meta(0x58, [4, 2, 24, 8]));
    let lastBpm = null, lastKey = null;
    for (const b of blocks) {
      const keyStr = b.key ? b.key.tonic + b.key.mode : null;
      if (b.key && keyStr !== lastKey) { push(ctl, T(b.start), keySig(b.key)); lastKey = keyStr; }
      push(ctl, T(b.start), text(0x06, b.sec.title || b.sec.type));
      for (let s = b.start; s < b.start + b.len; s++) {
        const bpm = Math.round(E.stepBpm(b, s) * 10) / 10;
        if (bpm !== lastBpm) { push(ctl, T(s), meta(0x51, u32(Math.round(60e6 / bpm)).slice(1))); lastBpm = bpm; }
      }
    }
    const tracks = [track(ctl)];
    const feel = opts.feel == null ? 0 : opts.feel;
    for (let v = 0; v < 4; v++) {
      const notes = [];
      for (const b of blocks) for (const n of b.notes) if (n.voice === v) notes.push([n, b]);
      if (!notes.length) continue;
      const ev = [];
      push(ev, 0, text(0x03, E.VOICES[v].name));
      push(ev, 0, [0xc0 | v, programs[v]]);
      for (const [n, b] of notes) {
        // dynamics follow the chosen feel; timing stays on the grid so notation imports cleanly
        const vel = Math.max(1, Math.min(127, Math.round((VELOCITY[n.tag] || 72) * E.expression(n, b, feel))));
        // note-offs sort before note-ons on the same tick so repeated pitches re-strike
        ev.push({ tick: T(n.start + n.dur), bytes: [0x80 | v, n.midi, 0], order: -1 });
        ev.push({ tick: T(n.start), bytes: [0x90 | v, n.midi, vel], order: order++ });
      }
      tracks.push(track(ev));
    }
    const header = chunk('MThd', [...u16(1), ...u16(tracks.length), ...u16(PPQ)]);
    return new Uint8Array([].concat(header, ...tracks));
  }

  // ---------- zip (stored, no compression) ----------
  const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
      t[n] = c >>> 0;
    }
    return t;
  })();
  function crc32(u8) {
    let c = 0xffffffff;
    for (let i = 0; i < u8.length; i++) c = CRC_TABLE[(c ^ u8[i]) & 255] ^ (c >>> 8);
    return (c ^ 0xffffffff) >>> 0;
  }
  function zip(files, when) {
    const d = when || new Date();
    const time = (d.getHours() << 11) | (d.getMinutes() << 5) | (d.getSeconds() >> 1);
    const date = ((Math.max(1980, d.getFullYear()) - 1980) << 9) | ((d.getMonth() + 1) << 5) | d.getDate();
    const parts = [], central = [];
    let offset = 0;
    for (const f of files) {
      const name = enc(f.name), data = f.data, crc = crc32(data);
      const local = new Uint8Array(30 + name.length), lv = new DataView(local.buffer);
      lv.setUint32(0, 0x04034b50, true); lv.setUint16(4, 20, true); lv.setUint16(6, 0x0800, true); lv.setUint16(8, 0, true);
      lv.setUint16(10, time, true); lv.setUint16(12, date, true); lv.setUint32(14, crc, true);
      lv.setUint32(18, data.length, true); lv.setUint32(22, data.length, true); lv.setUint16(26, name.length, true); lv.setUint16(28, 0, true);
      local.set(name, 30);
      const cen = new Uint8Array(46 + name.length), cv = new DataView(cen.buffer);
      cv.setUint32(0, 0x02014b50, true); cv.setUint16(4, 20, true); cv.setUint16(6, 20, true); cv.setUint16(8, 0x0800, true);
      cv.setUint16(10, 0, true); cv.setUint16(12, time, true); cv.setUint16(14, date, true); cv.setUint32(16, crc, true);
      cv.setUint32(20, data.length, true); cv.setUint32(24, data.length, true); cv.setUint16(28, name.length, true);
      cv.setUint32(42, offset, true);
      cen.set(name, 46);
      parts.push(local, data);
      central.push(cen);
      offset += local.length + data.length;
    }
    const cdSize = central.reduce((a, c) => a + c.length, 0);
    const end = new Uint8Array(22), ev = new DataView(end.buffer);
    ev.setUint32(0, 0x06054b50, true); ev.setUint16(8, files.length, true); ev.setUint16(10, files.length, true);
    ev.setUint32(12, cdSize, true); ev.setUint32(16, offset, true);
    const all = parts.concat(central, [end]);
    const out = new Uint8Array(all.reduce((a, p) => a + p.length, 0));
    let o = 0;
    for (const p of all) { out.set(p, o); o += p.length; }
    return out;
  }

  // ---------- analysis ----------
  const NOTE = ['C', 'C♯', 'D', 'E♭', 'E', 'F', 'F♯', 'G', 'A♭', 'A', 'B♭', 'B'];
  const noteName = (m) => NOTE[m % 12] + (Math.floor(m / 12) - 1);
  function analysis(E, blocks, opts) {
    const fg = blocks[0].fugue, origin = blocks[0].start;
    const where = (s) => {
      const rel = s - origin;
      return 'bar ' + (Math.floor(rel / 16) + 1) + (rel % 16 ? ', beat ' + (Math.floor((rel % 16) / 4) + 1) : '');
    };
    const lines = [];
    lines.push(`Fugue in ${E.keyName(fg.key)}`);
    lines.push(`${fg.character} subject, ${fg.voices.length} voices${fg.form === 'double' ? ', double fugue' : ''}, ♩ = ${fg.bpm}`);
    lines.push(`Composed by Fugue State. Token: ${fg.token}`);
    if (opts && opts.link) lines.push(`Replay: ${opts.link}`);
    lines.push('');
    const first = blocks[0].notes.filter((n) => n.tag === 'subject').sort((a, b) => a.start - b.start);
    lines.push('Subject: ' + first.map((n) => noteName(n.midi)).join(' '));
    if (fg.answer) lines.push('The answer is tonal: its opening dominant is answered by the tonic.');
    lines.push('');
    lines.push('Form');
    for (const b of blocks) {
      const s = b.sec;
      let detail = s.title || s.type;
      if (s.type === 'episode') detail = 'Episode, to ' + E.keyName(s.to);
      if (s.type === 'cadence' && s.pivot) detail += ', pivoting to ' + E.keyName(s.pivot);
      else if (s.type === 'entry' && s.group === 'exposition') detail += ' (' + E.keyName(s.key) + ')';
      lines.push(`  ${where(b.start).padEnd(16)} ${detail}`);
    }
    return lines.join('\n') + '\n';
  }

  // Re-compose one fugue from its token in a throwaway stream and pack it.
  function fugueZip(E, token, opts) {
    opts = opts || {};
    const fs = new E.FugueStream({ token });
    const fg = fs.fugue, blocks = [];
    let guard = 0;
    while (fs.fugue === fg && guard++ < 200) blocks.push(fs.next());
    const slug = E.keyName(fg.key).toLowerCase().replace('♯', '-sharp').replace('♭', '-flat').replace(/\s+/g, '-');
    const base = `fugue-in-${slug}-${token}`;
    const midi = buildMidi(E, blocks, opts);
    const data = zip([
      { name: base + '.mid', data: midi },
      { name: base + '.txt', data: enc(analysis(E, blocks, opts)) },
    ]);
    return { filename: base + '.zip', data, blocks };
  }

  return { buildMidi, zip, crc32, analysis, fugueZip };
});

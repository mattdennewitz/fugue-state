#!/usr/bin/env node
// Build the GitHub Pages site. index.html is written as a page fragment (the claude.ai
// artifact format, which the viewer wraps in a document), so wrap it here the same way.
// Usage: node scripts/build-pages.mjs [outDir]   (default: _site)
import { readFileSync, writeFileSync, mkdirSync, copyFileSync } from 'node:fs';

const out = process.argv[2] || '_site';
const src = readFileSync('index.html', 'utf8');
const cut = src.indexOf('<style>');
if (cut < 0) throw new Error('index.html has no <style> block to split the head at');

// Everything before the first <style> (title, metas, font links) belongs in <head>.
const head = src.slice(0, cut).trim();
const body = src.slice(cut);
const reset = ':root{color-scheme:light;padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}' +
  'body{margin:0;font:14px/1.4 system-ui,sans-serif}img{max-width:100%}[hidden]{display:none!important}';

const doc = `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<style>${reset}</style>
${head}
</head>
<body>
${body}
</body>
</html>
`;

mkdirSync(out, { recursive: true });
writeFileSync(`${out}/index.html`, doc);
for (const f of ['engine.js', 'export.js']) copyFileSync(f, `${out}/${f}`);
writeFileSync(`${out}/.nojekyll`, '');
console.log(`built ${out}/ (index.html, engine.js, export.js)`);

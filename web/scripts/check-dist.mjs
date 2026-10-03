#!/usr/bin/env node
// Post-build guard: the production bundle must contain no mock/fixture data,
// no service worker, and must carry the CSP meta tag.
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const dist = join(dirname(fileURLToPath(import.meta.url)), '../dist');
const files = [];
const walk = (d) => {
  for (const f of readdirSync(d)) {
    const p = join(d, f);
    if (statSync(p).isDirectory()) walk(p);
    else files.push(p);
  }
};
walk(dist);

const forbidden = ['DEMO FIXTURE', 'demo-fixture', 'sub_demo_', 'mockServiceWorker', 'x-arena-mock-dataset'];
const errors = [];
for (const f of files) {
  if (/mockServiceWorker/.test(f)) errors.push(`service worker shipped: ${f}`);
  if (!/\.(js|html|css|json|txt|svg)$/.test(f)) continue;
  const text = readFileSync(f, 'utf8');
  for (const needle of forbidden) if (text.includes(needle)) errors.push(`${f} contains "${needle}"`);
}
const html = readFileSync(join(dist, 'index.html'), 'utf8');
if (!/http-equiv="Content-Security-Policy"/.test(html)) errors.push('index.html lacks CSP meta');
if (/<script(?![^>]*\bsrc=)[^>]*>/.test(html)) errors.push('index.html contains an inline script');
if (/\sstyle=/.test(html) || /<style/.test(html)) errors.push('index.html contains inline styles');

if (errors.length) {
  console.error('check-dist FAILED:\n  ' + errors.join('\n  '));
  process.exit(1);
}
console.log(`check-dist ok: ${files.length} files, no mock data, CSP present`);

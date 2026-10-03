#!/usr/bin/env node
// Generates TypeScript types from the frozen JSON Schemas in common/schemas/.
// Output is committed under src/generated/ — rerun after a contract change:
//   pnpm gen:types
import { compile } from 'json-schema-to-typescript';
import { readFileSync, readdirSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, join, basename } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const schemaDir = join(here, '../../common/schemas');
const outDir = join(here, '../src/generated');
mkdirSync(outDir, { recursive: true });

const files = readdirSync(schemaDir).filter((f) => f.endsWith('.schema.json')).sort();
const index = [];
for (const file of files) {
  const schema = JSON.parse(readFileSync(join(schemaDir, file), 'utf8'));
  const name = basename(file, '.schema.json');
  const ts = await compile(schema, schema.title ?? name, {
    bannerComment:
      `/* eslint-disable */\n/**\n * GENERATED from common/schemas/${file} by web/scripts/gen-types.mjs.\n * Do not edit by hand; run \`pnpm gen:types\`.\n */`,
    additionalProperties: false,
    strictIndexSignatures: true,
    unreachableDefinitions: true,
    format: true,
    style: { singleQuote: true },
  });
  writeFileSync(join(outDir, `${name}.ts`), ts);
  index.push(name);
  console.log(`wrote src/generated/${name}.ts`);
}

// API envelope types that exist only in the server's OpenAPI document
// (StoredChallenge for /v1/challenges, EventPayload for SSE).
const openapiPath = join(here, '../../server/openapi.json');
const openapi = JSON.parse(readFileSync(openapiPath, 'utf8'));
const API_TYPES = ['StoredChallenge', 'EventPayload'];
const apiSchema = {
  title: 'ArenaApiTypes',
  type: 'object',
  additionalProperties: false,
  properties: Object.fromEntries(API_TYPES.map((t) => [t, { $ref: `#/components/schemas/${t}` }])),
  components: openapi.components,
};
const apiTs = await compile(apiSchema, 'ArenaApiTypes', {
  bannerComment:
    '/* eslint-disable */\n/**\n * GENERATED from server/openapi.json (StoredChallenge, EventPayload) by web/scripts/gen-types.mjs.\n * Do not edit by hand; run `pnpm gen:types`.\n */',
  additionalProperties: false,
  strictIndexSignatures: true,
  format: true,
  style: { singleQuote: true },
});
writeFileSync(join(outDir, 'api.ts'), apiTs);
console.log('wrote src/generated/api.ts');

writeFileSync(
  join(outDir, 'README.md'),
  '# Generated types\n\nGenerated from `common/schemas/*.schema.json` and `server/openapi.json` (api.ts) by `pnpm gen:types`. Do not edit.\n',
);

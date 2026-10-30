# Complete-code witness policy regression

These five pairs come from independent pinned-nearcore seed 2718 global/cache chunks.
Each complete witness was cold-nearcore accepted. Its paired mutation removes one code
blob without changing the claim or trie witness. All original `meta.json` bytes are retained.
Three missing-code mutants were cold-nearcore accepted; two were cold-nearcore rejected.
Those raw outcomes are never relabelled.

Run from the repository root with a built successor checker:

```sh
python3 tools/d3/check_code_witness_policy.py \
  --pairs tools/d3/code-policy-fixtures/pairs.json \
  --out /tmp/complete-code-policy
```

The harness checks the `completeCodeGlobal` tier twice. Complete and restored witnesses
must accept. Since 2026-10-29 a missing-code witness must reproduce its own raw cold
nearcore verdict: accept when an earlier in-chunk deploy serves the code deterministically,
reject (`MissingTrieValue`) when nothing does. The only other admitted result is the named
race exclusion `out of domain (e.code_prep_race)`. Until 2026-10-29 the policy rejected every
missing-code witness with `w.code_complete`, including the three nearcore accepts; that rule
is superseded (docs/evidence/lean-chunk-completion/w08-warm-cache/README.md).
Restoration verifies every supplied code hash and length against the original producer
registry, preserves the claim/trie, and must reproduce the complete witness byte-for-byte.

The committed evidence also records a larger 14-pair run (drop, flip and truncation,
nine raw cold acceptances and five raw cold rejections) made under the superseded policy.

Historical hash/code coherence (a poisoned compiled cache) remains an environment boundary,
as described in `docs/research/lean-code-witness-closure.md`.

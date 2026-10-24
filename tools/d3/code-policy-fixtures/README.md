# Complete-code witness policy regression

These five pairs come from independent pinned-nearcore seed 2718 global/cache chunks.
Each complete witness was cold-nearcore accepted. Its paired mutation removes one code
blob without changing the claim or trie witness. All original `meta.json` bytes are retained.
Three missing-code mutants were cold-nearcore accepted; two were cold-nearcore rejected.
Those raw outcomes must not be relabelled to match the stricter complete-witness relation.

Run from the repository root with a built successor checker:

```sh
python3 tools/d3/check_code_witness_policy.py \
  --pairs tools/d3/code-policy-fixtures/pairs.json \
  --out /tmp/complete-code-policy
```

The harness checks the `completeCodeGlobal` tier twice. Complete and restored witnesses
must accept; missing-code witnesses must specifically reject with `w.code_complete`.
A generic claim rejection or out-of-domain result fails this regression. Restoration
verifies every supplied code hash and length against the original producer registry,
preserves the claim/trie, and must reproduce the complete witness byte-for-byte. It does
not infer a new oracle verdict for an arbitrarily modified witness.

The committed evidence also records a larger 14-pair run (drop, flip and truncation),
including nine raw cold acceptances and five raw cold rejections. Temporary original
paths in that report identify the generation run; exact input and binary hashes bind
its observations. The five drop pairs here provide a portable replay subset.

This is verdict/policy evidence, not a proof of nearcore equivalence under arbitrary
compiled-cache history. Historical hash/code coherence remains a boundary, as described
in `docs/research/lean-code-witness-closure.md`.

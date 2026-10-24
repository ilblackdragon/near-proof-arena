# Live W13 acquisition/gate probe — 2026-10-24

**Result: FAIL. This is not a successful mainnet execution replay.**

Three mainnet block documents were downloaded over HTTPS from the recorded NEAR Data URLs,
heights 220185437–220185439. They contain 30 newly included chunk slots. Exact response bytes and
hashes are retained in `capture/`. There are no claim/witness pairs for these chunks in this probe.

The actual `make w13-gate` invocation reports:

```text
W13 FAIL: mismatch=N/A (no comparisons); coverage=0.0000%; compared=0/30; {'missing_witness': 30}
```

`result/report.json` records missing data, the absent native adapter, the 1000-block requirement,
and executable/input identities. The named Lean executable was identified but never invoked because
there were no executable cases. This proves capture and failure accounting work, not that any
mainnet chunk executed in Lean. Archive provenance trusts HTTPS; finality signatures were not checked.

Reproduce from the repository root (nonzero exit is expected until real inputs are provided):

```sh
make w13-gate \
  W13_CAPTURE=docs/evidence/lean-chunk-completion/mainnet-w13-probe/capture \
  W13_REPORT=/tmp/w13-probe-report
```

The runtime path/identity may differ from the archived probe. A real W13 pass requires the full
window, validated native mainnet context and witness pairs, with all expected chunks matching.
See `tools/mainnet-replay/README.md` for acquisition and adapter requirements.

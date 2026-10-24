# L7 — D2 output evidence: causal mutant check and committed reports (handoff)

Date: 2026-10-24. Work item: close the two D2 gaps in the D3 output evidence — the report lived in
gitignored `var/`, and the causal header-mutant check was D3-only. Plan lane:
`docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md` (L7 differential validation). Evidence document:
[docs/evidence/lean-chunk-final-outputs/d2-outputs.md](../evidence/lean-chunk-final-outputs/d2-outputs.md).

## Execution and handoff checklist

| field | value |
|---|---|
| owner | L7 (differential validation and integration) |
| agent | verification subagent, OpenCode / DeepSeek V4.1 Flash 1017 |
| worktree | `/data/illia/nearproof-wt/lean-d2-outputs` |
| branch | `work/d2-output-evidence` |
| base commit | `5491f7f03d2c1521e62c6407d8df52afad4471df` |
| committed tip | recorded in the reply; **not merged, not pushed** |
| target | nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86 |
| inventory IDs | none claimed. This is an evidence/tooling change under the L7 lane; it closes no inventory row and no Gate A/B/C. |

## 1. Result summary

Both gaps are closed and committed. **D2's causal output check passes with 0 failures**, and the D3 path
is provably unchanged.

| measure | value |
|---|---|
| D2 whole-corpus output agreement | 67,384 cases read; 17,738 accept / 49,256 reject / 390 out-of-domain; **0 field mismatches**, 0 null-output accepts, 0 missing lines, **0 failures** |
| D2 causal header-mutant check | 747/747 honest bases accepted with outputs; **10,298 mutants** across 14 covered families; 10,298 rejected for an output reason; **0 wrong, 0 failures** |
| D2 non-output header mutants (not scored) | 2,209 run for visibility: `proposed_split.some` 715/715 rejected `InvalidChunkHeaderShardSplit`; `height_created` 747/747 accept; `height_included(unchecked)` 747/747 accept |
| D3 regression | 40/40 bases, 360/360 mutants right, 0 failures; report **byte-identical** (`cmp`) to the committed `mut-d3c9.json` |
| reason table | all 17 `hdr.*` families produce identical verdict/reason strings under `--d2` and D3; no per-mode override needed |

Nothing here closes Gate A, B or C. It is evidence and tooling for the D2 pipeline.

## 2. Changed declarations and scripts

Lean: **none**. The signed relation `checkD2CoreObs`/`checkD2Core` and every Lean file is untouched; the
driver binary is the one already committed at base. Only Python tooling and docs changed.

| file | change |
|---|---|
| `tools/d3/check_output_mutants.py` | added `--d2`, `--family`, `--families core\|extended`; split `EXPECTED` into `CORE_EXPECTED` (9, D3 default, unchanged) and `EXTENDED_EXPECTED` (14, default under `--d2`); added `UNCOVERED` visibility histogram; reports gain `pipeline`, `honest_family`, `family_table`, `uncovered_families`, and per-family `preempted` — all only on the extended/D2 path |
| `docs/evidence/lean-chunk-final-outputs/d2-outputs.md` | new evidence document |
| `docs/evidence/lean-chunk-final-outputs/full-d2.json` | new: whole-corpus output agreement, D2 pipeline |
| `docs/evidence/lean-chunk-final-outputs/mut-d2.json` | new: causal mutant report, D2 pipeline, 747 bases |
| `docs/evidence/lean-chunk-final-outputs/mut-d3c9-regress.json` | new: D3 regression report, byte-identical to `mut-d3c9.json` |

No existing evidence file was modified. `mut-d3c9.json` and the four `mut-d3c*.json` reports are untouched.

## 3. Build and test commands

No rebuild was needed; the base commit's binary is current for these sources. Verified:

```sh
sha256sum oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out
# 6ec0e691af1c9c4038ee62e1c20cf32f41c82bc91f585a9aee84af5580daa64a

# whole-corpus output agreement, all three families
python3 tools/d3/check_outputs.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --d2 --families d2,mutants,ood --shards 20 --report var/out-runs/full-d2.json

# causal header-mutant check, full base set
python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --d2 --shards 24 --bases 747 --report var/out-runs/mut-d2.json

# D3 regression
python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 20 --bases 40 --report var/out-runs/mut-d3c9-regress.json
cmp var/out-runs/mut-d3c9-regress.json docs/evidence/lean-chunk-final-outputs/mut-d3c9.json   # silent = identical
```

All three scripts exited 0. Rebuild commands, if the binary is ever absent:
`(cd spec/lean/v3 && lake build NearSpecV3)` → `lake build NearSpecV3.Logged.API` →
`(cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3-out)`.

## 4. Artifact hashes (sha256)

| artifact | sha256 |
|---|---|
| driver `nearspec-v3-check-d3-out` | `6ec0e691af1c9c4038ee62e1c20cf32f41c82bc91f585a9aee84af5580daa64a` |
| `tools/d3/check_output_mutants.py` | `cec2c553c026214d79b11cb6134059d6517978c2f73d4de7267c311ba4409b10` |
| `docs/evidence/.../d2-outputs.md` | `54758b96380224ed9f83dd292eb5eb8cac85ea589bec21aebcebc233d81db05c` |
| `docs/evidence/.../full-d2.json` | `e551fce95fe02cec803096af87fe50f9b04d46232b879f568334e5ac089d0b87` |
| `docs/evidence/.../mut-d2.json` | `51d194ebd88cfe40e70b5d88fe5ac18799ee5912a9834070f86cd9ecb6809115` |
| `docs/evidence/.../mut-d3c9-regress.json` | `83f52cb7e672b316aabc1e484edec1d8b29bc56ab20c2a1ba56c22ddbf00e75c` |
| corpus `summary.json` | `fc62b6c3de4dd5dbb223f1f489ddad8f039de0064cd51793a9f0b49ba8101393` |
| Lean `ChunkValidationD2.lean` (unmodified) | `86ca3b3bcbbceee1fbdc41b099b3aa4d14fbcfe924a009808421ecff20187384` |
| Lean `ChunkValidationD2Out.lean` (unmodified) | `85e817a617ca1638566ffbc509e725e95164b0f8ba5ee32f33d0c58431e70f9a` |
| `oracle/wasm-d3/lean/MainD3Out.lean` (unmodified) | `8d544d0b709c31a970011ad0851c94c676dbb928880ccbbb1d66a3b1dcee665a` |

Hashes are of the working-tree files as committed. The document and report hashes change if either is
edited, so re-hash after any edit. The script hash changes only when the script changes.

## 5. Actual counts and failing cases

| run | denominator | result |
|---|---|---|
| `check_outputs.py --d2 --families d2,mutants,ood` | 67,384 cases (every case on disk) | accept 17,738 · reject 49,256 · out-of-domain 390 · **0 mismatches · 0 failures** |
| `check_output_mutants.py --d2 --bases 747` | 747 bases · 10,298 covered mutants | 747/747 bases accepted · 10,298/10,298 output-reject · **0 failures** |
| `check_output_mutants.py d3c9 --bases 40` | 40 bases · 360 mutants | 40/40 bases · 360/360 output-reject · **0 failures** |

**Failing cases: none.** No mutant in the D2 run was rejected for a non-output reason; no mutant was
pre-empted by another output check (every reason named its own field's comparison exactly).

The 40-base D2 slice was also run (`--bases 40`, 14 families, 0 failures) as a cheap smoke check; the
committed denominator is the full 747-base set. The 2,209 non-output header mutants are not counted as
passes or failures — see the evidence document's "What this does not establish".

## 6. Next executable step

1. **Independent witness for D2 outputs.** The Python claim decoder shares the wire format with Lean, so a
   decoder bug present in both would be invisible. [RESULT.md](../evidence/lean-chunk-final-outputs/RESULT.md)
   §3 closes this for D3 using nearcore's own `meta.json` features (`wasmGas` vs
   `fc_gas_burnt_for_function_call`, log count vs `n_logs`). Audit the D2 corpus's `meta.json` for the
   same independent fields and run `tools/d3/check_nearcore_features.py --family d2` over `d2corpus.v2`.
   That is the strongest remaining gap in this evidence and it is not blocked.
2. Optionally wire `check_output_mutants.py --d2 --bases 40` into CI as a cheap causal regression gate; the
   full 747-base sweep takes minutes and is better as a scheduled job.

## 7. Files safe for the next agent to edit

* **Safe:** `docs/evidence/lean-chunk-final-outputs/d2-outputs.md` (add the nearcore-feature section when
  §6.1 lands), `docs/logs/lean-chunk-L7-d2-outputs-2026-10-24.md` (append a session note),
  `tools/d3/check_output_mutants.py` (extend families or add a CI flag; keep the default D3 path
  byte-identical — `mut-d3c9.json` byte equality is the guard).
* **Regenerate, do not hand-edit:** the four committed JSON reports. They are script output; re-run the
  commands in §3 and copy from `var/out-runs/`.
* **Do not edit:** the signed Lean surface (`spec/lean/v3/NearSpecV3/ChunkValidationD2.lean`,
  `ChunkValidationD2Out.lean`) — out of scope by task constraint; and the existing D3 evidence files
  (`RESULT.md`, `full-d3c*.json`, `mut-d3c*.json`, `nearcore-feat-d3*.json`) — this change added to that
  directory without modifying any of them.

# STATUS — lane L6 (NEAR AIR)

Branch `lane/zk-L6`. Layout spec: `NEAR-AIR.md`. Lean: `zk-formal/ZkFormal/Near/`.

## Top theorems (`Near/Compose.lean`, `Near/Main.lean`)

| theorem | remaining hypotheses |
|---|---|
| `nearAir_sound_L5` | `NodeViewStmt`, `RcptViewStmt`, `MrkViewStmt`, `LinkStmt` |
| `nearAir_complete'` | `RenderStmt` |
| `honestTrace_fits'` | `RenderStmt` |

## Obligations

| statement | owner | state |
|---|---|---|
| `GoodSoundStmt` (spec ⇒ `NearRelation`) | L6-sound | **proved** `Spec/Sound.lean` `good_sound` |
| `GoodCompleteStmt` + `extOf` (pruning) | L6-complete | **proved** `Spec/Complete.lean` `good_complete` |
| `ShaFactsStmt` (SHA contract) | L6 | **proved** `Extract/ShaFacts.lean` `shaFacts` (from L5 `sha_digest_contract_closed`) |
| `SortViewStmt` | L6 | **proved** `Extract/SortProof.lean` `sort_view` |
| `WalkViewStmt` | L6 | **proved** `Extract/WalkProof.lean` `walk_view` |
| `AcctViewStmt` | L6 | **proved** `Extract/AcctProof.lean` `acct_view` |
| `MrkViewStmt` | L6 | open |
| `NodeViewStmt` | L6 | open |
| `RcptViewStmt` | L6 | open (rcpt table under test in L6-render) |
| `LinkStmt` (views + SHA + balance ⇒ `Good`) | L6-link | in progress |
| `RenderStmt` + `render` (honest trace) | L6-render | generators for all but rcpt done, rcpt + statement split in progress |
| `Budget.weq_le` (W_eq = 1766 ≤ 3000), `nearAir_wf` | L6 | **proved** (kernel, `BudgetCheck.lean`, 13 s) |
| `nearAir_npOk` (L3 side condition) | L6 | **proved** (kernel, `NpOkCheck.lean`, 8 s) |

## Table fixes found by tests/proofs

* acct: `lo8` monotonicity was enforced across segment boundaries (fixed).
* sort: `ft` reset constraint fired on the wrap from a full `2^13` table to row 0 (now gated by `isTransition`).

## Elaboration time (per module)

All `Near/Spec/*`, `Near/Extract/*` modules: < 2 s each. Kernel checks: BudgetCheck 13 s, NpOkCheck 8 s.

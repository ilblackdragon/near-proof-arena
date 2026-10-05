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

## L6-link (`LinkStmt`, branch `lane/zk-L6-link`)

`Link/Compose.lean`: `link_of` proves `LinkStmt` from the nine statements of
`Link/Statements.lean` (witness `linkExt`).

| statement | state | file |
|---|---|---|
| `ShaStmt` (message reconstruction) | **proved** `sha_ok` | `Link/Sha.lean` |
| `ClaimStmt` | **proved** `claim_ok` | `Link/Claim.lean` |
| `ReceiptsStmt` | **proved** `receipts_ok` | `Link/Receipts.lean` |
| `NodupStmt` | **proved** `nodup_ok` | `Link/Nodup.lean` |
| `TrieStmt` | **proved** `trie_ok` | `Link/Trie.lean` |
| `RunStmt` | **proved** `run_ok` | `Link/Run.lean` |
| `PostStmt` | **proved** `post_ok` | `Link/Post.lean` |
| `RefundsStmt` | **proved** `refunds_ok` | `Link/Refunds.lean` |
| `OutStmt` | open | — |
| `WalksStmt` | open | — |

View changes (REQUESTS-L6.md): R-L6d-1 (`canon` fields), R-L6d-2 (`arith`
assumes `Bytes8 ramt` only for refund receipts).

# STATUS — lane L6 (NEAR AIR)

Branch `lane/zk-L6`. Layout spec: `NEAR-AIR.md`. Lean: `zk-formal/ZkFormal/Near/`.

## Top theorems (`Near/Compose.lean`, `Near/Main.lean`)

| theorem | remaining hypotheses |
|---|---|
| `nearAir_sound_R` (`Near/Final.lean`) | `RcptViewStmt` |
| `nearAir_sound_closed` (`Near/Final.lean`) | **none** (axioms: propext, Classical.choice, Quot.sound) |
| `nearAir_sound_NR` / `nearAir_sound_L5` | (superseded) |
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
| `MrkViewStmt` | L6 | **proved** `Extract/MrkProof.lean` `mrk_view` |
| `NodeViewStmt` | L6 | **proved** `Extract/NodeProof.lean` `node_view` (22 modules `Extract/Node*`, ~20 s total) |
| `RcptViewStmt` | L6-rcptview | **proved** `Extract/RcptProof.lean` `rcpt_view` (statement fixed per R-L6r-1..3) |
| `LinkStmt` (views + SHA + balance ⇒ `Good`) | L6-link | **proved** `Link/Main.lean` `link` |
| `RenderStmt` + `render` (honest trace) | L6-render / L6e | generators done (all buses balance on the sample, `test/NearRenderTest.lean`); obligations `RenderObligations` (Local/Traffic/Bus) in progress (sub-lane `lane/zk-L6-rproof`) |
| `Budget.weq_le` (W_eq = 1766 ≤ 3000), `nearAir_wf` | L6 | **proved** (kernel, `BudgetCheck.lean`, 13 s) |
| `nearAir_npOk` (L3 side condition) | L6 | **proved** (kernel, `NpOkCheck.lean`, 8 s) |

## Table fixes found by tests/proofs

* acct: `lo8` monotonicity was enforced across segment boundaries (fixed).
* sort: `ft` reset constraint fired on the wrap from a full `2^13` table to row 0 (now gated by `isTransition`).
* rcpt: account ids of 65 bytes were accepted (now `≤ 64`).
* rcpt: `idx` was not reset at a receipt start (R-L6r-4; added `rf·idx = 0`).
* views: `MrkV.n` added (the claimed `n` is only a field element); `canon` fields (raw values `< p`).

## Elaboration time (per module)

All `Near/Spec/*`, `Near/Extract/*` modules: < 5 s each (slowest `NodeSlot` 4.7 s, `MrkProof` 5 s).
Node extraction: 22 modules, ~20 s total. Kernel checks: BudgetCheck 13 s, NpOkCheck 8 s.

## L6-link (`LinkStmt`, branch `lane/zk-L6-link`) — **proved**

`Link/Main.lean`: **`link : LinkStmt`** (axioms: propext, Classical.choice,
Quot.sound), via `link_of` (`Link/Compose.lean`) from the nine statements of
`Link/Statements.lean` (witness `linkExt`); also `nearAir_sound_linked`
(`nearAir_sound'` without the `LinkStmt` hypothesis).

| statement | proof | file |
|---|---|---|
| `ShaStmt` (message reconstruction) | `sha_ok` | `Link/Sha.lean` (+ `ShaCore`, `ShaEnc`) |
| `ClaimStmt` | `claim_ok` | `Link/Claim.lean` |
| `ReceiptsStmt` | `receipts_ok` | `Link/Receipts.lean` |
| `NodupStmt` | `nodup_ok` | `Link/Nodup.lean` |
| `TrieStmt` | `trie_ok` | `Link/Trie.lean` (+ `Parent`, `Tree`, `NodeHash`, `TrieHash`) |
| `WalksStmt` | `walks_ok` | `Link/Walks.lean` (+ `WalkLen`, `WalkEdge`, `WalkChain`, `WalkKey`, `WalkSpec`) |
| `RunStmt` | `run_ok` | `Link/Run.lean` (+ `MemBus`, `MemTime`, `Mem`, `RunChain`, `RunAcc`) |
| `PostStmt` | `post_ok` | `Link/Post.lean` |
| `OutStmt` | `out_ok` | `Link/OutMain.lean` (+ `MrkLevels`, `OutLeaf`, `OutBus`, `Out`) |
| `RefundsStmt` | `refunds_ok` | `Link/Refunds.lean` |

View changes (REQUESTS-L6.md): R-L6d-1 (`canon` fields), R-L6d-2 (`arith`
assumes `Bytes8 ramt` only for refund receipts). Elaboration: every `Link/*`
module < 1 s; all 40 modules from scratch 12.6 s wall.

## L6-rcptview (`rcpt_view`, branch `lane/zk-L6-rcptview`)

Modules `Extract/Rcpt*.lean` (each < 6 s elaboration; `RcptCharClass` ≈ 5 s, all others < 2 s):
Facts/Segs/Layout/Table/Regs (row structure, receipt field layout `layout_of`, `table_of`),
RowT/Of/Chunks/FB1/FB2/Bytes/Gates/Bus/Chars/Key/Dig/Claim/Shape/Traffic (`traffic_of`: all buses),
WfEasy/Count/Chain/Gas1-3/Dep/Arith/Toks/ClaimArith/CharClass/Strings/StrField/Names/WfIds (`RcptWf`),
Proof (`rcpt_view`).  Statement fixes R-L6r-1..3 adopted in `Extract/RcptView.lean`; `Link/{Mem,RunChain,
RcptFacts,EncLemmas,Refunds,Sha,Run}.lean` adapted (`link` still proved).

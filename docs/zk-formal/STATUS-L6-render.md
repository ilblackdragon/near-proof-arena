# STATUS — sub-lane L6e (L6-render): honest traces and AIR checker

Branch `lane/zk-L6-render`. Lean: `zk-formal/ZkFormal/Near/Render/`,
test `zk-formal/test/NearRenderTest.lean`
(`lake env lean test/NearRenderTest.lean`, ≈ 4 s).

## What exists

| module | content |
|---|---|
| `Render/Common.lean` | `Info`/`mkInfo` (pre/post `ser` of every node bottom-up, depths, walk targets `res`, pre/post value bytes, touched slots), `walkOf`/`walksOf` (key walks over the node table's edges), `edgeUses`, `tprevOf`/`tlastOf`, `Msg`, `padTo` |
| `Render/Node.lean` | `nodeRowsAll I uses` (one row per serialized byte, node-id order, `SUM` row, padding), `nodeMsgs` (`NPRE`/`NPOST`) |
| `Render/Walk.lean` | `walkRowsAll` (START + one row per key symbol, chained counters `u`) |
| `Render/Acct.lean` | `acctRowsAll`, `acctMsgs` (`VPRE`/`VPOST`) |
| `Render/Mrk.lean` | `mrkRowsAll`, `mrkMsgs` (`MRK(q)`) |
| `Render/Sort.lean` | `sortRowsAll` (ids ascending LE, delay line cyclic) |
| `Render/Rcpt.lean` | `rcptRowsAll` (claim rows, receipt segments, registers, account-id machinery, key symbols, gas/balance arithmetic with carries/borrows/delay lines/bit pools, claim checks; emission slots filled by evaluating the table's own `emits`), `rcptData` |
| `Render/Views.lean` | the honest views of the extraction side (`nodeViewsOf`, `walkViewsOf`, `rcptViewsOf`, `acctViewsOf`, `mrkViewOf`, `sortIdsOf`), `shaTraffic`, `honestTraffic c e` (seven `Traffic`s, `nearAir` order) |
| `Render/Statements.lean` | split of `RenderStmt`: `LocalStmt` ×7, `TrafficStmt` ×7, `BusStmt` ×10 (`RenderObligations`) |
| `Render/Compose.lean` | `other_bus` (proved), **`render_stmt : RenderObligations → RenderStmt`** (no sorry; axioms propext, choice, Quot.sound) |
| `Render/RcptSim.lean` | the `rcpt` side simulated from the `Ext` (kept for comparison: `Bundle.busSim`): `rcptMsgs` (`RC`, `RF`, `PEO`, `LEAF`, `RID`), `rcptBus` (DIGEST receives, KEYNIB, FINAL, MEM, RIDS, MPOS), `shaSim` (sha side: BYTES receives, DIGEST sends) |
| `Render/Check.lean` | `violations` (every non-vanishing `(row, constraint)`, via `Expr.eval`), `badBits`, `tableBus` (via `multNat`/`msgVal`), `imbalances` (per bus/message `Σ send − Σ recv` with contributing tables), reports |
| `Render/Tables.lean` | `bundle c e` (all five generators + every SHA message), `Bundle.bus` (whole AIR traffic, `sha`/`rcpt` simulated) |

## Test results (`test/NearRenderTest.lean`)

Examples (claim computed from the `Ext`: roots via `trieOf … |>.hashOf`,
`outcomeRoot`, commitments): ex1 root branch-with-ref-value → branches →
branch with two touched leaves (2 receipts); ex2 odd extension → branch →
two touched leaves + two dead extensions (one single-nibble), 3 receipts
(two on one slot: MEM chain); ex3 branch with a touched value and a touched
one-nibble leaf below; ex4 empty-key extensions (root and inner) and a
one-nibble extension, 1 receipt (mrk promote-only, sort single segment).

With the acct fix and the sort padding row: node, walk, acct, mrk, sort have **no constraint
violations and no bad bits** on all four examples, and **every bus balances**
(BYTES, DIGEST, PARENT, VSLOT, EDGE, KEYNIB, FINAL, MEM, RIDS, MPOS), with
`sha` and `rcpt` simulated. In particular the pre/post state roots and the
outcome root computed by NearSpec match the digests the tables look up.

## Table bugs found

1. **`acct`, lane-switch constraint** `act · lo8' · (1 − lo8) = 0`: violated
   on the last lane of every segment (the next row is the next segment's first
   lane, `lo8 = 1`) and, on a full table, by the wrap to row 0. Fixed on
   `lane/zk-L6` by the lead (gate `act · (1 − al)`); this branch merged that
   version (my equivalent `act − al` gate was dropped).
2. **`sort`, next-segment `ft = 0`** `sl · act' · ft' = 0`: violated whenever
   the table is full (`32·n` a power of two): the last row is `sl` and wraps to
   row 0, which has `ft = 1`. **Not fixed in the table** (the lead's
   `Extract/SortProof.lean` uses this exact constraint); the generator always
   adds at least one padding row instead. That works for every `n` except
   **`n = 256`**: `32·256 = 2^13 = 2^maxLog`, no room for a padding row, so the
   honest trace of a full batch violates the table — a **completeness bug**.
   **Fixed by the lead** on `lane/zk-L6` (`isTransition · sl · act' · ft' = 0`).

## Generator notes (not table bugs)

* node: on an odd `HPF` row and on the last key row of an extension, the edge
  contents `aI aS aN aJ` / `bN bJ` are constrained even when the gate is off
  (dead extension child); the generator fills them.

## Soundness review (trie side: no holes found; rcpt: see bug 3)

Mutation probe (`test/NearProbeTest.lean`, ≈ 75 s): on an honest trace of a
mixed example (odd extension, branch, touched branch value, dead extension,
odd/even leaves, 3 receipts), every column of one row per flag pattern is
changed by `+1`; a change no constraint (rows `r−1`, `r`) and no interaction
observes is "free". Free cells found are all don't-cares: node nibble bits off
`HPF`/`KEY` rows, `jj`/`w`/`lastw` off branch `CH` windows, flags on the `SUM`
and padding rows; acct `inv` off the last lane; mrk `sp s odd inv` on the root
row; sort `diff` bits / carries on the first segment and padding; walk none.

Checked while writing the generators (argument sketches in the commit log):
window slot order (`belowE = w` ⇒ windows are the present slots in order,
exactly `pop` of them; extensions exactly one), node segment/field framing,
`VSLOT` one-to-one, `acct` lane framing, walk framing (START first, `KEYNIB`
consumed once per `(r,t)`, `END` = last), edge chains (consumers alone need
`p` walk rows), mrk level shape (`sp + odd = 2s` with a huge `s` cannot reach
`lil`, so the table cannot end), the root row's free `J` (only the top node's
`MPOS` is unreceived), sort's delay line (32 previous rows are active).

Minor / completeness-only:
* node `HPL` first byte is `hplen` with the other three `0`: needs
  `hplen < 256` (key < 510 nibbles); account paths are ≤ 132 nibbles.
* dead extension: `xres` (and the window's `cres`) are free; harmless (no edge
  leaves the extension).

## rcpt (second milestone)

* Generator `Render/Rcpt.lean` written from `Tables/Rcpt*.lean`; the real
  table replaces the simulation in `bundle`, `Bundle.bus` and `render`
  (`ZkFormal.Near.render := Render.render` in `Honest.lean`).
* Tests: on ex1–ex5, rcpt has no violations and every bus balances with the
  real rcpt table. ex5 covers: 64-char receiver, SECP256K1 signer key
  (`kt = 1`), gas price below / equal / above the block price (refund only
  above; `ge = 0` case), a 6-char predecessor ≠ `system`, a `0x`+40 receiver
  that is not hex (named), storage 700 ≤ 770 with balance below the stake
  (`big = 0`) and storage 5000 above it, a `2^100` deposit.
* `views exN`: every table's traffic equals the extraction side's view
  traffic of the honest views (`nodeTraffic` … `sortTraffic`, i.e. the
  `TrafficStmt`s hold on the examples), and that traffic balances (the
  `BusStmt`s).
* Mutation probe on rcpt: no semantic cell is free (only `xb 8..25` on claim
  rows 8–11, the `770` slack bits when `big = 1`, the `tprev` bits off the
  first DEP row).

### rcpt table bug (fixed, soundness)

3. **Account-id length ≤ 64 not enforced.** `L − 2 = bitsX 0 6` allows
   `L ∈ [2, 65]`; `AccountId.valid` (and `RcptV.Wf.ids` of the extraction
   side) needs `≤ 64`, so a receipt with a 65-byte predecessor / receiver /
   signer was accepted (the relation rejects it). Fix in
   `Tables/Rcpt/Arith.lean` `cChars`: `fe · s · (64 − L − bitsX 6 6) = 0` for
   `s ∈ {P, V, S}` (3 constraints, no new columns; `xb 6..11` are unused on
   those rows; `BudgetCheck` passes). Test: a 65-char predecessor violates
   exactly this constraint.

## Sort table

The lead's fix (`isTransition · sl · act' · ft'`) is merged; the generator no
longer adds a padding row (a full batch, `n = 256`, fills `2^13` rows exactly).

## Render statements

`RenderStmt` ⇐ `RenderObligations` (`Render/Compose.lean`, proved):
`ShaLocalStmt … SortLocalStmt` (`TableLocal` of each table of
`render c.1 e` under `Good c.1 e`), `ShaTrafficStmt … SortTrafficStmt`
(`TableTraffic … (htf c e t)`, the honest view traffic), `BytesBusStmt …
MposBusStmt` (trace-free balance of the honest traffic per bus); buses `≥ 10`
carry nothing (`other_bus`). `bundle` is total (a failing walk is empty, with
`walkErrors`), so `render` has no fallback branch.

## Doc discrepancies (for the lead)

* NEAR-AIR.md §1 `PEO` length `46 + 32·hr + L_v`: `Outcome.partialEncode` is
  `4 + 32·hr + 8 + 16 + (4 + L_v) + 1 + 4 = 37 + 32·hr + L_v` (the rcpt table
  uses 37, correctly).

## Open

* Proofs of the `RenderObligations` (none proved yet). The generators are
  imperative (`Id.run`, `Array.set!` loops), which is convenient for testing
  but not for proofs; the local statements are best attacked by giving each
  table a closed-form cell function `cell r col` (segment `r / L`, lane
  `r % L`) proved equal to the generator's rows, then checking constraints
  per row kind.
* `extOf` (pruning) is still a placeholder; `render` assumes the records'
  root is node 0 and the walks succeed (`walkErrors = []`), which `Good`
  should give via `WalkTo` (the generator's walk skips empty-key extensions
  through `res`, the spec walk takes `EPS` steps).
* The sha cells via `Sha.Gen.rowCell` cost ≈ 1.5 ms each in the interpreter,
  so tests use L5's expected traffic for the sha side.

## Render obligations — proofs (`Render/Proof/`, lane/zk-L6-rproof)

Generators rewritten in closed form where needed for the proofs (same rows;
`test/NearRenderTest.lean` still: no violations, every bus balanced):
`mkTab H W f` tables for sort/acct/walk, `Info.vpre/vpost/res` as maps
(`resF`), functional `walkOf` (`walkFrom`), `rcptData` (`rdOf`, prefix sums),
walk counters `useAtL`/`usesL` shared by the walk table and its view.

| obligation | theorem | module |
|---|---|---|
| `SortLocalStmt` | `sortLocal` | `Proof/SortLocal` (+ `SortIds`: sorted ids strictly increasing, carries) |
| `SortTrafficStmt` | `sortTraffic_ok` | `Proof/SortTraffic` |
| `AcctLocalStmt` | `acctLocal'` (needs `TouchedLe e`, R-L6e-1), `acctLocal_of` | `Proof/AcctLocal` (+ `AcctFacts`) |
| `AcctTrafficStmt` | `acctTraffic_ok` | `Proof/AcctTraffic` |
| `WalkLocalStmt` | `walkLocal` | `Proof/WalkLocal` (+ `WalkOk`: generator walk = spec walk; `WalkShape`) |
| `WalkTrafficStmt` | `walkTraffic_ok` | `Proof/WalkTraffic` (+ `WalkIdx`) |
| `VslotBusStmt` | `vslotBus` | `Proof/BusVslot` |
| `RidsBusStmt` | `ridsBus` | `Proof/BusRids` |
| `MemBusStmt` | `memBus` | `Proof/BusMem` (+ `MemChain`: write/read time pairs are a permutation) |
| `FinalBusStmt`, `KeynibBusStmt` | `finalBus`, `keynibBus` | `Proof/BusFinal` |
| `MrkLocalStmt` | `mrkLocal` | `Proof/MrkLocal{,2,3,4}` (+ `MrkRecs`: row records of the levels) |
| `MrkTrafficStmt` | `mrkTraffic_ok` | `Proof/MrkTraffic{,2,3}` (+ `MrkFacts`: level sizes, `MRK` indices = `hashedBefore`) |
| `MposBusStmt` | `mposBus` | `Proof/BusMpos` (children of level `j` = level `j − 1` in order; taken positions = rotation of offered ones) |

**Assembly** (`Proof/Main`): `render_of_rest : RenderRest → RenderStmt`, where
`RenderRest` = the open obligations: `TouchedLe` from `Good` (R-L6e-1),
`Sha/Node/Rcpt` Local + Traffic, buses `BYTES, DIGEST, PARENT, EDGE`.
All proofs: axioms `propext, Classical.choice, Quot.sound` only.

Elaboration (`lake env lean`, wall): MrkLocal2 21 s, MrkLocal 12 s, WalkLocal 6 s,
SortLocal 5 s, MrkLocal3 5 s, MrkLocal4 5 s, AcctLocal 4 s, the rest ≤ 1.2 s.
`test/NearRenderTest.lean` ≈ 50 s (was 36 s; walk counters are `O(rows²)`).

Generator changes (rows unchanged up to the closed forms; test passes):
`Render/{Sort,Acct,Walk,Mrk}.lean` closed form via `mkTab`; `Render/Common.lean`:
`mkTab`, `Info.vpre/vpost` as maps, `resF` (walk targets), functional
`walkFrom`/`walkOf`; `Render/Rcpt.lean`: `rdOf`/`rcptData` as a map with
prefix sums; `Render/Views.lean`: views built from the same closed forms
(walk counters `usesL`, mrk levels `MrkGen.levels`).

Key lemma: `walkOf_ok` (`Proof/WalkOk`): under `Good`, the generator's walk of
every receipt succeeds and ends at `e.slot r` (simulation of the spec `Walk`
with `EPS` steps collapsed by `resF`; `resF` is stable by the `TreeShape`
depth argument).

## Sub-lane L6e-rsha (lane/zk-L6-rsha): `Small`, sha, BYTES

**Statement fix (R-L6e-1, resolved).** `Spec/Small.lean`: `NodeRec.dead`
(branch, no value, no child), `NodeRec.terminal = touched || dead`,
`structure Small e` with field `terminals : (e.ns.filter terminal).length ≤
maxBatch` (`Small.touched`, `Small.dead`).  `Spec/SmallComplete.lean`:
`small_complete : NearRelation c w → Small (extOf c w)` (`tc_prune`: each
terminal record of `prune keys t` ends a distinct key).  `RenderStmt` and every
`Local/Traffic/BusStmt` now assume `Good c.1 e → Small e →`; `Good` unchanged.
`SmallCompleteStmt` (Near/Statements); `nearAir_complete hC hSm hR` /
`honestTrace_fits` (Near/Compose), primed versions in Near/Main with
`good_complete`, `small_complete`; `nearAir_complete_rest`,
`honestTrace_fits_rest : RenderRest → …` (Render/Proof/Main, the DESIGN
statements from the open obligations only).  `acctLocal : AcctLocalStmt`.

| obligation | theorem | module |
|---|---|---|
| `ShaLocalStmt` | `shaLocal` | `Proof/ShaFit4` (+ `ShaTab`: table 0 of `render` = `Sha.honestTrace`, L5's `sha_complete_closed`) |
| `ShaTrafficStmt` | `shaTraffic_ok` | `Proof/ShaFit4` |
| `BytesBusStmt` | `bytesBus_of : NodeSerStmt → RcptBytesStmt → BytesBusStmt` | `Proof/BusBytes` |
| `RcptBytesStmt` (rcpt BYTES sends = bytes of `rcptMsgs`) | `rcptBytes` | `Proof/RcptBytes{1,2}` |

`Sha.MsgsOk` under `Good ∧ Small` (`ShaFit1–4`): bytes `< 256` and lengths
`< 2^25` for every message; SHA rows (`rowsOf L = 1 + 17·⌈(L+9)/64⌉`):
node `≤ (5·revealedOf + 144·#dead)/4 ≤ 3 759 216` (only dead branches are under
43 bytes; `8·rowsOf S ≤ 5·S` for `S ≥ 43`, tight at 56), acct `≤ 17 920`,
mrk `≤ 13 600`, rcpt `≤ 81 355`; total `≤ 3 872 091 ≤ 2^22`.

`RenderRest` now: `nodeL, rcptL, nodeT, rcptT, nodeSer, digest, parent, edge`.
`NodeSerStmt` (for the node lane): the node views serialize as `mkInfo`'s
`pre`/`post` (`(nodeViewOf I uses n).v.ser false = I.pre.getD n []`, same for
`post`).

**Merge note.** `Proof/ShaFit1` proves `pre_ok`/`post_ok` (bytes, length
`≤ sz0 (nodeAt n)`) for the *loop* form of `mkInfo`; lane/zk-L6-node rewrites
`mkInfo` in closed form (`nodeSer (treeOf …)`), so after that merge only
`pre_ok`/`post_ok` need a new proof (they already take `Good`, for the hash
widths of `Kid.hash`).  Everything downstream uses only these two lemmas.

Elaboration (`lake env lean`, wall): ShaTab 2.7 s, RcptBytes2 1.6 s, ShaFit4
1.4 s, all others `< 0.6 s`.

**Open: `RcptLocalStmt`, `RcptTrafficStmt`.** Not started: the rcpt table has
965 constraints over 228 columns and the generator (`Render/Rcpt.lean`) is
imperative (`Id.run`, `set!` loops per field / carry / delay line).  As for
the other tables, the first step is a closed-form cell function per segment
row (`(r, field, idx) ↦ cell`), then one lemma per constraint family
(`Tables/Rcpt/{Fields,Arith}.lean`).  `RcptTraffic` could then reuse the
soundness side: the extraction (`Extract/RcptTraffic`, `rcpt_view`) gives the
traffic of any locally valid rcpt table as `rcptTraffic pub (viewOf …)`, so
it remains to identify the extracted view with `rcptViewsOf I`.

## Sub-lane L6e-rcpt (lane/zk-L6-rcptr): `RcptLocalStmt` (partial), `RcptTrafficStmt` (open)

**Generator in closed form.** `Render/Rcpt.lean`: records `recsOf ds`
(`RRec.cl i`, `RRec.seg r s i`), cells `fullCell` (= `segCell`/`clCell`, emission
slots = the table's `emits` evaluated by `evalF`), carries/borrows `chain`/`bchain`,
columns as numerals.  Same rows as the old imperative generator on ex1–ex5
(checked cell by cell); `test/NearRenderTest.lean` passes (≈ 67 s, was ≈ 50 s).

**Proof infrastructure** (`Render/Proof/Rcpt{Base,Rows,Cells,Col,Lem}`): `evR`
(an expression on a row given as functions), `Zr` (syntactic vanishing when
cells are zero), `nextOf` adjacency of the records, `allRows_of` (a constraint
holds on every row from: record rows with their successor, the last record,
padding rows), generated column lemmas `S_*`/`L_*` (simp sets `rseg`, `rcl`).

**Proved families** (on every row of `render c.1 e`, under `Good`):
`cStates` (`RcptStates1–7`: bits, one-hot, field bookkeeping, last indices,
successions, receipt boundaries and offsets `o`/`o2`/`rcnt`, constants),
`cEmit` (`RcptEmit`), `cChars` (`RcptChars1–5`: character-local constraints by
`decide` over the 256 bytes on a synthetic row, separators, lengths,
predecessor ≠ `system`, named receiver), `cKey` (`RcptKey`); heights and
multiplicity bits (`RcptLocal`).

**Assembly.** `RcptP.rcptLocal_of`/`rcptLocal_fams : RcptFams → RcptLocalStmt`;
`RenderRest.rcptL` is now `RcptP.RcptFams` = the five open families
`cRegs`, `cGas`, `cDep`, `cClaim`, `cEnd` (`FamOk F`: every `x ∈ F` holds on
every row).  No table bug found.  All modules ≤ 8.1 s (`RcptChars1` 8.1 s,
`RcptStates1` 4.6 s, rest ≤ 2.5 s); axioms `propext, Classical.choice,
Quot.sound`.

**Open.** The five families (registers/tokens, gas and balance byte-serial
arithmetic, claim checks, end-of-batch) and `RcptTrafficStmt`.  Gas/dep need
the chain lemmas (`Σ out_j 256^j + 256^n·carry_n = Σ x_j 256^j`) and the
no-overflow facts of `RcptOk`; `cEnd` needs `pub_n/pub_nref/pub_tok`
(`Link/Claim`) with `Hdr = ⟨hg.pv, hg.chain⟩`.

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

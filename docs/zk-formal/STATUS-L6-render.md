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
| `Render/RcptSim.lean` | the `rcpt` side simulated from the `Ext`: `rcptMsgs` (`RC`, `RF`, `PEO`, `LEAF`, `RID`), `rcptBus` (DIGEST receives, KEYNIB, FINAL, MEM, RIDS, MPOS), `shaSim` (sha side: BYTES receives, DIGEST sends) |
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

After the fixes below: node, walk, acct, mrk, sort have **no constraint
violations and no bad bits** on all four examples, and **every bus balances**
(BYTES, DIGEST, PARENT, VSLOT, EDGE, KEYNIB, FINAL, MEM, RIDS, MPOS), with
`sha` and `rcpt` simulated. In particular the pre/post state roots and the
outcome root computed by NearSpec match the digests the tables look up.

## Table fixes

1. **`acct`, lane-switch constraint** `act · lo8' · (1 − lo8) = 0` (lo8 never
   rises): violated on the last lane of every segment, since the next row is
   the next segment's first lane (`lo8 = 1`) — or, when the table is full,
   row 0 by wrap-around. Gate changed to `act − al` (active, not last lane);
   degree unchanged. Soundness unchanged: within a segment `lo8` is still
   non-increasing, starts at 1 (`af`), ends at 0 (`al`), and drops only at
   `i = 7`.
2. **`sort`, next-segment `ft = 0`** `sl · act' · ft' = 0`: violated when
   the table is full (`32·n` a power of two, e.g. `n = 1, 2, 4`): the last row
   is `sl` and wraps to row 0, which has `ft = 1`. Replaced by
   `isTransition · sl · ft' = 0` (degree 3; padding rows have `ft = 0`
   honestly and `ft` is only read on active rows).

## Generator notes (not table bugs)

* node: on an odd `HPF` row and on the last key row of an extension, the edge
  contents `aI aS aN aJ` / `bN bJ` are constrained even when the gate is off
  (dead extension child); the generator fills them.

## Soundness review (holes found: none so far)

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

## Doc discrepancies (for the lead)

* NEAR-AIR.md §1 `PEO` length `46 + 32·hr + L_v`: `Outcome.partialEncode` is
  `4 + 32·hr + 8 + 16 + (4 + L_v) + 1 + 4 = 37 + 32·hr + L_v`.

## Open

* `render : Claim → Ext → Trace Fp` (`Render/Trace.lean`): in progress.

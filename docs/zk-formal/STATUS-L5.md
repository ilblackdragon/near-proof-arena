# Lane L5 (SHA-256 AIR) status

Table: `zk-formal/ZkFormal/Sha/Table.lean` — 544 columns, degree ≤ 4,
1011 constraints, 17 interactions (16 byte receives + 1 digest provide).
Layout: `Sha/Layout.lean`. Honest generator: `Sha/Gen.lean`
(test: `lake env lean --run zk-formal/test/ShaGenTest.lean`).

Top theorems (`Sha/Compose.lean`, proved from the statements below, no sorry):
`shaLocal_of_holds`, `sha_block_sound`, `sha_bus_sound`, `sha_digest_contract`,
`sha_complete`.

| Statement (`Sha/Statements.lean`) | Owner | State |
|---|---|---|
| `KindStmt` | L5-block | open |
| `BlockStmt` (= `sha_block_sound`) | L5-block | open |
| `IVStmt` | L5-block | open |
| `ChainStmt` | L5 (lead) | open |
| `FrameStmt` | L5 (lead) | open |
| `DigestIoStmt` | L5 (lead) | open |
| `CompleteFamStmt cBool/cKind/cIV/cRound/cSched/cHelp/cDigest/cFrame` | L5-complete | **proved** (`Sha/Complete/*`: `complete_cBool` … `complete_cFrame`) |
| `LogStmt`, `MultBitsStmt`, `TrafficStmt` | L5-complete | **proved** (`logStmt`, `multBitsStmt`, `trafficStmt`) |

Elaboration times: Spec 0.4 s, Table 0.5 s, Compose < 2 s.

## Completeness (closed)

`Sha/Complete/All.lean`: `sha_complete_closed` = `Compose.sha_complete`
instantiated with all eleven completeness sublemmas (axioms: `propext`,
`Classical.choice`, `Quot.sound` only).  Structure of the proof:

* `Complete/Basic` — every honest cell is `Fp.ofNat` of a `Nat`, so an AIR
  expression evaluates to the image of an integer (`eval_honest`); bit-level
  facts for `rotr`/`σ`/`Σ`/`Ch`/`Maj` (via `Nat.testBit`);
* `Complete/Rows` — `honestRows` per message as an indexed function
  (`msgRows_eq`); every row and its cyclic successor form a `Step`
  (`step_at`); `logStmt`;
* `Complete/Cells`, `FrameCells` — cell values by column group;
* `Complete/Blocks`, `Pad` — block bounds/chaining, padded-message bytes;
* `Complete/Words` — gates and word limbs; one file per family
  (`Bool, Kind, IV, Help, Digest, Round, Sched, Frame{1,2,3}, Frame`);
* `Complete/TrafficMsg`, `Traffic` — per-message receives/provides, then
  `trafficStmt`.

Elaboration (`lake env lean`, per module, incl. import loading): Basic 0.4 s,
Rows 0.5 s, Cells 1.5 s, Kind 0.3 s, Bool 0.2 s, IV 0.2 s, Blocks 0.3 s,
Words 0.3 s, Help 0.3 s, Digest 0.3 s, Round 0.4 s, Sched 1.1 s, MultBits 0.2 s,
Pad 0.5 s, FrameCells 0.3 s, Frame1 0.5 s, Frame2 0.5 s, Frame3 2.2 s,
Frame 0.2 s, TrafficMsg 0.4 s, Traffic 0.4 s, All 0.1 s.

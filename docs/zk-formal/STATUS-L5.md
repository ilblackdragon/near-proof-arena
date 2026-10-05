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
| `KindStmt` | L5-block | **proved** (`Sha/Sound/Kind.lean`: `Sound.kindStmt`) |
| `BlockStmt` (= `sha_block_sound`) | L5-block | **proved** (`Sha/Sound/Block.lean`: `Sound.blockStmt`, `Sound.sha_block_sound'`) |
| `IVStmt` | L5-block | **proved** (`Sha/Sound/Kind.lean`: `Sound.ivStmt`) |
| `ChainStmt` | L5 (lead) | **proved** from `KindStmt` (`Frame/Chain.lean` `chainStmt_of`) |
| `FrameStmt` | L5 (lead) | **proved** from `KindStmt`, `BlockStmt` (`Frame/Stmt.lean` `frameStmt_of`; padding core `Frame/Pad.lean` `pad_of_frame`) |
| `DigestIoStmt` | L5 (lead) | **proved** from `KindStmt` (`Frame/Stmt.lean` `digestIoStmt_of`) |
| `CompleteFamStmt cBool/cKind/cIV/cRound/cSched/cHelp/cDigest/cFrame` | L5-complete | **proved** (`Sha/Complete/*`: `complete_cBool` … `complete_cFrame`) |
| `LogStmt`, `MultBitsStmt`, `TrafficStmt` | L5-complete | **proved** (`logStmt`, `multBitsStmt`, `trafficStmt`) |

Elaboration times: Spec 0.4 s, Table 0.5 s, Compose < 2 s.

`Sha/Frame/All.lean`: `sha_bus_sound_of`, `sha_digest_contract_of` — soundness
now depends only on `KindStmt`, `BlockStmt`, `IVStmt`.
Frame modules elaborate in ≤ 2 s each.
Soundness (`Sha/Sound/`): Bits 0.3 s, Bridge 0.4 s, Kind 0.4 s, Round 1.9 s, Block 1.6 s
(no sorry/axiom/native_decide; axioms: propext, Classical.choice, Quot.sound).

`Sha/Sound/` structure: `Bits` (bit characterization of `rotr/bsig/ssig/ch/maj`,
`ofBits`), `Bridge` (field→`Nat`: `ev`, sums without wraparound, boolean
gadgets, `addC`/`eqG` with gate 1), `Kind` (`KindStmt`, `IVStmt`, gate values),
`Round` (row-local round/schedule/helper/digest steps), `Block`
(rows of a block, schedule by strong induction via `Spec.Wt_rec'`, rounds via
`Spec.As_succ4/Es_succ4`, digest via `Spec.compress_eq`).
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

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
| `CompleteFamStmt cBool/cKind/cIV/cRound/cSched/cHelp/cDigest/cFrame` | L5-complete | open |
| `LogStmt`, `MultBitsStmt`, `TrafficStmt` | L5-complete | open |

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

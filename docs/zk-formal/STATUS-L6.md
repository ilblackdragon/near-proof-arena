# STATUS — lane L6 (NEAR AIR)

Branch `lane/zk-L6`. Layout spec: `NEAR-AIR.md`. Lean: `zk-formal/ZkFormal/Near/`.

## Top theorems (`Near/Compose.lean`) — proved from statements

| theorem | from |
|---|---|
| `nearAir_sound` | `ExtractStmt`, `GoodSoundStmt` |
| `nearAir_complete` | `GoodCompleteStmt`, `RenderStmt` |
| `honestTrace_fits` | `GoodCompleteStmt`, `RenderStmt` (via `Holds.logBound`) |

## Obligations

| statement | owner (sub-lane) | state |
|---|---|---|
| `GoodSoundStmt` (spec ⇒ `NearRelation`) | L6-spec-sound | open |
| `GoodCompleteStmt` + `extOf` (pruning) | L6-spec-complete | open |
| tables `node/walk/rcpt/acct/mrk/sort` | L6 (lead) | skeleton |
| `ExtractStmt` (per-table/bus split pending tables) | L6a–d | open |
| `RenderStmt` + `render` | L6e | open |
| `Budget.weq_le` (W_eq ≤ 3000, kernel) | L6 | open |

## Elaboration time (per module, `lake build`)

| module | time |
|---|---|
| `Near.Spec.*`, `Near.Compose` (skeleton) | < 1 s |

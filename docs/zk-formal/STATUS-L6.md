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
| `GoodSoundStmt` (spec ⇒ `NearRelation`) | L6-spec-sound | **proved** (`Spec/Sound.lean` `good_sound`) |
| `GoodCompleteStmt` + `extOf` (pruning) | L6-spec-complete | open |
| tables `node/walk/rcpt/acct/mrk/sort` | L6 (lead) | v1 written (`Tables/*.lean`); testing in L6-render |
| `ExtractStmt` (per-table/bus split pending tables) | L6a–d | open |
| `RenderStmt` + `render` | L6e | open |
| `Budget.weq_le` (W_eq = 1766 ≤ 3000, kernel), `nearAir_wf` | L6 | **proved** (`BudgetCheck.lean`, 13 s) |
| `RenderStmt` generator + checker | L6-render | in progress |

## Elaboration time (per module, `lake build`)

| module | time |
|---|---|
| `Near.Spec.*`, `Near.Compose` (skeleton) | < 1 s |

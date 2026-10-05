# STATUS — lane L4 (AIR DSL, protocol/verifier model, fast SHA)

Branch `lane/zk-L4`. Interfaces published (frozen for M1); format: `FORMATS.md`.

## Published interfaces

| Item | Where | State |
|---|---|---|
| `Air.Expr/Interaction/Table/Air/Trace`, `Expr.eval(With)`, `Holds` (multi-table, bit multiplicities, multiset bus balance) | `ZkFormal/Air/Basic.lean` | done |
| `Air.exportJson` (`np-air-v1`) | `ZkFormal/Air/Export.lean` | done |
| `StarkField` interface + instance for L1 `Fp`/`Fp8` | `Stark/Field.lean`, `Stark/Instance.lean` | done |
| `Params` (UDR2 defaults) | `Stark/Params.lean` | done |
| abstract IOP: `Slot`, `PT`, `Mat`/`Oracle`, `IopSpec`, `trueOpenings`, `ChecksPass`, `NextIsProver/Chal`, `AtQuery`, `accepts` | `Stark/Iop.lean` | done |
| BCS compiler `Bcs.compile`, total parser `parsePrefix`, MMCS multiproofs | `Stark/Bcs.lean` | done |
| layout/aux/schedule | `Stark/Protocol.lean` | done |
| `Iop.verifier`, `verifier`, `verifier_eq_compile` (rfl) | `Stark/Verifier.lean` | done |
| `ArenaCore.sha256Fast` + `@[csimp] sha256_eq_sha256Fast` (1.1 µs/block vs 40–52) | `formal-core/ArenaCore/SHA256Fast.lean`, `GOVERNANCE-sha256fast.md` | done |

## Obligations (`Stark/Statements.lean` → `Stark/Compose.lean`)

| Statement | Owner (sub-lane) | State |
|---|---|---|
| `CompileQueryBoundStmt` | lane/zk-L4-qbound | **proved** `compile_queryBound` (QueryBound.lean) |
| `NpBoundsStmt` (np-udr-stark bounds ⇒ `NVu`) | lane/zk-L4-npbounds | **proved** `np_bounds` (NpBounds.lean; propext, Quot.sound) |
| `ParsePrefixStmt`, `LawsStmt`, `DecodeAgreeStmt` | lane/zk-L4-parse | **proved** `parsePrefix_split`, `laws` (+ `instance lawsInst`), `decode_agree`, `readHeader_encHeader` |
| Reference prover + end-to-end tests + L8 vectors | lane/zk-L4-test | in progress |
| `verifier_queryBound'` (NVu, unconditional) | L4 | **proved** |

## Notes

* Transcript encoding follows L2's extraction (`Bcs/*` on lane/zk-L2): a challenge
  steps the state (`d ← WH(CHAL, d)`), absorption is `u8 #roots ‖ roots ‖ clear`.
* `Air.wf` also bounds total bus multiplicity and fingerprint degree by
  `busBudget = 2^36` (the per-round bad count assumed by `Params.commitBad`).
* Session OOM crash at 19:06: the qbound and test sub-lanes were restarted under the
  `heavy` wrapper.

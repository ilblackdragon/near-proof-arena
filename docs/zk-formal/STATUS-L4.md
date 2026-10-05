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

## Verifier speed (lane/zk-L4d)

Compiled-verify time was quadratic: `take?` measured `List.length` of the
remaining proof on every 4-byte read, and Merkle leaf/node readers sliced
`r.take (r.length - r'.length)`. Fix: linear `takeF`, `mpLeavesF`, `readInjF`,
each proved equal in the kernel and installed with `@[csimp]` inside
`Stark/Bcs.lean`, right after the originals, so all compiled callers use them.
Definitions and proofs are unchanged. Axioms: propext, Quot.sound.

| proof | before | after |
|---|---|---|
| 0.40 MB (toy multi 10) | 5850 ms | 87 ms |
| 0.77 MB (toy multi 14) | 19104 ms | 170 ms |
| 1.00 MB (toy multi 16) | – | 230 ms |
| 1.66 MB (bench w=1000, h=2^14) | – | 382 ms |
| 3.51 MB (bench w=3000, h=2^14) | – | 792 ms |
| 3.95 MB (bench 3×w=1000, h=2^16) | – | 920 ms |
| 4.18 MB (bench w=3500, h=2^16) | – | 1005 ms |

The lead measured 13 s, 80 s and 180 s for 0.5 MB, 0.92 MB and 1.45 MB before
the fix. Conformance `run.sh 3 6 10` gives ALL PASS (honest proofs accepted,
every mutation rejected).

# Lane L2 (Fiat–Shamir/BCS) status

Top theorem: `ZkFormal.Bcs.bcs_romSound` (`Bcs/Compose.lean`), **proved** from
the statements in `Bcs/Statements.lean`. Axioms: propext, Classical.choice,
Quot.sound.

| Sublemma | File | Owner | State |
|---|---|---|---|
| log plumbing (`evalT`, `simulate_evalT`, `TableWF`, splits) | Bcs/Log.lean | L2 | proved |
| wide hash binding `wh_unique`, no-inversion `noInv_of` | Bcs/Wide.lean | L2 | proved |
| commitment interface, `invert_eq`, `used_produced` | Bcs/Commit.lean | L2 | proved |
| single-height Merkle `merkle_binding` | Bcs/Merkle.lean | L2 | proved |
| **extraction lemma** `chain_extract`, `accept_imp_event_log` | Bcs/Extract.lean | L2 | proved |
| `bcs_romSound` (composition) | Bcs/Compose.lean | L2 | proved from Stmts |
| `GameStmt`, `QBAddStmt`, `StepMixStmt` | Bcs/Game2.lean | L2-game | **proved** `game2`, `qbAdd`, `stepMix` |
| `MmcsStmt` (mixed-height MMCS binding, L4 byte format) | Bcs/Mmcs.lean | L2 | **proved** `mmcs_binding_rooted` |
| `BudgetStmt` | Bcs/Budget.lean | L2-budget | **proved** `budget`, `budget_K24` |
| `MultiproofStmt` (L4 multiproof ⇒ mmcsOpen paths) | Bcs/Multiproof*.lean | L2-mp | **proved** `multiproof_sound` |
| `CompileAcceptsStmt` (L4 `Stark.Bcs.compile` ⇒ `AcceptsIn (adapt V)`) | Bcs/Stark{Adapter,Parse,Chain,Decode,Open,Align,Refine,Main}.lean | L2 | **proved** `compile_accepts` |
| `stark_romSound'` (RomSound of L4's deployed verifier) | Bcs/Final.lean | L2 | **proved**; inputs: L3 RBR facts, L4 `SchedOk` |
| `InvPotStmt` (inversion potential) | Bcs/InvPot.lean | L2-inv | **proved** `invPot` |
| RBR facts transport (L3 `RbrFacts` → `Bcs.PT mmcs` form) | — | L3/L7 | not started |

Design amendments (relative to DESIGN.md §4), recorded in REQUESTS.md:
* Challenge: `d ← WH(CHAL, d)`, challenge = first half. This fixes an
  out-of-order challenge gap in the original `H(CHAL ‖ d)` scheme.
* Absorb: `WH(ABS, d ‖ u8 n ‖ roots ‖ raw)`.
* Inversion: the half-known attack. An adversary that learns one half
  `H(tag‖1‖m)` can use digests `(known, guess)` before asking the other half.
  This is a 256-bit guess per use, not 512-bit, so DESIGN's "Q²·2^-512, an
  instance of product_step" is not right as stated. The correct bound is
  about `C·q/2^256`, which is still negligible. It is proved with a dedicated
  potential (`InvPotStmt`).

Elaboration: all Bcs modules < 1 s each.

## L2b: RBR transport (branch lane/zk-L2b)

Top theorem: `ZkFormal.Bcs.Transport.stark_romSound_rbr` (`Bcs/TransFinal.lean`).
It gives `RomSound` for `Stark.Bcs.compile V` with bound
`bcsNum K (bad·Dm) (G^K) … / 2^(256K)`, from L3's `Udr.RbrWith V InLang Kall bad agree D`.
Its remaining inputs are:
* L1/L4: `Dm` (`hdec_deployed` gives `Dm = 2·3^8` for Fp/Fp8, `Kall = Fp8.all`);
* L4: `SchedOk V`, `0 < posPerChunk`, `posPerChunk·posBits ≤ 256`, `queryLog ≤ posBits`;
* a bound `G ≥ agree(2^n0)^p·2^(256−p·n0)`;
* query budgets.

| Sublemma | File | State |
|---|---|---|
| `decodePT`, `DoomedB` (malformed = doomed forever) | Bcs/TransDefs.lean | defs |
| `transport` (hinit/hmsg/hround/hquery from RbrWith) | Bcs/TransCompose.lean | proved from Stmts |
| `DecNoneStmt`, `DecMsgStmt`, `DecChalStmt` | Bcs/DecPush.lean | **proved** |
| `DecQueryStmt` | Bcs/DecQuery.lean | **proved** `decQuery` |
| `PosCountStmt` | Bcs/PosCount.lean | **proved** `posCount` |
| `hdec_deployed` | Bcs/TransFinal.lean | **proved** |

Adapter change: rows are normalized to the declared width (`rowAt`/`normRow`),
and `points` is `[0]` when there is no header. `compile_accepts` was re-proved under both.

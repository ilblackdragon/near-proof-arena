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
| `stark_romSound` (RomSound of L4's deployed verifier) | Bcs/Final.lean | L2 | proved, modulo `InvPotStmt` + L3 RBR facts |
| `InvPotStmt` (inversion potential) | Bcs/InvPot.lean | L2-inv | in progress |
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

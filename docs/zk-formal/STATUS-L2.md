# Lane L2 (Fiat–Shamir/BCS) status

Top theorem: `ZkFormal.Bcs.bcs_romSound` (`Bcs/Compose.lean`), **proved** from
the statements in `Bcs/Statements.lean`. Axioms: propext, Classical.choice,
Quot.sound.

| Sublemma | File | Owner | State |
|---|---|---|---|
| log plumbing (`evalT`, `simulate_evalT`, `TableWF`, splits) | Bcs/Log.lean | L2 | proved |
| wide hash binding `wh_unique`, no-inversion `noInv_of` | Bcs/Wide.lean | L2 | proved |
| commitment interface, `invert_eq`, `used_produced` | Bcs/Commit.lean | L2 | proved |
| single-height Merkle `merkle_binding`, `merkle_rooted` | Bcs/Merkle.lean | L2 | proved |
| **extraction lemma** `chain_extract`, `accept_imp_event_log` | Bcs/Extract.lean | L2 | proved |
| `bcs_romSound` (composition) | Bcs/Compose.lean | L2 | proved from Stmts |
| `GameStmt`, `QBAddStmt`, `StepMixStmt` | Bcs/Game2.lean | sub-agent L2-game | open |
| `InvPotStmt` (inversion potential) | Bcs/InvPot.lean | sub-agent L2-inv | open |
| `MmcsStmt` (mixed-height MMCS binding) | Bcs/Mmcs.lean | sub-agent L2-mmcs | open |
| `BudgetStmt` (profile arithmetic) | Bcs/Budget.lean | sub-agent L2-budget | open |
| L4 refinement `evalT … = some true → AcceptsIn` | (L4) | L4 | requested (REQUESTS.md) |
| RbrFacts transport to byte transcripts | (L7/L2) | — | not started |

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

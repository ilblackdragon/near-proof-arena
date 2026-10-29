import NearSpecV3.ActionConfinement
import NearSpecV3.StateMeasure
import NearSpecV3.Supply
import NearSpecV3.D2.Receipts
import NearSpecV3.D2.RuntimeD2

/-!
# The top-level conservation statement, as a type

Companion to `docs/TOP_LEVEL_THEOREM.md`. This file contains **no proofs** — only the definitions the
statement needs and the statement itself as `example`s left `sorry`ed, so that a third party can check
that the obligation is well-typed against the real tree before investing in it.

Everything here elaborates against the pinned definitions; the `sorry`s are the work to be done.

## Why the measure needs the in-flight term

A deposit-paying step moves value out of an account and into an emitted receipt. The account-only
measure therefore **drops**, and a statement without the in-flight term is *false*, not merely weaker:

  `(senderBefore - dep) + receiverAfter ≠ senderBefore + receiverAfter`   for `dep > 0`

With the in-flight term the identity holds. This is exactly the accounting a
"credited then rejected" bug corrupts, which is why the state measure alone cannot catch it.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3 NearSpecV3.Supply

/-! ## The measure -/

/-- NEAR attached to a receipt: the deposit its actions carry, if it is an action receipt.
Data and distribution receipts carry none. -/
def rcptAmount (r : Rcpt) : Nat :=
  match r.body with
  | .action _ a => (totalDeposit a.actions).getD 0
  | _ => 0

/-- NEAR sitting in receipts emitted but not yet applied: forwarded, buffered-to-local, and the
instant queue. -/
def inFlight (rs : RS) : Nat :=
  sumNat ((rs.outgoing ++ rs.locals ++ rs.instant).map rcptAmount)

/-- **The full supply measure for receipt processing.** Accounts plus access-key balances plus burnt
tokens (`stateTotal`, `StateMeasure.lean`) plus value in flight. -/
def rsSupply (rs : RS) : Nat :=
  stateTotal rs.o.trie (rs.txBurnt + rs.otherBurnt) + inFlight rs

/-! ## The obligations

Each is stated as an `example` with a `sorry` body. A prover should replace the `sorry` with a proof;
the statement must not be altered (see §6 of `docs/TOP_LEVEL_THEOREM.md`). -/

/-- **Obligation 1 (the core).** Applying one action receipt conserves the measure.

This is the statement that catches "credited during execution, then the receipt fails and rolls back,
but the refund over-returns": the measure includes both the account total and the value sitting in the
receipts the failure path emits, so an over-refund makes the equality fail. -/
example (hooks : ActionHooks) (env : Env) (rs rs' : RS) (r : Rcpt) (a : ActionR)
    (out : OutD1) (n : Nat)
    (h : applyActionReceipt hooks env rs r a = .ok (rs', out, n)) :
    rsSupply rs' = rsSupply rs := by
  sorry

/-- **Obligation 2.** A transaction conserves the measure *up to the fee it pays in*.

`processTxD2` (`RuntimeD2.lean:24`) has the two credit sites `:49` and `:66`; the charge is
`totalCost = gasCost + depositCost`, taken from the signer before execution. The right-hand side is
therefore larger by the declared cost, which is a parameter of the transaction, not a free amount. -/
example (env : Env) (rs rs' : RS) (seen seen' : List Bytes) (tf : TxD2 × Bool) (fee : Nat)
    (h : processTxD2 env (rs, seen) tf = .ok (rs', seen'))
    (htc : ∃ c : TxCostD2,
      txCostD2 tf.1.pk tf.1.signer tf.1.receiver tf.1.actions env.ctx.gasPrice = some c
        ∧ c.totalCost = fee) :
    rsSupply rs' = rsSupply rs + fee := by
  sorry

/-- **Obligation 3.** Processing one receipt conserves the measure, with no in-flight bookkeeping
needed.

`processReceipt` (`Receipts.lean:219`) dispatches on the receipt body and, for an action receipt,
runs `applyActionReceipt`; the value it consumes arrives inside `r` itself, so the in-flight term is
unchanged by the call and the equality is over `rsSupply` alone. This is the composition point: with
obligations 1 and 3, an induction over `processLocals` / `processReceipt` gives conservation for the
whole receipt phase.

Note this is *not* stated over `applyNewChunkD2`: that function returns only a root hash
(`RuntimeD2.lean:228`), so accounts cannot be compared through it. A chunk-level statement must either
be phrased on the state before `finalize`, or use a root-to-supply function that does not exist yet. -/
example (hooks : ActionHooks) (env : Env) (rs rs' : RS) (r : Rcpt) (out : Option (OutD1 × Nat))
    (h : processReceipt hooks env rs r = .ok (rs', out)) :
    rsSupply rs' = rsSupply rs := by
  sorry

/-! ## What is deliberately *not* stated here

Two weaker or false formulations were considered and rejected; they are recorded so a prover does not
"helpfully" weaken the obligation back to them.

* **The account-only measure** (`stateTotal` without `inFlight`) is *not* conserved — a deposit-paying
  step drops it by `dep`. Proved counterexample shape in the module docstring above.
* **A chunk-level statement over `applyNewChunkD2`** cannot compare accounts: that function returns
  only `out.root : Bytes` (`RuntimeD2.lean:228`), and no `Bytes → Nat` supply function exists. A
  chunk-level theorem must be phrased on the `RS` before `finalize`, or must first define and prove a
  root-to-supply extraction lemma. Stating it over `out.root` would be either false or vacuous.

## The composition

Obligation 1 (`applyActionReceipt`) and obligation 3 (`processReceipt`) are the two steps that move
value. A prover who closes both, then inducts over `processLocals` / `processDelayed` /
`processIncoming` and folds `processTxD2` (obligation 2), obtains conservation for the whole receipt
phase. Adding the epoch mint — bounded already by `Supply.mintedAmount_le_supply_div_40` — gives the
chunk-level claim.

That is the end-to-end property: **no NEAR is created or destroyed anywhere in the D2 runtime except
by the epoch mint, and that mint is capped at 2.5 % per year. -/

end NearSpecV3.D2
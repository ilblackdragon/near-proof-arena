# Top-level theorem: NEAR is conserved by the D2 runtime

**Status: specification only.** Nothing in this document is proved. The Lean file
`spec/lean/v3/NearSpecV3/ConservationStatement.lean` contains the three obligations as `example`s with
`sorry` bodies, and **it elaborates against the pinned tree** — so the statements are well-typed as
written. That file is deliberately *excluded* from the default build so `make lean` stays
`sorry`-free.

Companion to `docs/PLAN_BALANCE_CONFINEMENT.md` (engineering plan) and
`docs/SUPPLY_AND_INFLATION.md` (what is currently proved).

---

## 1. The claim

> For every receipt the D2 runtime applies, the total NEAR held in accounts, against access keys, in
> receipts emitted but not yet applied, and already burnt is **exactly** preserved — so a credit that
> is later rolled back cannot leave value behind, and no step can create or destroy NEAR except the
> epoch mint, whose size is capped at 2.5 %/yr.

This is the property that catches the bug where a receipt credits a balance, then fails, and the
refund path does not net to zero.

---

## 2. The measure

```lean
-- StateMeasure.lean, already proved sound & complete via PTrie.allKeys:
acctTotalOf (v : Bytes) : Nat          -- amount + locked, 0 if not an account
acctSumOf   (t : PTrie) : Nat          -- Σ over account keys
akSumOf     (t : PTrie) : Nat          -- Σ over access-key gas balances
stateTotal  (t : PTrie) (burnt : Nat) : Nat := acctSumOf t + akSumOf t + burnt

-- ConservationStatement.lean, new:
rcptAmount (r : Rcpt) : Nat            -- the deposit an action receipt carries, else 0
inFlight   (rs : RS) : Nat             -- Σ rcptAmount over outgoing ++ locals ++ instant
rsSupply   (rs : RS) : Nat := stateTotal rs.o.trie (rs.txBurnt + rs.otherBurnt) + inFlight rs
```

### Why `inFlight` is mandatory

A deposit-paying step moves value out of an account and into an emitted receipt, so the account-only
measure **drops**. The statement without `inFlight` is therefore *false*, not merely weaker:

```lean
(senderBefore - dep) + receiverAfter ≠ senderBefore + receiverAfter      -- dep > 0
(senderBefore - dep) + receiverAfter + dep = senderBefore + receiverAfter
```

Both are machine-checked in this repo. This distinction is the whole point: a "credited then rejected"
bug corrupts the *in-flight → account* transition, which the state measure alone cannot see.

---

## 3. The obligations

All three are in `ConservationStatement.lean` and elaborate. Provers must replace the `sorry`s
without altering the statements (§6).

### Obligation 1 — one action receipt (the core)

```lean
example (hooks : ActionHooks) (env : Env) (rs rs' : RS) (r : Rcpt) (a : ActionR)
    (out : OutD1) (n : Nat)
    (h : applyActionReceipt hooks env rs r a = .ok (rs', out, n)) :
    rsSupply rs' = rsSupply rs
```

### Obligation 2 — one transaction, up to its fee

```lean
example (env : Env) (rs rs' : RS) (seen seen' : List Bytes) (tf : TxD2 × Bool) (fee : Nat)
    (h : processTxD2 env (rs, seen) tf = .ok (rs', seen'))
    (htc : ∃ c : TxCostD2,
      txCostD2 tf.1.pk tf.1.signer tf.1.receiver tf.1.actions env.ctx.gasPrice = some c
        ∧ c.totalCost = fee) :
    rsSupply rs' = rsSupply rs + fee
```

`processTxD2` (`RuntimeD2.lean:24`) has the two credit sites `:49` and `:66`; the charge is
`totalCost = gasCost + depositCost`, taken from the signer before execution. The right-hand side is
larger by the declared cost — a parameter of the transaction, not a free amount.

### Obligation 3 — one receipt of any kind

```lean
example (hooks : ActionHooks) (env : Env) (rs rs' : RS) (r : Rcpt) (out : Option (OutD1 × Nat))
    (h : processReceipt hooks env rs r = .ok (rs', out)) :
    rsSupply rs' = rsSupply rs
```

`processReceipt` (`Receipts.lean:219`) dispatches on the body and runs `applyActionReceipt` for action
receipts. The value consumed arrives inside `r`, so `inFlight` is unchanged by the call and the
equality is over `rsSupply` alone.

---

## 4. Composition to the chunk

Close obligations 1–3, then induct over `processLocals` / `processDelayed` / `processIncoming` and fold
`processTxD2` over the transaction list. Adding the epoch mint — already bounded by
`Supply.mintedAmount_le_supply_div_40` — gives the chunk claim.

That is the end-to-end property: **no NEAR is created or destroyed anywhere in the D2 runtime except
by the epoch mint, and that mint is capped at 2.5 % per year.**

---

## 5. Two formulations that are wrong (do not weaken back to them)

* **Account-only measure** — false, as shown in §2. A prover who drops `inFlight` will either fail or
  prove something untrue.
* **A chunk-level statement over `applyNewChunkD2`** — impossible as stated: it returns only
  `out.root : Bytes` (`RuntimeD2.lean:228`) and no `Bytes → Nat` supply function exists. A chunk-level
  theorem must be phrased on the `RS` before `finalize`, or must first define and prove a
  root-to-supply extraction lemma.

---

## 6. What is already proved, and what is not

Proved, axiom-clean (`propext`, `Quot.sound`, `Classical.choice` only):

| module | content |
|---|---|
| `Supply.lean` | epoch mint formula, uptime clip, `minted_amount` = ledger total, 2.5 %/yr bound, header supply identity, multi-block conservation |
| `SupplyConfinement.lean` | `validatorUpdate` writes no account outside the shard's stake info + treasury |
| `StateMeasure.lean` | account measure over the trie: sound & complete by `allKeys`, sensitive to account values, plus the overlay write delta `sumEntries_kvPut` |
| `ActionConfinement.lean` | 7 of 10 action constructors leave account keys alone (`actDelegate`, `actDeleteAccount` open) |

**Not proved** (this is the work being handed over):

1. Lifting `sumEntries_kvPut` from the committed list to `Ovl` + `finalize` — the *amount* delta, the
   analogue of what `StateMeasure` does for *keys*.
2. The commit/rollback fork: on `!res.ok`, `st.account`'s write-back (`Receipts.lean:141`) is
   discarded by `rollback` (`:162`), so the receipt's credit does not land. **This is the crux.**
3. `refunds` returns exactly the `dep` that the charge took, on the failure path.
4. Obligations 1–3 above, and their composition.

---

## 7. Hypotheses a prover may assume

Environment contract, not free assumptions — each is already an explicit argument:

* `Env` well-formed (layout, height, chain id).
* `RS.limits` / `RS.cong` invariants; the functions already `throw` on violation.
* All arithmetic is `Nat` with explicit `≥ 2^128 ⇒ throw` guards, so an `= .ok` premise already
  excludes overflow.

## 8. Do NOT assume

* **That `st.account` agrees with `o.lookup (kAccount recv)`.** They can disagree mid-receipt;
  `actTransfer` credits `st.account` while `o` is untouched. The step-4 write-back reconciles them. A
  proof assuming agreement is unsound.
* **That `refunds`' `depRefund` equals the deposit charged** — that is obligation 3.
* **That reward amounts equal the epoch ledger.** `validator_update` is a *trusted* claim value
  (`spec/claim-v3.md` T10); the claim carries no inputs to recompute it. Only the bound is provable,
  and it is proved.

---

## 9. Acceptance criteria

1. Compiles with **no `sorry`, no new `axiom`, no `native_decide`**.
2. `#print axioms` on each headline theorem: only `propext`, `Quot.sound`, `Classical.choice`.
3. `make lean` green across all four Lean projects.
4. Statements are the ones in §3, not weakened restatements.
5. **Regression check:** mutating `refunds` to return `dep + 1` must make a theorem fail to prove. If a
   proof survives that mutation, it is not proving conservation.

Criterion 5 is what distinguishes a real proof from the vacuous `Nat`-identity lemmas that
`SupplyRuntime.lean` currently contains — those are equally provable for a deliberately wrong refund.

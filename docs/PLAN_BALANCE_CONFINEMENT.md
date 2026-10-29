# Plan: end-to-end account-balance confinement for the D2 runtime

Status: **Phase 2: 7/10 actions; Phases 1, 3, 4 not done.** Written before
implementation so the shape and its limits are reviewable up front, and updated as reality diverged.

## Outcome so far (honest)

Proved in `NearSpecV3/ActionConfinement.lean`: `actCreateAccount`, `actDeploy`, `actToGasKey`,
`actFromGasKey`, `actStake`, `actDeleteKey`, **`actTransfer`** never change any account key's lookup,
plus the reusable `applyAll_keeps` / `foldRemove_keeps` / `rangeRemove_keeps` / `setAK_keeps` /
`setNonce_keeps` / `keeps_of_setAK_or_self` / `isBytePrefix_head_ne`.

`actTransfer` was the hard one and it did need a restructure, but not the one I predicted: the fix was
to stop letting a single `first` pick among closing tactics (which commits before the hypothesis is in
usable shape) and instead run separate `try`-guarded rewrite passes — `rw [← (Prod.mk.inj h).1]`, then
`rw [← h.1]` — before closing.

**A correction to the plan's premise.** I wrote that "no action writes an account key". That is
**false**: `actDeleteAccount` does `o.remove (kAccount recv)` (`Actions.lean:241`). The true statement
is *"every action except `actDeleteAccount` leaves all account keys alone, and `actDeleteAccount`
touches only the receiver's."* The six-`setAcct` census below is still the complete set of account
**credits**; it is not the complete set of account **writes**.

Also: `kAccount_ne_kNonce` did not exist in the key-disjointness set and was added to
`SupplyConfinement.lean`.

## The structural finding that makes this tractable

There are exactly **six** `setAcct` call sites in all of `NearSpecV3/D2`:

| # | file:line | who it credits |
|---|---|---|
| 1 | `D2/RuntimeD2.lean:49` | `t.signer` — deposit-failed transaction |
| 2 | `D2/RuntimeD2.lean:66` | `t.signer` — successful transaction charge |
| 3 | `D2/Receipts.lean:141` | `r.recv` — action write-back (step 4) |
| 4 | `D2/Receipts.lean:180` | `r.recv` — receiver gas reward |
| 5 | `D2/Validators.lean:52` | stake-info entry — epoch mint |
| 6 | `D2/Validators.lean:64` | treasury — epoch mint |

**`D2/Actions.lean` contains zero `setAcct`.** Every action mutates a *local*
`st.account : Option Acct` field of `ActSt`; `applyActionReceipt` writes that field back at step 4
(`Receipts.lean:141`) and **discards it at `rollback`** (`:162`). That is precisely the shape of the
bug class in question: credit applied during execution, then the receipt fails and the credit is
supposed to vanish.

So the account-write surface is finite, enumerable, and already 2/6 proved (§5.5).

## Phases

### Phase 1 — per-site confinement (6 sites)
For each `setAcct` site, prove `Keeps (kAccount b) o o1` when `b` is not the account that site names.
Sites 5–6 are done (`validatorUpdate_keeps`). Sites 1–4 need the same treatment.

### Phase 2 — actions never touch an account key (10 constructors)
For each action, prove
`actX ... = .ok (st', _) → st'.o.lookup (kAccount a) = st.o.lookup (kAccount a)`.

This was meant to establish that only the six sites can write an account. As noted above, that is
true for *credits* but not for *deletions* — `actDeleteAccount` removes the receiver's account key. Proven pattern (validated on `actCreateAccount` and `actToGasKey`):

```
unfold actX at h
simp only [bind, Except.bind, pure, Except.pure] at h
cases <each monadic read> ...
-- leaf: either Err (simp at h) or Ok:
obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h); subst hst
simp only [Ovl.setAK]; rw [lookup_set_other]; exact kAccount_ne_kAK ..
```

Reusable workhorse already proved: **`applyAll_keeps`** — a fold of `set`/`remove` at keys other than
`kAccount a` keeps `a`'s lookup (for `actDeleteAccount`'s `iterKeys`-driven removals).

### Phase 3 — the receipt fork (the theorem that answers the original question)
Compose Phase 1 + 2 into: *whatever `applyActionReceipt` does to the overlay, the only account whose
record can change is `r.recv`, and on the failure path its `st.account` mutation is discarded by
`rollback`.* The concrete target:

```
applyActionReceipt ... = .ok (rs', _, _) →
  ∀ b, b ≠ r.recv → Keeps (kAccount b) rs.o rs'.o
```

and its failure-path corollary: when `res.ok = false`, `r.recv`'s record is **not** updated, so the
`refunds` deposit return is the only balance movement for that receipt.

### Phase 4 — honesty pass
State what is still *not* proved, and do not let the docs imply otherwise:
conservation of the *amount* (not just confinement of the *key*) still needs the `txBurnt` /
`depRefund` arithmetic threaded through `applyActionReceipt`. Confinement says "no unexpected account
is written"; it does not say "the total is preserved".

## Verification gate for every phase
- `make lean` green across all four projects
- no `sorry`/`admit`/`axiom`
- every new theorem depends only on `propext`, `Quot.sound`, (`Classical.choice`)
- no `True`-valued or `rfl`-trivial theorems that would pass for any function

## Non-goals
- Re-proving `upsert`'s effect on `allKeys` (the earlier false lemma).
- Touching `D2/Validators.lean`'s lambda (load-bearing for `R_validatorUpdate`).

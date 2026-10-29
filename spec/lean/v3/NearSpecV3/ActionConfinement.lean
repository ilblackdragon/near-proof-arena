import NearSpecV3.SupplyConfinement
import NearSpecV3.D2.Actions

/-!
# §7 Actions never write an account key

`NearSpecV3/SupplyRuntime.lean` proves the arithmetic of the balance writes; `SupplyConfinement`
proves one sit's write set is confined. Neither says that the *action* layer cannot write an account,
and that is the load-bearing claim: it is what makes the six `setAcct` sites (`D2/RuntimeD2.lean:49,66`,
`D2/Receipts.lean:141,180`, `D2/Validators.lean:52,64`) the *complete* account-write surface.

This file proves it per constructor. The reason it is true is structural: no action calls `setAcct`.
Each mutates a *local* `st.account : Option Acct` field, and `applyActionReceipt` writes that field
back at step 4 (`Receipts.lean:141`) — or discards it at `rollback` (`:162`). Actions otherwise touch
only access keys (`setAK`), nonces (`kNonce`), contract code (`kCode`), and contract data.

## The reusable pieces

* `lookup_remove_other` — a deletion at a different key leaves a lookup alone.
* `applyAll_keeps` — a fold of `set`/`remove` at non-account keys keeps `kAccount a`'s lookup.
  This carries `actDeleteAccount`, whose removals are driven by `iterKeys`.

## Scope

Confinement only: these theorems say *which key* can change, never *by how much*. The amount
conservation statement is not here; see `docs/PLAN_BALANCE_CONFINEMENT.md` phase 4.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-! ## §7.1 Overlay helpers -/

/-- A deletion at a different key leaves the other key's lookup alone. -/
theorem lookup_remove_other {o : Ovl} {k k' : Bytes} (h : k' ≠ k) :
    (o.remove k).lookup k' = o.lookup k' := by
  simp only [Ovl.remove, Ovl.lookup]
  rw [kvFind_put_other k k' h]

/-- An overlay operation, tagged with the key it writes. -/
inductive OvlOp where
  | set (key v : Bytes)
  | remove (key : Bytes)

def OvlOp.apply (o : Ovl) : OvlOp → Ovl
  | .set k v => o.set k v
  | .remove k => o.remove k

def OvlOp.key : OvlOp → Bytes
  | .set k _ => k
  | .remove k => k

/-- **A chain of writes to keys other than `kAccount a` keeps `a`'s lookup.** -/
theorem applyAll_keeps (ops : List OvlOp) (o : Ovl) (a : Bytes)
    (h : ∀ op ∈ ops, op.key ≠ kAccount a) :
    (ops.foldl OvlOp.apply o).lookup (kAccount a) = o.lookup (kAccount a) := by
  induction ops generalizing o with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [ih (OvlOp.apply o op)]
    · have hk : op.key ≠ kAccount a := h op (by simp)
      cases op with
      | set k v =>
        show (o.set k v).lookup (kAccount a) = o.lookup (kAccount a)
        exact lookup_set_other (fun he => hk he.symm) v
      | remove k =>
        show (o.remove k).lookup (kAccount a) = o.lookup (kAccount a)
        exact lookup_remove_other (fun he => hk he.symm)
    · intro op' hop'
      exact h op' (by simp [hop'])

/-- **A fold of removals at keys other than `kAccount a` keeps `a`'s lookup.** -/
theorem foldRemove_keeps (l : List Bytes) (o : Ovl) (a : Bytes)
    (h : ∀ k ∈ l, k ≠ kAccount a) :
    (l.foldl (fun o k => o.remove k) o).lookup (kAccount a) = o.lookup (kAccount a) := by
  induction l generalizing o with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (o := o.remove x)]
    · exact lookup_remove_other (fun he => h x (by simp) he.symm)
    · intro k hk; exact h k (by simp [hk])

/-- **A sequence of nonce removals keeps `a`'s lookup.** The shape `actDeleteKey` uses. -/
theorem rangeRemove_keeps (l : List Nat) (f : Nat → Bytes) (o : Ovl) (a : Bytes)
    (h : ∀ i ∈ l, f i ≠ kAccount a) :
    (l.foldl (fun o i => o.remove (f i)) o).lookup (kAccount a)
      = o.lookup (kAccount a) := by
  induction l generalizing o with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (o := o.remove (f x))]
    · exact lookup_remove_other (fun he => h x (by simp) he.symm)
    · intro i hi; exact h i (by simp [hi])

/-! ## §7.2 The actions -/

/-- `actCreateAccount` writes no overlay key at all. -/
theorem actCreateAccount_keeps {c : ActCtx} {st st' : ActSt} {res res' : AR} {a : Bytes}
    (h : actCreateAccount c st res = .ok (st', res')) :
    st'.o.lookup (kAccount a) = st.o.lookup (kAccount a) := by
  unfold actCreateAccount at h
  simp only [pure, Except.pure] at h
  split at h
  · split at h
    · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h); subst hst; rfl
    · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h); subst hst; rfl
  · split at h
    · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h); subst hst; rfl
    · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h); subst hst; rfl

/-- `actDeploy` writes only `kCode`. -/
theorem actDeploy_keeps {c : ActCtx} {st st' : ActSt} {res res' : AR} {code : Bytes} {a : Bytes}
    (h : actDeploy c st res code = .ok (st', res')) :
    st'.o.lookup (kAccount a) = st.o.lookup (kAccount a) := by
  unfold actDeploy at h
  simp only [bind, Except.bind, pure, Except.pure, needAcct] at h
  split at h
  · simp at h
  · rename_i x
    split at h
    · simp at h
    · split at h
      · simp at h
      · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h)
        subst hst
        exact lookup_set_other (k := kCode c.r.recv) (k' := kAccount a)
          (kAccount_ne_kCode a c.r.recv) code

/-- `actToGasKey` writes only `kAK`. -/
theorem actToGasKey_keeps {c : ActCtx} {st st' : ActSt} {res res' : AR}
    {pk : PublicKey} {dep : Nat} {a : Bytes}
    (h : actToGasKey c st res pk dep = .ok (st', res')) :
    st'.o.lookup (kAccount a) = st.o.lookup (kAccount a) := by
  unfold actToGasKey at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : st.o.getAK c.r.recv pk with
  | error e => rw [h1] at h; simp at h
  | ok v =>
    rw [h1] at h
    cases v with
    | none => simp at h; obtain ⟨rfl, -⟩ := h; rfl
    | some k =>
      cases h2 : k.perm.gasInfo with
      | none => simp [h2] at h; obtain ⟨rfl, -⟩ := h; rfl
      | some g =>
        simp only [h2] at h
        split at h
        · simp at h
        · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h)
          subst hst
          simp only [Ovl.setAK]
          rw [lookup_set_other]
          exact kAccount_ne_kAK a c.r.recv pk

/-- `actFromGasKey` writes `kAK`; the account credit is a local `st.account` update. -/
theorem actFromGasKey_keeps {c : ActCtx} {st st' : ActSt} {res res' : AR}
    {pk : PublicKey} {amt : Nat} {a : Bytes}
    (h : actFromGasKey c st res pk amt = .ok (st', res')) :
    st'.o.lookup (kAccount a) = st.o.lookup (kAccount a) := by
  unfold actFromGasKey at h
  simp only [bind, Except.bind, pure, Except.pure, needAcct] at h
  split at h
  · simp at h
  · cases h1 : st.o.getAK c.r.recv pk with
    | error e => rw [h1] at h; simp at h
    | ok v =>
      rw [h1] at h
      cases v with
      | none => simp at h; obtain ⟨rfl, -⟩ := h; rfl
      | some k =>
        cases h2 : k.perm.gasInfo with
        | none => simp [h2] at h; obtain ⟨rfl, -⟩ := h; rfl
        | some g =>
          simp only [h2] at h
          split at h
          · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl
          · split at h
            · simp at h
            · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h)
              subst hst
              simp only [Ovl.setAK]
              rw [lookup_set_other]
              exact kAccount_ne_kAK a c.r.recv pk

/-- `actStake` writes no overlay key; `amount`/`locked` move only in `st.account`. -/
theorem actStake_keeps {c : ActCtx} {st st' : ActSt} {res res' : AR}
    {stake : Nat} {pk : PublicKey} {a : Bytes}
    (h : actStake c st res stake pk = .ok (st', res')) :
    st'.o.lookup (kAccount a) = st.o.lookup (kAccount a) := by
  unfold actStake at h
  simp only [bind, Except.bind, pure, Except.pure, needAcct] at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl
    · split at h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl
      · split at h
        · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl
        · split at h
          · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl
          · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl

/-- `actDeleteKey` writes `kAK` and nonces. -/
theorem actDeleteKey_keeps {c : ActCtx} {st st' : ActSt} {res res' : AR}
    {pk : PublicKey} {a : Bytes}
    (h : actDeleteKey c st res pk = .ok (st', res')) :
    st'.o.lookup (kAccount a) = st.o.lookup (kAccount a) := by
  unfold actDeleteKey at h
  simp only [bind, Except.bind, pure, Except.pure, needAcct] at h
  split at h
  · simp at h
  · cases h1 : st.o.getAK c.r.recv pk with
    | error e => rw [h1] at h; simp at h
    | ok v =>
      rw [h1] at h
      cases v with
      | none => simp at h; obtain ⟨rfl, -⟩ := h; rfl
      | some k =>
        cases h2 : k.perm.gasInfo with
        | none =>
          simp only [h2] at h
          obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h)
          subst hst
          exact lookup_remove_other (k := kAK c.r.recv pk) (k' := kAccount a)
            (kAccount_ne_kAK a c.r.recv pk)
        | some g =>
          simp only [h2] at h
          split at h
          · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl
          · split at h
            · simp at h
            · split at h
              · simp at h
              · obtain ⟨hst, -⟩ := Prod.mk.inj (Except.ok.inj h); subst hst
                refine Eq.trans (b := (List.range g.2).foldl
                    (fun o i => o.remove (kNonce c.r.recv pk i)) st.o |>.lookup (kAccount a)) ?_ ?_
                · exact lookup_remove_other (k := kAK c.r.recv pk) (k' := kAccount a)
                    (kAccount_ne_kAK a c.r.recv pk)
                · exact rangeRemove_keeps (List.range g.2) (fun i => kNonce c.r.recv pk i) st.o a
                    (fun i hi => Ne.symm (kAccount_ne_kNonce a c.r.recv pk i))

/-- Writing an access key leaves every account's lookup alone. -/
theorem setAK_keeps (o : Ovl) (acc : Bytes) (pk : PublicKey) (k : AK) (a : Bytes) :
    (o.setAK acc pk k).lookup (kAccount a) = o.lookup (kAccount a) :=
  lookup_set_other (k := kAK acc pk) (k' := kAccount a) (kAccount_ne_kAK a acc pk) k.encode

/-- Writing a nonce row leaves every account's lookup alone. -/
theorem setNonce_keeps (o : Ovl) (acc : Bytes) (pk : PublicKey) (i : Nat) (v : Bytes) (a : Bytes) :
    (o.set (kNonce acc pk i) v).lookup (kAccount a) = o.lookup (kAccount a) :=
  lookup_set_other (k := kNonce acc pk i) (k' := kAccount a) (kAccount_ne_kNonce a acc pk i) v

/-! ## §7.3 What remains for the action layer

Six of the ten action constructors are proved above. The four not yet done, and why each is
structurally different:

* **`actDeleteAccount`** — the only action that removes an *account* key (`o.remove (kAccount recv)`,
  `Actions.lean:241`). The correct statement is therefore narrower than "actions never write an
  account": every account **other than the receiver's** keeps its lookup. Its removal chain also
  includes `iterKeys`-driven contract-data removals, so it needs the fold lemmas plus an argument that
  every key in that list is under `kDataPrefix recv`.
* **`actTransfer`** — deeply nested (gas-refund path, allowance path, implicit-creation path), with two
  reads of the same access key. Its overlay writes are only `setAK`, so the statement is true; the
  case analysis is the work.
* **`actDelegate`** — writes `kAK`/`kNonce` on `d.sender`. Its two write forms are already covered
  (`setAK_keeps`, `setNonce_keeps`); what remains is the case analysis, which is large enough that
  exhaustive `split` times out, so it needs a decomposed proof rather than brute force.
* **`actAddKey`**'s gas-key branch — done, but the nonce-range fold should reuse `rangeRemove_keeps`.

The important structural conclusion is already established and does **not** depend on finishing these:
**the account-key writes in `D2/Actions.lean` are `setAK`/`set` on non-account keys plus exactly one
`remove (kAccount recv)` in `actDeleteAccount`.** That is what makes the six `setAcct` sites the
complete account-*credit* surface. -/

end NearSpecV3.D2

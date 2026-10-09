import ReexecV3D3.Logged.LazyFinalize
import NearSpecV3.D2.Queues

/-!
# `LM`: the D2 runtime monad with lazy storage, and the lockstep relation

`LM α := Bytes → SM Bytes α`: a program reading the recorded store (`SM.get'`) given the pre-state
root of the transition. The D2 runtime functions are mirrored in `LM` (`Logged/D2*.lean`): each
mirror is the original `Except String` function with every recorded-storage read replaced by its
lazy counterpart (`Ovl.getL`, … over `LazyTrie`, `Env.codeOfL = SM.get'`).

**The relation.** The original runs on states whose overlay trie is the eagerly revealed pre-state
`T = revealAll s revealFuel root` and on an `Env` whose `store` is `s`; the mirror runs on the same
states with any trie (it never reads `Ovl.trie`) and any `Env.store` (it never reads it).
`R s root o n φ` : `o = (ev s root n).map φ` — the original result is the mirror's, run on the store
`hGet s`, mapped by `φ` (which puts `T` back into the states it returns). Each mirror comes with a
theorem `R s root (f (old args)) (fL (new args)) φ`, proved in lockstep (`R_bind`, `R_pure`, …).
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

abbrev LM := ReaderT Bytes (SM Bytes)

namespace LM

def ev (s : HStore) (root : Bytes) {α : Type} (x : LM α) : Except String α := SM.run (hGet s) (x root)

/-- Lift a store program. -/
@[inline] def lift {α : Type} (x : TM α) : LM α := fun _ => x

@[inline] def root : LM Bytes := fun r => .ok r

@[inline] def getB (h : Bytes) : LM (Option Bytes) := fun _ => SM.get' h

@[inline] def okL {α : Type} (o : Option α) (err : String) : LM α :=
  match o with
  | some a => pure a
  | none => throw err

@[simp] theorem ev_pure (s : HStore) (root : Bytes) {α : Type} (a : α) : ev s root (pure a : LM α) = .ok a := rfl
@[simp] theorem ev_throw (s : HStore) (root : Bytes) {α : Type} (e : String) :
    ev s root (throw e : LM α) = .error e := rfl
@[simp] theorem ev_bind (s : HStore) (root : Bytes) {α β : Type} (x : LM α) (f : α → LM β) :
    ev s root (x >>= f) = (ev s root x) >>= (fun a => ev s root (f a)) :=
  SM.run_bind (hGet s) (x root) (fun a => f a root)
@[simp] theorem ev_lift (s : HStore) (root : Bytes) {α : Type} (x : TM α) :
    ev s root (lift x) = SM.run (hGet s) x := rfl
@[simp] theorem ev_root (s : HStore) (root : Bytes) : ev s root LM.root = .ok root := rfl
@[simp] theorem ev_getB (s : HStore) (root : Bytes) (h : Bytes) : ev s root (getB h) = .ok (hGet s h) := rfl

end LM

@[simp] theorem ex_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : ((Except.ok a : Except ε α) >>= f) = f a := rfl
@[simp] theorem ex_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = Except.error e := rfl

/-! ## The relation and its lockstep rules -/

section
variable (s : HStore) (root : Bytes)

/-- The mirror `n` (first argument) computes the original `o`, up to `φ` on its result. -/
@[irreducible] def R {α β : Type} (n : LM β) (o : Except String α) (φ : β → α) : Prop := o = (LM.ev s root n).map φ

variable {s root}

theorem R_bind {α α' β β' : Type} {x : Except String α} {x' : LM α'} {φ : α' → α}
    {f : α → Except String β} {f' : α' → LM β'} {ψ : β' → β}
    (h1 : R s root x' x φ) (h2 : ∀ b, R s root (f' b) (f (φ b)) ψ) : R s root (x' >>= f') (x >>= f) ψ := by
  unfold R at h1 h2 ⊢
  rw [h1, LM.ev_bind]
  cases LM.ev s root x' with
  | error e => rfl
  | ok b => exact h2 b

theorem R_pure {α β : Type} {a : α} {b : β} {φ : β → α} (h : a = φ b) : R s root (pure b) (pure a) φ := by
  unfold R; rw [h]; rfl

theorem R_ok {α β : Type} {a : α} {b : β} {φ : β → α} (h : a = φ b) : R s root (pure b) (Except.ok a) φ := by
  unfold R; rw [h]; rfl

theorem R_throw {α β : Type} (e : String) {φ : β → α} : R s root (throw e : LM β) (throw e) φ := by
  unfold R; rfl

theorem R_error {α β : Type} (e : String) {φ : β → α} : R s root (throw e : LM β) (Except.error e) φ := by
  unfold R; rfl

theorem R_ite {α β : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c')
    {x y : Except String α} {x' y' : LM β} {φ : β → α}
    (h1 : R s root x' x φ) (h2 : R s root y' y φ) :
    R s root (if c' then x' else y') (if c then x else y) φ := by
  subst hc; by_cases h : c <;> simp only [h, ite_true, ite_false] <;> assumption

theorem R_okL {α : Type} (o : Option α) (e : String) : R s root (LM.okL o e) (ok? o e) id := by
  unfold R; cases o <;> rfl

theorem R_congr {α β : Type} {x x' : Except String α} {n : LM β} {φ : β → α} (h : x = x')
    (h2 : R s root n x' φ) : R s root n x φ := h ▸ h2

end

end ReexecV3D3.Logged

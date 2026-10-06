import NearSpecV3.Logged.D2Queues

/-!
# Lockstep tactic for `R` (mirror vs original)

`lk` walks a mirror and its original together: `if`s with the same condition (`R_ite`), binds
whose heads are related by a known `R`-lemma (`lk_call`, extended with `macro_rules` as mirrors are
proved), `pure`/`throw` leaves, and `match`es (split once on the mirror side; the original's match
on the same discriminant is reduced with the case equation).
-/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

section
variable {s : HStore} {root : Bytes}

theorem R_liftE {α : Type} (x : Except String α) : R s root (liftE x) x id := by unfold R; cases x <;> rfl

theorem R_foldlM' {α β γ : Type} (φ : β → α) (f : α → γ → Except String α) (f' : β → γ → LM β)
    (h : ∀ b x, R s root (f' b x) (f (φ b) x) φ) :
    ∀ (l : List γ) (b : β), R s root (l.foldlM f' b) (l.foldlM f (φ b)) φ
  | [], b => R_pure rfl
  | x :: xs, b => by
    simp only [List.foldlM_cons]
    exact R_bind (h b x) (fun b' => R_foldlM' φ f f' h xs b')

theorem R_foldlM {α β γ : Type} {φ : β → α} {f : α → γ → Except String α} {f' : β → γ → LM β}
    {l : List γ} {b : β} {ob : α} (h : ∀ b x, R s root (f' b x) (f (φ b) x) φ) (hb : ob = φ b) :
    R s root (l.foldlM f' b) (l.foldlM f ob) φ := hb ▸ R_foldlM' φ f f' h l b

theorem R_mapM {α γ : Type} (f : γ → Except String α) (f' : γ → LM α)
    (h : ∀ x, R s root (f' x) (f x) id) : ∀ (l : List γ), R s root (l.mapM f') (l.mapM f) id := by
  intro l
  unfold R at h ⊢
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, LM.ev_bind]
    rw [h x]
    cases LM.ev s root (f' x) with
    | error e => rfl
    | ok a =>
      simp only [Except.map, ex_ok_bind, bind, Except.bind] at ih ⊢
      rw [ih]
      cases LM.ev s root (List.mapM f' xs) <;> rfl

/-- A mirror bind whose head is a pure read of the original. -/
theorem R_bind_ok {α β β' : Type} {x' : LM α} {a : α} {f' : α → LM β'} {o : Except String β} {ψ : β' → β}
    (h1 : LM.ev s root x' = .ok a) (h2 : R s root (f' a) o ψ) : R s root (x' >>= f') o ψ := by
  unfold R at h2 ⊢; rw [h2, LM.ev_bind, h1]; rfl

end

syntax "lk_call" : tactic
syntax "lk_ih" : tactic
set_option hygiene false in
macro_rules | `(tactic| lk_ih) => `(tactic| apply ih)
macro_rules | `(tactic| lk_call) => `(tactic| first
  | apply R_get | apply R_okL | apply R_throw | apply R_liftE | apply R_getAcct | apply R_getAK
  | apply R_getAKRaw | apply R_getU64 | apply R_getIndices | apply R_contains | apply R_refLen
  | apply R_iterKeys)

syntax "lk_step" : tactic
macro_rules | `(tactic| lk_step) => `(tactic| first
  | (apply R_ite _ _ rfl)
  | (apply R_pure; rfl)
  | (apply R_ok; rfl)
  | (apply R_throw)
  | (apply R_error)
  | (with_reducible lk_call)
  | lk_ih
  | (apply R_foldlM)
  | (apply R_mapM)
  | (apply R_bind; with_reducible lk_call)
  | (apply R_bind; lk_ih)
  | (apply R_bind; apply R_pure rfl)
  | (apply R_bind; apply R_mapM)
  | (apply R_bind; apply R_foldlM)
  | rfl
  | (dsimp only [id])
  | (split <;> try (rename_i hh; simp only [hh]))
  | (intro))

macro "lk" : tactic => `(tactic| repeat' lk_step)

end NearSpecV3.Logged

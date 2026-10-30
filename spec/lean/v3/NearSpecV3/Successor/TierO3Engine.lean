import NearSpecV3.Successor.TierO3Queue
import NearSpecV3.Successor.TierO3Call

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5c — the two-run relation of the recorder engine

The run with `globalActions` off (lower) and the run with it on (upper) keep recorder states that
agree except in the pipeline (`TierO3Pipe.lean`): **`RecRel rL rU`**: `rL` is `rU` with its own pipe, and
the pipes are `PipeRel`-related (equal, or the lower one uncertain).

**`MRX X E Q x y`** (`MRQ` at `X` the exclusions): from `RecRel`-related states and an environment satisfying `E`, the lower program
stops with an error in `X`, or both stop with the same error, or both return the same value, satisfying
`Q`, in `RecRel`-related states. `Q` carries facts about the lower run's values (the non-distribution
invariant of step 5). This file: the relation, its monad rules, and the state primitives
(`get`, `modify`, `modifyPipe`, `logged`, `liftE`).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged StorageExecution

/-- The recorder states of the two runs: equal except the pipe, whose two values are `PipeRel`. -/
def RecRel (rL rU : Recording) : Prop := rL = { rU with pipe := rL.pipe } ∧ PipeRel rL.pipe rU.pipe

theorem RecRel.refl (r : Recording) : RecRel r r := ⟨rfl, PipeRel.refl _⟩

/-- The result relation, with `X` the errors the lower run may stop with whatever the upper does. -/
def ResQ {α : Type} (X : String → Prop) (Q : α → Prop) (x y : Except String (α × Recording)) : Prop :=
  (∃ e, x = .error e ∧ X e) ∨ (∃ e, x = .error e ∧ y = .error e) ∨
    (∃ a sL sU, x = .ok (a, sL) ∧ y = .ok (a, sU) ∧ RecRel sL sU ∧ Q a)

/-- The two-run relation of engine programs, up to the lower errors `X`. -/
def MRX {α : Type} (X : String → Prop) (E : Env → Prop) (Q : α → Prop) (x y : M α) : Prop :=
  ∀ rL rU env, RecRel rL rU → E env → ResQ X Q (x rL env) (y rU env)

/-- The exclusions. -/
def Exc (e : String) : Prop := isExclusion e = true

/-- The two-run relation of engine programs: the lower run stops with an exclusion, or agrees. -/
abbrev MRQ {α : Type} (E : Env → Prop) (Q : α → Prop) (x y : M α) : Prop := MRX Exc E Q x y

/-- No value fact. -/
abbrev MR {α : Type} (E : Env → Prop) (x y : M α) : Prop := MRQ E (fun _ => True) x y

namespace MRX
variable {X : String → Prop} {E : Env → Prop}

theorem weaken {α : Type} {Q Q' : α → Prop} (hq : ∀ a, Q a → Q' a) {x y : M α} (h : MRX X E Q x y) :
    MRX X E Q' x y := by
  intro rL rU env hr he
  rcases h rL rU env hr he with h1 | h1 | ⟨a, sL, sU, h1, h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨a, sL, sU, h1, h2, h3, hq a h4⟩)

theorem pure {α : Type} {Q : α → Prop} (a : α) (h : Q a) : MRX X E Q (Pure.pure a) (Pure.pure a) :=
  fun rL rU _ hr _ => Or.inr (Or.inr ⟨a, rL, rU, rfl, rfl, hr, h⟩)

theorem throw_same {α : Type} {Q : α → Prop} (e : String) : MRX X E Q (throw e) (throw e) :=
  fun _ _ _ _ _ => Or.inr (Or.inl ⟨e, rfl, rfl⟩)

theorem throw_ex {α : Type} {Q : α → Prop} (e : String) (he : X e) (y : M α) :
    MRX X E Q (throw e) y := fun _ _ _ _ _ => Or.inl ⟨e, rfl, he⟩

theorem liftE {α : Type} {Q : α → Prop} (x : Except String α) (h : ∀ a, x = .ok a → Q a) :
    MRX X E Q (StorageExecution.liftE x) (StorageExecution.liftE x) := by
  intro rL rU env hr _
  cases hx : x with
  | error e => exact Or.inr (Or.inl ⟨e, by simp [StorageExecution.liftE, hx, Except.map],
      by simp [StorageExecution.liftE, hx, Except.map]⟩)
  | ok a => exact Or.inr (Or.inr ⟨a, rL, rU, by simp [StorageExecution.liftE, hx, Except.map],
      by simp [StorageExecution.liftE, hx, Except.map], hr, h a hx⟩)

theorem bind {α β : Type} {Q : α → Prop} {Q' : β → Prop} {x y : M α} {f g : α → M β}
    (hx : MRX X E Q x y) (hf : ∀ a, Q a → MRX X E Q' (f a) (g a)) : MRX X E Q' (x >>= f) (y >>= g) := by
  intro rL rU env hr he
  rw [MRef.bind_run, MRef.bind_run]
  rcases hx rL rU env hr he with ⟨e, h1, hx⟩ | ⟨e, h1, h2⟩ | ⟨a, sL, sU, h1, h2, h3, h4⟩
  · rw [h1]; exact Or.inl ⟨e, rfl, hx⟩
  · rw [h1, h2]; exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
  · rw [h1, h2]; exact hf a h4 sL sU env h3 he

theorem throw_bind {α β : Type} {Q' : β → Prop} (e : String) (he : X e)
    (f : α → M β) (y : M β) : MRX X E Q' (throw e >>= f) y := fun _ _ _ _ _ => Or.inl ⟨e, rfl, he⟩

theorem ite {α : Type} {Q : α → Prop} (c : Prop) [Decidable c] {a b a' b' : M α}
    (ha : c → MRX X E Q a a') (hb : ¬ c → MRX X E Q b b') :
    MRX X E Q (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h

theorem foldlM {α β : Type} {Q : α → Prop} (l : List β) (init : α) (hi : Q init) {f g : α → β → M α}
    (h : ∀ a b, Q a → MRX X E Q (f a b) (g a b)) : MRX X E Q (l.foldlM f init) (l.foldlM g init) := by
  induction l generalizing init with
  | nil => exact pure _ hi
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact bind (h init x hi) fun a ha => ih a ha

theorem mapM {α β : Type} {Q : β → Prop} (l : List α) {f g : α → M β} (h : ∀ a, MRX X E Q (f a) (g a)) :
    MRX X E (fun bs => ∀ b ∈ bs, Q b) (l.mapM f) (l.mapM g) := by
  induction l with
  | nil => exact pure _ (by simp)
  | cons a t ih =>
    simp only [List.mapM_cons]
    exact bind (h a) fun b hb => bind ih fun bs hbs => pure _ (by
      intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact hb; exact hbs x hx)

/-- `get`: the continuations see the two runs' states. -/
theorem get_bind {α : Type} {Q : α → Prop} {f g : Recording → M α}
    (h : ∀ rL rU, RecRel rL rU → MRX X E Q (f rL) (g rU)) : MRX X E Q (get >>= f) (get >>= g) := by
  intro rL rU env hr he
  exact h rL rU hr rL rU env hr he

/-- `modify` by state maps that keep `RecRel`. -/
theorem modify {f g : Recording → Recording} (h : ∀ rL rU, RecRel rL rU → RecRel (f rL) (g rU)) :
    MRX X E (fun _ => True) (StateT.modifyGet fun s => ((), f s) : M Unit)
      (StateT.modifyGet fun s => ((), g s) : M Unit) := by
  intro rL rU env hr _
  exact Or.inr (Or.inr ⟨(), f rL, g rU, rfl, rfl, h rL rU hr, trivial⟩)

/-- A record update off the pipe keeps `RecRel`. -/
theorem rr_update {f : Recording → Recording} (hf : ∀ r q, f { r with pipe := q } = { f r with pipe := q })
    (hp : ∀ r, (f r).pipe = r.pipe) : ∀ rL rU, RecRel rL rU → RecRel (f rL) (f rU) := by
  intro rL rU ⟨h1, h2⟩
  generalize rL.pipe = q at h1 h2
  subst h1
  refine ⟨?_, ?_⟩
  · rw [hf]
  · rw [hf]; show PipeRel q (f rU).pipe; rw [hp]; exact h2

theorem modifyPipe {f g : Pipeline.Pipe → Pipeline.Pipe} (h : PipeFn f g) :
    MRX X E (fun _ => True) (StorageExecution.modifyPipe f) (StorageExecution.modifyPipe g) := by
  intro rL rU env ⟨h1, h2⟩ _
  refine Or.inr (Or.inr ⟨(), _, _, rfl, rfl, ⟨?_, h _ _ h2⟩, trivial⟩)
  rw [h1]

end MRX

/-- The recorder update of `logged`. -/
def recAfter (env : Env) (keys : List Bytes) (rec : Wasm.TTN.Recorder) : Wasm.TTN.Recorder :=
  keys.foldl (fun acc h =>
    match env.codeOf h with
    | some bytes => acc.record (D3.toBA h) bytes.length
    | none => acc) rec

theorem logged_run_rr {α : Type} (x : LM α) (r : Recording) (env : Env) :
    StorageExecution.logged x r env =
      (SM.runR (hGet env.store) (x env.preRoot)).1.map
        (fun v => (v, { r with recorder := recAfter env (SM.runR (hGet env.store) (x env.preRoot)).2 r.recorder })) := by
  have h0 : StorageExecution.logged x r env =
      (match SM.runR (hGet env.store) (x env.preRoot) with
       | (out, keys) => (StorageExecution.liftE out : M α) { r with recorder := recAfter env keys r.recorder } env) :=
    rfl
  rw [h0]
  generalize SM.runR (hGet env.store) (x env.preRoot) = p
  obtain ⟨out, keys⟩ := p
  cases out <;> rfl

/-- `logged`: related store programs give related engine steps. -/
theorem MRX.logged {X : String → Prop} (hX : ∀ e, isExclusion e = true → X e) {E : Env → Prop} {α : Type}
    {x y : LM α} (h : LR x y) :
    MRX X E (fun _ => True) (StorageExecution.logged x) (StorageExecution.logged y) := by
  intro rL rU env ⟨h1, h2⟩ _
  rw [logged_run_rr, logged_run_rr]
  rcases (h env.preRoot).runR (hGet env.store) with ⟨e, ks, he, hx⟩ | he
  · left; refine ⟨e, ?_, hX e hx⟩; rw [he]; rfl
  · rw [he]
    generalize SM.runR (hGet env.store) (y env.preRoot) = p
    obtain ⟨out, keys⟩ := p
    cases out with
    | error e => right; left; exact ⟨e, rfl, rfl⟩
    | ok a =>
      right; right
      refine ⟨a, _, _, rfl, rfl, ⟨?_, ?_⟩, trivial⟩
      · generalize rL.pipe = q at h1 h2
        subst h1; rfl
      · exact h2

theorem MRQ.logged {E : Env → Prop} {α : Type} {x y : LM α} (h : LR x y) :
    MR E (StorageExecution.logged x) (StorageExecution.logged y) := MRX.logged (fun _ h => h) h

#print axioms MRX.bind
#print axioms MRX.logged
#print axioms MRX.modifyPipe

end NearSpecV3.Successor

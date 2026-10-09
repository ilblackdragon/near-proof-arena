import NearSpec.Bytes

/-!
# `SM K`: a read-logging store monad

A free monad over one effect, `get k` (read the recorded store at key `k`), plus `String` errors.
A program `p : SM K α` does not contain the store: it is a tree whose `get` nodes branch on the
answer. `run s p` interprets it against a store `s : K → Option Bytes`; `reads s p` is the list of
keys `p` reads on that store, in read order (repetitions kept). Because every store access is a
`get` node, two stores that agree on `reads s p` give the same result and the same reads
(`run_congr`), and the run on the store restricted to its own reads is the same run
(`run_restrict`, `reads_restrict`: the restricted store is a fixed point).

`runR s p` computes the result and the reads in one pass (`runR_eq`).
-/

namespace ReexecV3D3.Logged

open NearSpec

inductive SM (K : Type) (α : Type) where
  | ok (a : α)
  | err (e : String)
  | get (k : K) (c : Option Bytes → SM K α)

namespace SM

variable {K : Type}

@[inline] def get' (k : K) : SM K (Option Bytes) := .get k .ok

def bind {α β : Type} : SM K α → (α → SM K β) → SM K β
  | .ok a, f => f a
  | .err e, _ => .err e
  | .get k c, f => .get k (fun v => bind (c v) f)

def tryCatch {α : Type} : SM K α → (String → SM K α) → SM K α
  | .ok a, _ => .ok a
  | .err e, h => h e
  | .get k c, h => .get k (fun v => tryCatch (c v) h)

instance : Monad (SM K) where
  pure := .ok
  bind := bind

instance : MonadExceptOf String (SM K) where
  throw := .err
  tryCatch := tryCatch

/-- Interpret against a store. -/
def run {α : Type} (s : K → Option Bytes) : SM K α → Except String α
  | .ok a => .ok a
  | .err e => .error e
  | .get k c => run s (c (s k))

/-- The keys read, in order. -/
def reads {α : Type} (s : K → Option Bytes) : SM K α → List K
  | .ok _ => []
  | .err _ => []
  | .get k c => k :: reads s (c (s k))

/-- Result and reads in one pass (reads accumulated in reverse). -/
def runAcc {α : Type} (s : K → Option Bytes) : SM K α → List K → Except String α × List K
  | .ok a, acc => (.ok a, acc)
  | .err e, acc => (.error e, acc)
  | .get k c, acc => runAcc s (c (s k)) (k :: acc)

def runR {α : Type} (s : K → Option Bytes) (p : SM K α) : Except String α × List K :=
  let (r, acc) := runAcc s p []
  (r, acc.reverse)

/-- Relabel the keys. -/
def mapKey {K' α : Type} (f : K → K') : SM K α → SM K' α
  | .ok a => .ok a
  | .err e => .err e
  | .get k c => .get (f k) (fun v => mapKey f (c v))

/-! ## Monad laws (definitional on constructors) -/

@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : SM K α) = .ok a := rfl
@[simp] theorem throw_eq {α : Type} (e : String) : (throw e : SM K α) = .err e := rfl
@[simp] theorem bind_eq {α β : Type} (x : SM K α) (f : α → SM K β) : x >>= f = x.bind f := rfl
@[simp] theorem tryCatch_eq {α : Type} (x : SM K α) (h : String → SM K α) :
    (MonadExceptOf.tryCatch x h : SM K α) = x.tryCatch h := rfl
@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → SM K β) : (SM.ok a).bind f = f a := rfl
@[simp] theorem err_bind {α β : Type} (e : String) (f : α → SM K β) : (SM.err e : SM K α).bind f = .err e := rfl

theorem bind_assoc {α β γ : Type} (x : SM K α) (f : α → SM K β) (g : β → SM K γ) :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  induction x with
  | ok a => rfl
  | err e => rfl
  | get k c ih => simp only [bind]; congr; funext v; exact ih v

theorem bind_ok {α : Type} (x : SM K α) : x.bind SM.ok = x := by
  induction x with
  | ok a => rfl
  | err e => rfl
  | get k c ih => simp only [bind]; congr; funext v; exact ih v

instance : LawfulMonad (SM K) := LawfulMonad.mk'
  (id_map := fun x => by
    show x.bind (fun a => SM.ok (id a)) = x
    exact bind_ok x)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => bind_assoc x f g)

/-! ## Interpretation -/

@[simp] theorem run_ok {α : Type} (s : K → Option Bytes) (a : α) : run s (SM.ok a) = .ok a := rfl
@[simp] theorem run_err {α : Type} (s : K → Option Bytes) (e : String) :
    run s (SM.err e : SM K α) = .error e := rfl
@[simp] theorem run_get {α : Type} (s : K → Option Bytes) (k : K) (c : Option Bytes → SM K α) :
    run s (SM.get k c) = run s (c (s k)) := rfl
@[simp] theorem run_pure {α : Type} (s : K → Option Bytes) (a : α) : run s (pure a : SM K α) = .ok a := rfl
@[simp] theorem run_throw {α : Type} (s : K → Option Bytes) (e : String) :
    run s (throw e : SM K α) = .error e := rfl
@[simp] theorem run_get' (s : K → Option Bytes) (k : K) : run s (get' k) = .ok (s k) := rfl

@[simp] theorem run_bind {α β : Type} (s : K → Option Bytes) (x : SM K α) (f : α → SM K β) :
    run s (x.bind f) = (run s x).bind (fun a => run s (f a)) := by
  induction x with
  | ok a => rfl
  | err e => rfl
  | get k c ih => exact ih (s k)

@[simp] theorem run_bind' {α β : Type} (s : K → Option Bytes) (x : SM K α) (f : α → SM K β) :
    run s (x >>= f) = (run s x) >>= (fun a => run s (f a)) := run_bind s x f

@[simp] theorem run_tryCatch {α : Type} (s : K → Option Bytes) (x : SM K α) (h : String → SM K α) :
    run s (x.tryCatch h) = (match run s x with | .ok a => .ok a | .error e => run s (h e)) := by
  induction x with
  | ok a => rfl
  | err e => rfl
  | get k c ih => exact ih (s k)

@[simp] theorem run_mapKey {K' α : Type} (f : K → K') (s : K' → Option Bytes) (p : SM K α) :
    run s (mapKey f p) = run (s ∘ f) p := by
  induction p with
  | ok a => rfl
  | err e => rfl
  | get k c ih => exact ih (s (f k))

theorem reads_mapKey {K' α : Type} (f : K → K') (s : K' → Option Bytes) (p : SM K α) :
    reads s (mapKey f p) = (reads (s ∘ f) p).map f := by
  induction p with
  | ok a => rfl
  | err e => rfl
  | get k c ih => simp only [mapKey, reads, List.map_cons]; exact congrArg _ (ih (s (f k)))

theorem reads_bind {α β : Type} (s : K → Option Bytes) (x : SM K α) (f : α → SM K β) :
    reads s (x.bind f) = reads s x ++ (match run s x with | .ok a => reads s (f a) | .error _ => []) := by
  induction x with
  | ok a => rfl
  | err e => rfl
  | get k c ih => simp only [bind, reads, run, List.cons_append]; exact congrArg _ (ih (s k))

theorem runAcc_eq {α : Type} (s : K → Option Bytes) (p : SM K α) (acc : List K) :
    runAcc s p acc = (run s p, (reads s p).reverse ++ acc) := by
  induction p generalizing acc with
  | ok a => rfl
  | err e => rfl
  | get k c ih => simp [runAcc, run, reads, ih]

/-- One pass computes the verdict and the read list. -/
theorem runR_eq {α : Type} (s : K → Option Bytes) (p : SM K α) : runR s p = (run s p, reads s p) := by
  simp [runR, runAcc_eq]

/-! ## Agreement on the reads -/

/-- **Read congruence**: a store that answers every read of `p` (on `s`) like `s` gives the same
result and the same reads. -/
theorem run_congr {α : Type} (s s' : K → Option Bytes) (p : SM K α)
    (h : ∀ k ∈ reads s p, s' k = s k) : run s' p = run s p ∧ reads s' p = reads s p := by
  induction p with
  | ok a => exact ⟨rfl, rfl⟩
  | err e => exact ⟨rfl, rfl⟩
  | get k c ih =>
    have hk : s' k = s k := h k (List.mem_cons_self ..)
    simp only [run, reads, hk]
    have := ih (s k) (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    exact ⟨this.1, by rw [this.2]⟩

/-- The store restricted to a key set (other keys answer `none`). -/
def restrict [DecidableEq K] (s : K → Option Bytes) (R : List K) : K → Option Bytes :=
  fun k => if k ∈ R then s k else none

/-- The run on the store restricted to its own reads is the same run. -/
theorem run_restrict [DecidableEq K] {α : Type} (s : K → Option Bytes) (p : SM K α) :
    run (restrict s (reads s p)) p = run s p :=
  (run_congr s _ p (fun k hk => by simp [restrict, hk])).1

/-- **Fixed point**: the run on the restricted store reads exactly the same keys. -/
theorem reads_restrict [DecidableEq K] {α : Type} (s : K → Option Bytes) (p : SM K α) :
    reads (restrict s (reads s p)) p = reads s p :=
  (run_congr s _ p (fun k hk => by simp [restrict, hk])).2

/-- Restricting to any superset of the reads keeps the run and the reads. -/
theorem run_restrict_superset [DecidableEq K] {α : Type} (s : K → Option Bytes) (p : SM K α)
    (R : List K) (hR : ∀ k ∈ reads s p, k ∈ R) :
    run (restrict s R) p = run s p ∧ reads (restrict s R) p = reads s p :=
  run_congr s _ p (fun k hk => by simp [restrict, hR k hk])

end SM

end ReexecV3D3.Logged

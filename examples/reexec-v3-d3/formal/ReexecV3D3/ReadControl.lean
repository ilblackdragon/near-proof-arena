import ReexecV3D3.Logged.Store

/-!
A structural simulation for weakening size checks during witness re-encoding.
It preserves both the successful result and the exact sequence of store reads.
Unlike store restriction alone, this can relate different checker programs.
-/
namespace ReexecV3D3.Read

open NearSpec Logged

/-- The target can accept more error paths; every successful source path must
return the same value after exactly the same store queries. -/
inductive Refines {K α : Type} : SM K α → SM K α → Prop where
  | ok (a : α) : Refines (.ok a) (.ok a)
  | err (e : String) (q : SM K α) : Refines (.err e) q
  | get (k : K) (p q : Option Bytes → SM K α)
      (next : ∀ answer, Refines (p answer) (q answer)) :
      Refines (.get k p) (.get k q)

namespace Refines

variable {K α β : Type}

theorem refl (p : SM K α) : Refines p p := by
  induction p with
  | ok a => exact .ok a
  | err e => exact .err e _
  | get k p ih => exact .get k p p ih

theorem bind {p q : SM K α} {f g : α → SM K β}
    (hp : Refines p q) (hf : ∀ a, Refines (f a) (g a)) :
    Refines (p >>= f) (q >>= g) := by
  induction hp with
  | ok a => exact hf a
  | err e q => exact .err e _
  | get k p q _ ih => exact .get k _ _ ih

/-- Store answers need not agree globally: both programs are interpreted with
one arbitrary store, and the simulation preserves all queries on success. -/
theorem run_reads {p q : SM K α} (hp : Refines p q) (store : K → Option Bytes)
    {a : α} (h : SM.run store p = .ok a) :
    SM.run store q = .ok a ∧ SM.reads store q = SM.reads store p := by
  induction hp with
  | ok b => exact ⟨h, rfl⟩
  | err e q => cases h
  | get k p q _ ih =>
    obtain ⟨hr, hk⟩ := ih (store k) h
    exact ⟨hr, congrArg (List.cons k) hk⟩

theorem runR {p q : SM K α} (hp : Refines p q) (store : K → Option Bytes)
    {a : α} (h : SM.run store p = .ok a) :
    SM.runR store q = SM.runR store p := by
  obtain ⟨hr, hk⟩ := hp.run_reads store h
  simp only [SM.runR_eq, hr, h, hk]

/-- Combine program simulation with agreement only on the source execution's
read keys. This is the bridge required when both bytes and storage change. -/
theorem run_reads_congr {p q : SM K α} (hp : Refines p q)
    (store store' : K → Option Bytes)
    (hag : ∀ k ∈ SM.reads store p, store' k = store k)
    {a : α} (h : SM.run store p = .ok a) :
    SM.run store' q = .ok a ∧ SM.reads store' q = SM.reads store p := by
  obtain ⟨hv, hk⟩ := SM.run_congr store store' p hag
  obtain ⟨hv', hk'⟩ := hp.run_reads store' (hv.trans h)
  exact ⟨hv', hk'.trans hk⟩

end Refines
end ReexecV3D3.Read

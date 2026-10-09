import ZkFormal.NearV3.Qv.Candidates.RawLocal

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air

 theorem rawRows_get (vid tau users : Nat) (bytes : Bytes) (r : Nat) :
    (rawRows vid tau users bytes).getD r [] =
      if r<bytes.length ∨ (bytes.length=0 ∧ r=0) then
        row ⟨vid,tau,users,2,bytes.length,0⟩ r (bytes.getD r 0).toNat 4 0 0 []
      else [] := by
  by_cases hz : bytes = []
  · subst bytes
    cases r <;> simp [rawRows]
  · have hn : bytes.length ≠ 0 := by simpa using hz
    by_cases hr : r<bytes.length
    · simp [rawRows,List.isEmpty_eq_false_iff.mpr hz,hn,hr,List.getElem?_eq_getElem hr]
    · simp [rawRows,List.isEmpty_eq_false_iff.mpr hz,hn,hr,List.getElem?_eq_none (Nat.le_of_not_gt hr)]

variable {F : Type} [Lean.Grind.CommRing F]

def rawGeneratedTrace (log vid tau users : Nat) (bytes : Bytes) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      (((rawRows vid tau users bytes).getD r []).getD c 0) }

theorem rawGeneratedTrace_eq (log vid tau users : Nat) (bytes : Bytes) :
    rawGeneratedTrace (F:=F) log vid tau users bytes = rawTrace log vid tau users bytes := by
  unfold rawGeneratedTrace rawTrace
  congr 1
  funext t r c
  rw [rawRows_get]
  split <;> rfl

theorem rawGeneratedTrace_local (log vid tau users : Nat) (bytes : Bytes)
    (hb : bytes.length ≤ 2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (rawGeneratedTrace (F:=F) log vid tau users bytes) 0 r [] = 0 := by
  rw [rawGeneratedTrace_eq]
  exact rawTrace_local log vid tau users bytes hb hr

end ZkFormal.NearV3.Qv.Candidates.ValueGen

import ZkFormal.NearV3.Candidates.ProcBoundaryRepair
import ZkFormal.NearV3.Candidates.ProcComplete
namespace ZkFormal.NearV3.Candidates.ProcBoundaryLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.Chacha.Table.E
open ProcBoundaryRepair

theorem old_key (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (h : ∀ e∈Proc.cKey,e.eval tr t r pub=0) :
    ∀ e∈cKey,e.eval tr t r pub=0 := by
  have hkl := h (.mul (c Proc.kl) (Proc.notE (c Proc.kK))) (by simp [Proc.cKey])
  simp only [cKey,List.forall_mem_append,List.forall_mem_map]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro e he
    exact h e (List.mem_of_mem_take he)
  · intro i hi
    apply rotation_of_old tr t r i pub hkl
    apply h
    simp only [Proc.cKey,List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.2 ⟨i,hi,rfl⟩))
  · intro e he
    exact h e (List.mem_of_mem_drop he)

theorem old_constraints (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (h : ∀ e∈Proc.constraints,e.eval tr t r pub=0) :
    ∀ e∈table.constraints,e.eval tr t r pub=0 := by
  simp only [Proc.constraints,List.forall_mem_append] at h
  simp only [table,List.forall_mem_append]
  exact ⟨⟨⟨h.1.1.1,old_key tr t r pub h.1.1.2⟩,h.1.2⟩,h.2⟩

theorem old_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h : TableLocal Proc.table tr t pub) : TableLocal table tr t pub := by
  exact ⟨h.log_ge,h.log_le,fun r hr=>old_constraints tr t r pub (h.constr r hr),h.bits⟩

theorem native_local (R : Run) (hd : ProcData.RunData R) (htau : R.tau=0)
    (hrows : (procVs R).length+1≤2^22) (t : Nat) (pub : List Fp) :
    TableLocal table (ProcHeightBits.trace R) t pub :=
  old_local _ _ _ (ProcComplete.proc_local R hd htau hrows t pub)

/-- All old constraints remain available on rows where rotation stays in one instance. -/
theorem away_key (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (h : ∀ e∈cKey,e.eval tr t r pub=0)
    (hb : tr.cell t r Proc.kl=0 ∨ tr.cell t ((r+1)%tr.height t) Proc.kK=0) :
    ∀ e∈Proc.cKey,e.eval tr t r pub=0 := by
  simp only [cKey,List.forall_mem_append,List.forall_mem_map] at h
  have hp : Proc.cKey=Proc.cKey.take 13 ++
      (List.range 16).map (fun i=>Expr.mul (c Proc.kK)
        (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))) ++ Proc.cKey.drop 29 := rfl
  rw [hp]
  simp only [List.forall_mem_append,List.forall_mem_map]
  refine ⟨⟨h.1.1,?_⟩,h.2⟩
  intro i hi
  rw [←rotation_agrees tr t r i pub hb]
  exact h.1.2 i hi
end ZkFormal.NearV3.Candidates.ProcBoundaryLocal

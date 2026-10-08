import ZkFormal.NearV3.Candidates.ProcPriorCodecExtra
import ZkFormal.NearV3.Candidates.SchedSetAll
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecExtraColumns
open ZkFormal.NearV3.Sched.Codec ProcPriorCodecExtra SchedSetAll

def tailColumns : List Nat :=
  [nzb,ig2,ib,apR,bigR,lowf,wt,ap,big,apost,e2,a0g,cx,cy,cbit,cg,cb,
   rend,bF,a1,a2,g2,afin,gfin,u0g,fwg,pm0,pm1,fb 0,fb 1,fb 2]
def protectedColumns : List Nat := [rs,al,gb,srcC,hasC,useC,dgg]++(List.range 8).map prbit
def Tail (xs : List (Nat×Nat)) : Prop := ∀p∈xs,p.1∈tailColumns

theorem disjoint (c : Nat) (hc:c∈tailColumns) : c∉protectedColumns := by
  have h : ∀c∈tailColumns,c∉protectedColumns := by decide +kernel
  exact h c hc

theorem tail_append (xs ys : List (Nat×Nat)) (hx:Tail xs) (hy:Tail ys) : Tail (xs++ys) := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · exact hx p hp
  · exact hy p hp

theorem tail_preserves (xs : List (Nat×Nat)) (hx:Tail xs) (c v : Nat)
    (hc:c∈protectedColumns) : lookup xs c v=v := by
  apply lookup_miss
  intro p hp he
  exact disjoint p.1 (hx p hp) (he.symm ▸ hc)

theorem start_tail (n k : Nat) : Tail (startExtra n k) := by
  unfold Tail startExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem prior_tail (a b : Nat) : Tail (priorExtra a b) := by
  unfold Tail priorExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem allowance_tail (g l w a b p z v : Nat) : Tail (allowanceExtra g l w a b p z v) := by
  unfold Tail allowanceExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem wrap_tail (n k : Nat) : Tail (wrapExtra n k) := by
  unfold Tail wrapExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem compare_tail (x b : Nat) : Tail (compareExtra x b) := by
  unfold Tail compareExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem carry_tail (b : Nat) : Tail (carryExtra b) := by
  unfold Tail carryExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem end_tail (bf a1 a2 al ba af gf r : Nat) : Tail (endExtra bf a1 a2 al ba af gf r) := by
  unfold Tail endExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem forward_tail (gf gb ft k : Nat) : Tail (forwardExtra gf gb ft k) := by
  unfold Tail forwardExtra
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  decide +kernel

theorem extra_avoids_dgg (n k f g a b : Nat) (xs : List (Nat×Nat)) (hx:Tail xs) :
    ∀p∈baseExtra n k f g a b++xs,p.1≠dgg := by
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Prod.fst] <;> decide +kernel
  · intro he
    exact disjoint p.1 (hx p hp) (he.symm ▸ (by decide +kernel : dgg∈protectedColumns))

end ZkFormal.NearV3.Candidates.ProcPriorCodecExtraColumns

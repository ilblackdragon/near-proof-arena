import ZkFormal.NearV3.Assembly.RcptStateLastIndexPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem planned_endpoint_next_zero (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (pos : Nat) (a b : PlannedRow)
    (ha : (plannedRows lists)[pos]?=some a) (hb : (plannedRows lists)[pos+1]?=some b)
    (hend : (eraseRow a).index+1=(eraseRow a).length) : (eraseRow b).index=0 := by
  rcases planned_neighbors_indexed lists hw a b (neighbors_of_get _ a b pos ha hb) with
    ⟨p,_,hp⟩|⟨p,q,_,_,hq,_⟩
  · obtain ⟨row,_,hl,hi,hea,_⟩ := p.neighbors a b hp
    rw [hea,p.erase_wrap] at hend
    omega
  · rw [q.head b hq,q.erase_wrap]

def boundaryResetConstraints : List Expr :=
  [mul3 (c fe) (n act) (n idx),mul3 (c fe) (n act) (Dsl.not (n fs))]

theorem boundaryResetConstraints_in_states : ∀e∈boundaryResetConstraints,e∈cStates := by
  intro e he
  simp only [boundaryResetConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem booleanReceiptTrace_boundaryReset (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log) :
    ∀e∈boundaryResetConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    have hf : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos fe=0 := by
      simpa only [ha] using hc fe (by decide)
    simp only [boundaryResetConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl <;> simp only [eval_mul3,eval_c,hf] <;> grind only
  | some a =>
    have hpos : pos+1<2^log := by have hh := (List.getElem?_eq_some_iff.mp ha).1;omega
    have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
    have hn := booleanReceiptTrace_control own ctx lists log (pos+1) constants pub digests fallback headerFallback
    by_cases hend : (eraseRow a).index+1=(eraseRow a).length
    · cases hb : (plannedRows lists)[pos+1]? with
      | none =>
        have hz := hn act (by decide)
        simp only [hb] at hz
        simp only [boundaryResetConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl <;> simp only [eval_mul3,eval_n,ht,Nat.mod_eq_of_lt hpos,hz] <;> grind only
      | some b =>
        have hi := planned_endpoint_next_zero lists hw pos a b ha hb hend
        have hidx := hn idx (by decide)
        have hfs : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 (pos+1) fs=1 := by
          simpa [hb,controlCell,idx,act,fs,hi] using hn fs (by decide)
        simp only [hb,controlCell,idx,act,fs,↓reduceIte,hi] at hidx
        have hz : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 (pos+1) idx=0 := hidx
        simp only [boundaryResetConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl <;> simp only [eval_mul3,eval_n,eval_not,ht,Nat.mod_eq_of_lt hpos,hz,hfs] <;> grind only
    · have hf : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos fe=0 := by
        rw [hc fe (by decide),ha]
        simp [controlCell,fe,idx,act,fs,hend]
      simp only [boundaryResetConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl <;> simp only [eval_mul3,eval_c,hf] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

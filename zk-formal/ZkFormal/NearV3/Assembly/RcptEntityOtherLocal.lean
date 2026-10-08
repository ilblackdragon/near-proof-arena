import ZkFormal.NearV3.Assembly.RcptEntityBoundaryLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem entityInterior_local (tr : Trace Fp) (pos : Nat) (pub : List Fp) (a : EntityPlan)
    (ha : EntityCells tr pos a) (hb : EntityCells tr ((pos+1)%tr.height 0) a)
    (hf : EntityInsideFlags tr pos pub a) :
    ∀e∈listBoundaryConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [listBoundaryConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|he
  all_goals try (simp only [eval_mul3,eval_mul,eval_sub,eval_add,eval_c,eval_not,eval_n,eval_k,
    hf.boundary,hf.listEnd,hf.activeEnd,hf.header,hf.lastReceipt];grind only)
  · simp only [eval_mul,eval_sub,eval_add,eval_c,eval_n,hf.header,hf.lastReceipt]
    rw [ha.bodyEnd,hb.bodyStart]
    cases a with
    | header p =>
      change _ * (_ * ((Fp.ofNat p.bodyOffset)-(Fp.ofNat p.bodyOffset)))=0
      grind only
    | receipt p =>
      change _ * ((0+0: Fp) * _)=0
      grind only
  · obtain ⟨col,hcol,rfl⟩ := List.mem_map.mp he
    have hcols : col=j ∨ col=nj := by simpa only [lconsts,List.mem_cons,List.not_mem_nil,or_false] using hcol
    simp only [eval_mul3,eval_sub,eval_c,eval_n]
    rcases hcols with rfl|rfl
    · rw [ha.listIndex,hb.listIndex];grind only
    · rw [ha.listCount,hb.listCount];grind only

theorem entityTerminal_local (tr : Trace Fp) (pos : Nat) (pub : List Fp) (a : EntityPlan)
    (ha : EntityCells tr pos a) (hf : EntityEndFlags tr pos pub a)
    (hl : a.lastInList=true) (hll : a.lastList=true) (hcount : a.withinList=a.listCount)
    (hz : ∀col,tr.cell 0 ((pos+1)%tr.height 0) col=0) :
    ∀e∈listBoundaryConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [listBoundaryConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|he
  all_goals try (simp only [eval_mul3,eval_mul,eval_sub,eval_add,eval_c,eval_not,eval_n,eval_k,hz,
    hf.boundary,hf.listEnd,hf.activeEnd,hl,hll,Bool.true_and,bitCell,ite_true,
    ha.withinList,ha.listCount,hcount];grind only)
  obtain ⟨col,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_not,eval_c,hf.listEnd,hl,bitCell,ite_true]
  grind only

theorem entityPadding_local (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : ∀col,tr.cell 0 pos col=0) :
    ∀e∈listBoundaryConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [listBoundaryConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|he
  all_goals try (simp only [eval_mul3,eval_mul,eval_sub,eval_add,eval_c,eval_not,eval_n,eval_k,brkE,lhEnd,hz];grind only)
  obtain ⟨col,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_c,hz]
  grind only

theorem booleanReceiptTrace_padding (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hn : (plannedRows lists)[pos]?=none) :
    ∀col,(booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos col=0 := by
  intro col
  have hb := plannedTrace_padding lists log pos (booleanConstants constants)
    (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux fallback))
    (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
      (emissionHeaderFallback (booleanHeaderAux headerFallback))) (List.getElem?_eq_none_iff.mp hn) col
  unfold booleanReceiptTrace emittedReceiptTrace emissionPatch
  simp only [plannedState,hn,emissionValues,emits_zero_lookup]
  split
  · have hm : (col-31)%4=0 ∨ (col-31)%4=1 ∨ (col-31)%4=2 ∨ (col-31)%4=3 := by omega
    rcases hm with hm|hm|hm|hm <;> rw [hm] <;> rfl
  · exact hb

end ZkFormal.NearV3.Assembly.RcptSkeleton

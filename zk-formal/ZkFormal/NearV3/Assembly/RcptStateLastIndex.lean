import ZkFormal.NearV3.Assembly.RcptStateContinuation
import ZkFormal.NearV3.Assembly.RcptSkeletonLastIndex

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def lastIndexConstraints : List Expr := lastIdx.map (fun (s,e)=>mul3 (c fe) (c s) (sub (c idx) e))

set_option maxRecDepth 4096 in
theorem lastIdx_shape : ∀x∈lastIdx,x.1∈states ∧ shapeExpr x.2=true := by decide
set_option maxRecDepth 4096 in
theorem lastIndexConstraints_footprint : lastIndexConstraints.all currentExpr=true ∧
    lastIndexConstraints.all noEmissionExpr=true := by decide

theorem lastIndexConstraints_in_states : ∀e∈lastIndexConstraints,e∈cStates := by
  intro e he
  simp only [cStates,List.mem_append]
  simp_all [lastIndexConstraints]

theorem receipt_lastIndex (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hw : p.input.receipt.wf=true)
    (hl : row.length=fieldLen p.input row.state) (pub : List Fp) :
    ∀e∈lastIndexConstraints,e.eval (receiptPair constants aux p row row) 0 0 pub=0 := by
  intro e he
  obtain ⟨⟨s,x⟩,hm,rfl⟩ := List.mem_map.mp he
  obtain ⟨hs,hshape⟩ := lastIdx_shape (s,x) hm
  have hfe : (receiptPair constants aux p row row).cell 0 0 fe=controlCell row fe := receipt_control_cell constants aux p row (c:=fe) (by decide)
  have hidx : (receiptPair constants aux p row row).cell 0 0 idx=Fp.ofNat row.index := receipt_control_cell constants aux p row (c:=idx) (by decide)
  have hstate : (receiptPair constants aux p row row).cell 0 0 s=if s=row.state then 1 else 0 := by
    have hh := states_limits hs
    exact (receipt_control_cell _ _ _ _ (by simp [controlColumn];omega)).trans (control_state row hs)
  simp only [eval_mul3,eval_sub,eval_c,hfe,hidx,hstate]
  by_cases he : row.index+1=row.length
  · simp only [controlCell,fe,idx,act,fs,↓reduceIte,he]
    by_cases heq : s=row.state
    · rw [if_pos heq]
      have hev := shape_eval_agree (receiptPair constants aux p row row) 0 0 p.input pub
        (fun col hc=>receipt_shape_cell constants aux p row hc) x hshape
      rw [hev,field_last_index p.input hw pub hm,heq]
      have hi : fieldLen p.input row.state-1=row.index := by omega
      rw [hi]
      change (1:Fp)*1*((row.index:Fp)-(row.index:Fp))=0
      grind only
    · rw [if_neg heq];grind only
  · simp only [controlCell,fe,idx,act,fs,↓reduceIte,if_neg he]
    grind only

theorem header_lastIndex (aux : ListPlan→Coord→Nat→Fp) (p : ListPlan) (i : Nat) (pub : List Fp) :
    ∀e∈lastIndexConstraints,e.eval (⟨fun _=>1,fun _ _ col=>headerCell aux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0 := by
  intro e he
  obtain ⟨⟨s,x⟩,hm,rfl⟩ := List.mem_map.mp he
  obtain ⟨hs,_⟩ := lastIdx_shape (s,x) hm
  have hstate : headerCell aux p ⟨sCL,i,12⟩ s=if s=sCL then 1 else 0 := by
    have hh := states_limits hs
    exact (header_control_cell _ _ _ (by simp [controlColumn];omega)).trans (control_state _ hs)
  simp only [eval_mul3,eval_sub,eval_c]
  change headerCell aux p ⟨sCL,i,12⟩ fe * headerCell aux p ⟨sCL,i,12⟩ s * _=0
  rw [hstate]
  by_cases hsc : s=sCL
  · subst s
    have hx : x=k 11 := by
      simp only [lastIdx,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm
      simp_all [sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ]
    subst x
    simp only [ite_true,eval_k]
    have hf : headerCell aux p ⟨sCL,i,12⟩ fe=if i+1=12 then 1 else 0 := header_control_cell _ _ _ (by decide)
    have hi : headerCell aux p ⟨sCL,i,12⟩ idx=Fp.ofNat i := header_control_cell _ _ _ (by decide)
    rw [hf,hi]
    by_cases he : i+1=12
    · have hei : i=11 := by omega
      subst i
      simp only [↓reduceIte]
      change (1:Fp)*1*(11-11)=0
      grind only
    · rw [if_neg he];grind only
  · rw [if_neg hsc];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

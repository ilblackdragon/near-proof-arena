import ZkFormal.NearV3.Assembly.RcptDigestMetadata

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

set_option maxRecDepth 4096 in
theorem receipt_digestMetadata (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (pub : List Fp)
    (hg : aux p row gDg=bitCell (row.index==0 && (row.state==sXRI || row.state==sXLH)))
    (hi : aux p row dI=if row.state=sXRI then Fp.ofNat K_RID+16*Fp.ofNat p.receiptIndex
      else Fp.ofNat K_PEO+16*Fp.ofNat p.receiptIndex)
    (hl : aux p row dL=if row.state=sXRI then 48
      else 37+32*bitCell p.input.refund+Fp.ofNat p.input.receipt.receiverId.length) :
    ∀e∈digestMetadataConstraints,e.eval (receiptPair constants aux p row row) 0 0 pub=0 := by
  have heval : ∀v,(Expr.const v).eval (receiptPair constants aux p row row) 0 0 pub=Fp.ofNat v := fun _=>rfl
  have hcast : ∀v : Nat,(v : Fp)=Fp.ofNat v := fun _=>rfl
  have hs : (receiptPair constants aux p row row).cell 0 0 fs=if row.index=0 then 1 else 0 :=
    receipt_control_cell constants aux p row (c:=fs) (by decide)
  have hx : (receiptPair constants aux p row row).cell 0 0 sXRI=if sXRI=row.state then 1 else 0 :=
    (receipt_control_cell constants aux p row (c:=sXRI) (by decide)).trans (control_state row (by decide))
  have hp : (receiptPair constants aux p row row).cell 0 0 sXLH=if sXLH=row.state then 1 else 0 :=
    (receipt_control_cell constants aux p row (c:=sXLH) (by decide)).trans (control_state row (by decide))
  have hg' : (receiptPair constants aux p row row).cell 0 0 gDg=aux p row gDg := rfl
  have hi' : (receiptPair constants aux p row row).cell 0 0 dI=aux p row dI := rfl
  have hl' : (receiptPair constants aux p row row).cell 0 0 dL=aux p row dL := rfl
  have hr : (receiptPair constants aux p row row).cell 0 0 RcptV3.hr=bitCell p.input.refund := rfl
  have hv : (receiptPair constants aux p row row).cell 0 0 Lv=Fp.ofNat p.input.receipt.receiverId.length := rfl
  have hri : (receiptPair constants aux p row row).cell 0 0 r=Fp.ofNat p.receiptIndex := rfl
  have hne : ¬(row.state=sXRI ∧ row.state=sXLH) := by unfold sXRI sXLH;omega
  intro e he
  simp only [digestMetadataConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl <;>
    simp only [eval_sub,eval_mul,eval_mul3,eval_add,eval_c,eval_k,mid,smul,sum,heval,hcast,
      List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,hs,hx,hp,hg',hi',hl',hr,hv,hri,hg,hi,hl]
  all_goals by_cases hfirst : row.index=0 <;> by_cases hri : row.state=sXRI <;>
    by_cases hpeo : row.state=sXLH <;>
    simp only [bitCell,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,hfirst,hri,hpeo,
      show (sXRI=row.state)=(row.state=sXRI) from propext eq_comm,
      show (sXLH=row.state)=(row.state=sXLH) from propext eq_comm,↓reduceIte,
      true_and,false_and,and_true,and_false,true_or,false_or,or_true,or_false]
  all_goals try contradiction
  all_goals try simp only [show (sXLH=sXRI)=False from propext (by decide),show (sXRI=sXLH)=False from propext (by decide),↓reduceIte]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

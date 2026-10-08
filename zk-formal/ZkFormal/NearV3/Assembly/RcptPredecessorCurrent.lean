import ZkFormal.NearV3.Assembly.RcptPredecessorArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def predecessorCurrentConstraints : List Expr :=
  [mul3 (c sP) (c fs) (sub (c acc) (RcptV3.sq (sub (c b) (c (reg 0))))),
   mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (RcptV3.sq (sub (c Lp) (k 6))))),
   mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (Dsl.not (c sys))),
   .mul (mul3 (c sP) (c fe) (c sys)) (c p1),
   mul3 RcptV3.rowE (c sys) (sub (c Lp) (k 6))]

theorem predecessorCurrent_footprint : predecessorCurrentConstraints.all currentExpr=true ∧
    predecessorCurrentConstraints.all noEmissionExpr=true := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem receipt_predecessor_current (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hlen : row.length=fieldLen p.input row.state) :
    ∀e∈predecessorCurrentConstraints,e.eval
      (receiptPair (booleanConstants (nativePriceConstants ctx (systemConstants constants)))
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback))) p row row)
      0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants constants))
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback))
  let tr := receiptPair cn aux p row row
  have hs0 : tr.cell 0 0 sP=if sP=row.state then 1 else 0 :=
    (receipt_control_cell cn aux p row (show controlColumn sP=true by decide)).trans
      (control_state row (show sP∈states by decide))
  have hsys : tr.cell 0 0 sys=bitCell (p.input.receipt.predecessorId==AccountId.system) :=
    systemConstants_cell ctx constants p
  have hlp : tr.cell 0 0 Lp=Fp.ofNat p.input.receipt.predecessorId.length := rfl
  have hlast : (mul3 RcptV3.rowE (c sys) (sub (c Lp) (k 6))).eval tr 0 0 pub=0 := by
    simp only [eval_mul3,eval_sub,eval_c,eval_k,hsys,hlp]
    have hh := predecessor_system_length p.input.receipt
    grind only
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [predecessorCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|he|he|he|he
  all_goals subst e
  rotate_left 4
  · exact hlast
  all_goals by_cases hs : row.state=sP
  all_goals try (simp only [eval_mul3,eval_mul,eval_c,hs0,if_neg (Ne.symm hs)]; grind only; done)
  all_goals
    have hc := predecessorAux_cells ctx lists constants pub digests fallback p row hs
    have hb := predecessor_bytes cn pub digests
      (tokenAux (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback))) p row hs
    have hacc : tr.cell 0 0 acc=Fp.ofNat (accP (characterData p.input.receipt) row.index) := hc.1
    have hp1 : tr.cell 0 0 p1=Fp.ofNat (pP (characterData p.input.receipt)) := hc.2.1
    have his : tr.cell 0 0 isys=(Fp.ofNat (pP (characterData p.input.receipt)))⁻¹ := hc.2.2.1
    have hbyte : tr.cell 0 0 b=Fp.ofNat ((characterData p.input.receipt).pred.getD row.index 0) := hb.1
    have hreg : tr.cell 0 0 (reg 0)=Fp.ofNat (sysB row.index) := hb.2
    have hf : tr.cell 0 0 fs=bitCell (row.index==0) := by
      change (if row.index=0 then (1:Fp) else 0)=_
      simp only [bitCell,beq_iff_eq]
    have he : tr.cell 0 0 fe=bitCell (row.index+1==row.length) := by
      change (if row.index+1=row.length then (1:Fp) else 0)=_
      simp only [bitCell,beq_iff_eq]
    have hv : AccountId.valid p.input.receipt.predecessorId=true := by
      simp only [Receipt.wf,Bool.and_eq_true] at hw
      grind only
  · simp only [eval_mul3,eval_sub,eval_c,RcptV3.sq,eval_mul,hacc,hbyte,hreg,hf]
    by_cases hi : row.index=0
    · have hh := predecessor_score_start p.input.receipt
      rw [hi]
      grind only
    · simp only [bitCell,beq_eq_false_iff_ne.mpr hi,Bool.false_eq_true,ite_false]
      grind only
  · simp only [eval_mul3,eval_sub,eval_c,RcptV3.sq,eval_mul,eval_add,eval_k,hp1,hacc,hlp,he]
    by_cases hi : row.index+1=row.length
    · have hh := predecessor_score_end p.input.receipt row.index (by simpa [hlen,hs,fieldLen,sP,sCL,sPL] using hi)
      grind only
    · simp only [bitCell,beq_eq_false_iff_ne.mpr hi,Bool.false_eq_true,ite_false]
      grind only
  · simp only [eval_mul3,eval_sub,eval_c,eval_mul,eval_not,hp1,his,hsys]
    have hh := (character_pred_inverse p.input.receipt hv).1
    grind only
  · simp only [eval_mul3,eval_c,eval_mul,hp1,hsys]
    have hh := (character_pred_inverse p.input.receipt hv).2
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

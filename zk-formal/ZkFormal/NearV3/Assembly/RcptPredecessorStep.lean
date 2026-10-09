import ZkFormal.NearV3.Assembly.RcptPredecessorCurrentPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def predecessorStepConstraint : Expr :=
  mul3 (c sP) (Dsl.not (c fe))
    (sub (n acc) (.add (c acc) (RcptV3.sq (sub (n b) (n (reg 0))))))

theorem receipt_predecessor_step (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (hs : row.state=sP) :
    predecessorStepConstraint.eval
      (receiptPair (booleanConstants (nativePriceConstants ctx (systemConstants constants)))
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback)))
        p row (advance row)) 0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants constants))
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback))
  let tr := receiptPair cn aux p row (advance row)
  have hc := predecessorAux_cells ctx lists constants pub digests fallback p row hs
  have hn := predecessorAux_cells ctx lists constants pub digests fallback p (advance row) hs
  have hb := predecessor_bytes cn pub digests
      (tokenAux (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback))) p (advance row) hs
  have hacc : tr.cell 0 0 acc=Fp.ofNat (accP (characterData p.input.receipt) row.index) := hc.1
  have hnacc : tr.cell 0 1 acc=Fp.ofNat (accP (characterData p.input.receipt) (row.index+1)) := hn.1
  have hnbyte : tr.cell 0 1 b=Fp.ofNat ((characterData p.input.receipt).pred.getD (row.index+1) 0) := hb.1
  have hnreg : tr.cell 0 1 (reg 0)=Fp.ofNat (sysB (row.index+1)) := hb.2
  have hnext : 1%tr.height 0=1 := by rfl
  change predecessorStepConstraint.eval tr 0 0 pub=0
  simp only [predecessorStepConstraint,eval_mul3,eval_sub,eval_n,eval_c,eval_add,RcptV3.sq,eval_mul,
    Nat.zero_add,hnext,hnacc,hacc,hnbyte,hnreg]
  have hh := predecessor_score_step p.input.receipt row.index
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

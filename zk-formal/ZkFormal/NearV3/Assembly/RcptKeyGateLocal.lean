import ZkFormal.NearV3.Assembly.RcptKeyFinalArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyGateConstraints : List Expr :=
  [sub (c gKA) (sum [c sV,c kz,.mul (c sRID) (c fs),
    .mul (c ee) (sum [c sT0,.mul (c sSL) (c fs),c sS,c sKT,c sPK,.mul (c sGP) (c fs)])]),
   sub (c gKB) (.add (c sV) (.mul (c ee) (sum [c sT0,.mul (c sSL) (c fs),c sS,c sKT,c sPK]))),
   sub (c gF) (.add (c rf) (.mul (c ee) (c sT0))),
   .mul (c rf) (c fkF),.mul (c rf) (sub (c kF) (c kslot)),
   sub (c gAK) (mul3 (c ee) (c sT0) (Dsl.not (c fkF)))]

theorem keyGate_footprint : keyGateConstraints.all currentExpr=true ∧ keyGateConstraints.all noEmissionExpr=true := by decide

theorem keyGate_in_key : ∀e∈keyGateConstraints,e∈cKey := by
  intro e he
  simp only [keyGateConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cKey,List.mem_cons,List.not_mem_nil,or_false]
  grind only

set_option maxRecDepth 4096 in
theorem receipt_key_gates (ctx : ApplyCtx) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) :
    ∀e∈keyGateConstraints,e.eval (receiptPair
      (booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants)))))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (keyAux accountId accessId fallback))) p row row) 0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants))))
  let aux := tokenReceiptAux pub digests tokens (booleanReceiptAux (keyAux accountId accessId fallback))
  let tr := receiptPair cn aux p row row
  have hfields := keyAux_transport accountId accessId
    (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId constants))))
    pub digests tokens fallback p row
  have hKA : tr.cell 0 0 gKA=bitCell (keyGateA p row) := hfields gKA (by decide)
  have hKB : tr.cell 0 0 gKB=bitCell (keyGateB p row) := hfields gKB (by decide)
  have hZ : tr.cell 0 0 kz=bitCell (keyZero row) := hfields kz (by decide)
  have hF : tr.cell 0 0 gF=bitCell ((row.state==sPL && row.index==0) || (systemEqual p.input.receipt && row.state==sT0)) := hfields gF (by decide)
  have hA : tr.cell 0 0 gAK=bitCell (systemEqual p.input.receipt && row.state==sT0 && !(accessId p).isNone) := hfields gAK (by decide)
  have hfF : tr.cell 0 0 fkF=bitCell (row.state==sT0 && (accessId p).isNone) := hfields fkF (by decide)
  have hkF : tr.cell 0 0 kF=Fp.ofNat (if row.state=sT0 then (accessId p).getD 0 else accountId p) := hfields kF (by decide)
  have hslot : tr.cell 0 0 kslot=Fp.ofNat (accountId p) := by
    change boolInput kslot (Fp.ofNat (accountId p))=Fp.ofNat (accountId p)
    exact if_neg (by decide)
  have hee : tr.cell 0 0 ee=bitCell (systemEqual p.input.receipt) :=
    (systemIdentity_cells ctx (keyConstants accountId constants) p).1
  have hrf : tr.cell 0 0 rf=bitCell (row.state==sPL && row.index==0) := rfl
  have hfs : tr.cell 0 0 fs=keyFirst row := by
    change (if row.index=0 then (1:Fp) else 0)=bitCell (row.index==0)
    simp only [bitCell,beq_iff_eq]
  have hst (s : Nat) (hsc : controlColumn s=true) (hss : s∈states) : tr.cell 0 0 s=keyState row s := by
    have hh := (receipt_control_cell cn aux p row hsc).trans (control_state row hss)
    apply hh.trans
    by_cases hs : s=row.state
    · simp only [keyState,bitCell,hs,beq_self_eq_true,ite_true]
    · simp only [keyState,bitCell,if_neg hs,beq_eq_false_iff_ne.mpr (Ne.symm hs),Bool.false_eq_true,ite_false]
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [keyGateConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [eval_sub,eval_add,eval_mul,eval_mul3,eval_not,eval_sum_cons,eval_sum_nil,eval_c,
    hKA,hKB,hZ,hF,hA,hfF,hkF,hslot,hee,hrf,hfs,
    hst sV (by decide) (by decide),hst sRID (by decide) (by decide),hst sT0 (by decide) (by decide),
    hst sSL (by decide) (by decide),hst sS (by decide) (by decide),hst sKT (by decide) (by decide),
    hst sPK (by decide) (by decide),hst sGP (by decide) (by decide)]
  · have hh := keyGateA_arithmetic p row
    grind only
  · have hh := keyGateB_arithmetic p row
    grind only
  · rw [keyFinal_gate]
    grind only
  · exact keyFinal_first_absent accessId p row
  · exact keyFinal_first_value accountId accessId p row
  · have hh := keyAccess_gate (systemEqual p.input.receipt) (row.state==sT0) (accessId p).isNone
    change _=0
    unfold keyState
    rw [hh]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

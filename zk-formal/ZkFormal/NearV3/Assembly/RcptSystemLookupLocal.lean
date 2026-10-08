import ZkFormal.NearV3.Assembly.RcptSystemIdentityLocal
import ZkFormal.NearV3.Assembly.RcptSystemLookupArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def systemLookupCurrentConstraints : List Expr :=
  [.mul (c gV) (Dsl.not (c sV)),mul3 (c ee) (c sV) (Dsl.not (c gV)),
   .mul (c gS) (Dsl.not (c sS)),mul3 (c ee) (c sS) (Dsl.not (c gS)),
   mul3 (c ee) (c sS) (sub (c sx) (c b)),
   .mul (.mul (c dd) (c gS)) (sub (.mul (sub (c b) (c sx)) (c invD)) (k 1)),
   mul3 (c sS) (c fs) (sub (c scnt) (c gS)),
   .mul (mul3 (c sS) (c fe) (c dd)) (Dsl.not (c scnt))]

theorem systemLookupCurrent_footprint : systemLookupCurrentConstraints.all currentExpr=true ∧
    systemLookupCurrentConstraints.all noEmissionExpr=true := by decide

theorem system_bit_nat (b : Bool) : Fp.ofNat (if b then 1 else 0)=bitCell b := by
  cases b <;> rfl

theorem receipt_signer_byte (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hs : row.state=sS) :
    receiptCell constants (streamAux pub digests fallback) p row b=
      Fp.ofNat ((p.input.receipt.signerId.getD row.index 0).toNat) := by
  rw [receipt_stream_byte]
  rw [hs,if_neg (show sS∉regStates by decide)]
  simp only [nativeFieldByte,hs,
    sS,sP,sV,sRID,Nat.reduceEqDiff,↓reduceIte]

theorem system_inverse_cast (a b : Fp) (h : a*(b-1)=0) : a*(b-(1:Nat))=0 := by grind only

set_option maxRecDepth 4096 in
theorem receipt_system_lookup (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hlen : row.length=fieldLen p.input row.state) :
    ∀e∈systemLookupCurrentConstraints,e.eval
      (receiptPair (booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))))
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))) p row row)
      0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))
  let tr := receiptPair cn aux p row row
  have hc := systemIdentity_cells ctx constants p
  have hee : tr.cell 0 0 ee=bitCell (systemEqual p.input.receipt) := hc.1
  have hdd : tr.cell 0 0 dd=bitCell (systemMismatch p.input.receipt) := hc.2.2.1
  have hfields := systemAux_transport ctx lists
    (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))) pub digests fallback p row
  have hgv : tr.cell 0 0 gV=bitCell (row.state==sV && systemLookup p.input.receipt row.index) := hfields gV (by decide)
  have hgs : tr.cell 0 0 gS=bitCell (row.state==sS && systemLookup p.input.receipt row.index) := hfields gS (by decide)
  have hsx : tr.cell 0 0 sx=Fp.ofNat ((p.input.receipt.receiverId.getD row.index 0).toNat) := hfields sx (by decide)
  have hcnt : tr.cell 0 0 scnt=Fp.ofNat (systemLookupCount p.input.receipt row.index) := hfields scnt (by decide)
  have hinv : tr.cell 0 0 invD=(Fp.ofNat ((p.input.receipt.signerId.getD row.index 0).toNat)-
      Fp.ofNat ((p.input.receipt.receiverId.getD row.index 0).toNat))⁻¹ :=
    (hfields invD (by decide)).trans (systemAux_invD fallback p row)
  have hst (s : Nat) (hsc : controlColumn s=true) (hss : s∈states) :
      tr.cell 0 0 s=bitCell (row.state==s) := by
    have hh := (receipt_control_cell cn aux p row hsc).trans (control_state row hss)
    apply hh.trans
    by_cases he : s=row.state
    · simp only [he,ite_true,beq_self_eq_true,bitCell]
    · have hn : row.state≠s := Ne.symm he
      simp only [if_neg he,bitCell,beq_eq_false_iff_ne.mpr hn,Bool.false_eq_true,ite_false]
  have hsv := hst sV (by decide) (by decide)
  have hss := hst sS (by decide) (by decide)
  have hgfV := systemLookup_gates p.input.receipt row.index (row.state==sV)
  have hgfS := systemLookup_gates p.input.receipt row.index (row.state==sS)
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [systemLookupCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [eval_mul,eval_not,eval_c,hgv,hsv] using hgfV.1
  · simpa only [eval_mul3,eval_not,eval_c,hee,hgv,hsv] using hgfV.2
  · simpa only [eval_mul,eval_not,eval_c,hgs,hss] using hgfS.1
  · simpa only [eval_mul3,eval_not,eval_c,hee,hgs,hss] using hgfS.2
  all_goals by_cases hs : row.state=sS
  all_goals try (simp only [eval_mul3,eval_mul,eval_c,hss,hgs,beq_eq_false_iff_ne.mpr hs,
    Bool.false_and,bitCell,Bool.false_eq_true,ite_false];grind only;done)
  all_goals
    have hb : tr.cell 0 0 b=Fp.ofNat ((p.input.receipt.signerId.getD row.index 0).toNat) :=
      receipt_signer_byte cn pub digests (tokenAux (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))) p row hs
  · simp only [eval_mul3,eval_sub,eval_c,hee,hss,hsx,hb,hs,beq_self_eq_true,bitCell,ite_true]
    have hh := systemLookup_equal_byte p.input.receipt row.index
    simp only [bitCell] at hh
    grind only
  · simp only [eval_mul,eval_sub,eval_c,eval_k,hdd,hgs,hsx,hb,hinv,hs,beq_self_eq_true,Bool.true_and]
    have hh := systemLookup_difference p.input.receipt row.index
    exact system_inverse_cast _ _ hh
  · simp only [eval_mul3,eval_sub,eval_c,hss,hcnt,hgs,hs,beq_self_eq_true,Bool.true_and]
    by_cases hi : row.index=0
    · have hfs : tr.cell 0 0 fs=1 := by change (if row.index=0 then (1:Fp) else 0)=1;rw [if_pos hi]
      rw [hfs,hi,systemLookupCount_start,system_bit_nat]
      grind only
    · have hfs : tr.cell 0 0 fs=0 := by change (if row.index=0 then (1:Fp) else 0)=0;rw [if_neg hi]
      rw [hfs]
      grind only
  · simp only [eval_mul3,eval_mul,eval_not,eval_c,hss,hdd,hcnt,hs,beq_self_eq_true]
    by_cases he : row.index+1=row.length
    · by_cases hm : systemMismatch p.input.receipt=true
      · have hi : row.index+1=p.input.receipt.signerId.length := by
          simpa [hlen,hs,fieldLen,sS,sP,sV,sCL,sPL,sVL,sRID,sT0,sSL] using he
        rw [systemLookupCount_end p.input.receipt hm row.index hi]
        change _*(1-(1:Fp))=0
        grind only
      · simp only [bitCell,if_neg hm]
        grind only
    · have hfe : tr.cell 0 0 fe=0 := by change (if row.index+1=row.length then (1:Fp) else 0)=0;rw [if_neg he]
      rw [hfe]
      grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

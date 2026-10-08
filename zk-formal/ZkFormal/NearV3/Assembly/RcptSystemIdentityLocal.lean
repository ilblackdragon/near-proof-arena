import ZkFormal.NearV3.Assembly.RcptSystemArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def systemIdentityConstraints : List Expr :=
  [mul3 rowE (c ee) (Dsl.not (c sys)),mul3 rowE (c sys) (c hr),
   mul3 rowE (c ee) (sub (c Ls) (c Lv)),
   .mul rowE (sub (c dd) (mul3 (c sys) (Dsl.not (c ee)) (c dm))),
   .mul (c rf) (.mul dzE (sub (.mul (sub (c Ls) (c Lv)) (c invL)) (k 1)))]

theorem systemIdentityConstraints_footprint : systemIdentityConstraints.all currentExpr=true ∧
    systemIdentityConstraints.all noEmissionExpr=true := by decide

theorem systemIdentityConstraints_eq : systemIdentityConstraints=cSys.take 5 := rfl

theorem system_identity_inv_gate (a b c : Fp) (h : b*(c-1)=0) : a*(b*(c-(1:Nat)))=0 := by grind only

theorem system_mul_zero (a b c : Fp) (h : b*c=0) : a*b*c=0 := by grind only

set_option maxRecDepth 4096 in
theorem receipt_system_identity (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hrf : p.input.refund=nativeRefund ctx p.input.receipt) :
    ∀e∈systemIdentityConstraints,e.eval
      (receiptPair (booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))))
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))) p row row)
      0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))
  let tr := receiptPair cn aux p row row
  have hc := systemIdentity_cells ctx constants p
  have hee : tr.cell 0 0 ee=bitCell (systemEqual p.input.receipt) := hc.1
  have hdm : tr.cell 0 0 dm=bitCell (systemEqualLength p.input.receipt) := hc.2.1
  have hdd : tr.cell 0 0 dd=bitCell (systemMismatch p.input.receipt) := hc.2.2.1
  have hsys : tr.cell 0 0 sys=bitCell (p.input.receipt.predecessorId==AccountId.system) := hc.2.2.2
  have hls : tr.cell 0 0 Ls=Fp.ofNat p.input.receipt.signerId.length := rfl
  have hlv : tr.cell 0 0 Lv=Fp.ofNat p.input.receipt.receiverId.length := rfl
  have hhr : tr.cell 0 0 hr=bitCell (nativeRefund ctx p.input.receipt) := by
    change bitCell p.input.refund=_
    rw [hrf]
  have hinv : tr.cell 0 0 invL=(Fp.ofNat p.input.receipt.signerId.length-Fp.ofNat p.input.receipt.receiverId.length)⁻¹ :=
    (systemAux_transport ctx lists (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
      pub digests fallback p row invL (by decide)).trans (systemAux_invL fallback p row)
  have har := system_identity_arithmetic p.input.receipt
  have hrefund := system_no_refund ctx p.input.receipt
  have hlen := system_length_inverse p.input.receipt hw
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [systemIdentityConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl <;>
    simp only [eval_mul3,eval_sub,eval_mul,eval_c,eval_not,eval_k,dzE,hee,hdm,hdd,hsys,hls,hlv,hhr,hinv]
  · exact system_mul_zero _ _ _ har.1
  · exact system_mul_zero _ _ _ hrefund
  · exact system_mul_zero _ _ _ har.2.1
  · rw [har.2.2]
    grind only
  · exact system_identity_inv_gate _ _ _ hlen

theorem systemIdentity_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : rowE.eval tr 0 pos pub=0) (hf : tr.cell 0 pos rf=0) :
    ∀e∈systemIdentityConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [systemIdentityConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl <;> simp only [eval_mul3,eval_mul,eval_c,hz,hf] <;> grind only

theorem booleanReceiptTrace_systemIdentity (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈systemIdentityConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
        pub digests (systemAux fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp systemIdentityConstraints_footprint.2 e he)]
  apply plannedTrace_current_input_family lists hw log pos _ _ _ pub systemIdentityConstraints
    systemIdentityConstraints_footprint.1 ?_ ?_ ?_ e he
  · intro p row hm hw _
    obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hm
    exact receipt_system_identity ctx lists constants pub digests fallback p row hw (hflags xs hxs p.input hx)
  · intro p i
    apply systemIdentity_zero _ _ _ ?_ (by rfl)
    simp only [rowE,eval_sub,eval_c]
    change (1:Fp)-1=0
    grind only
  · apply systemIdentity_zero _ _ _ ?_ (by rfl)
    simp only [rowE,eval_sub,eval_c,zeroCurrentTrace]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

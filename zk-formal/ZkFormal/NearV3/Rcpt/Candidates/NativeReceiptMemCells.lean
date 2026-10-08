import ZkFormal.NearV3.Assembly.RcptNativeFieldBytes
import ZkFormal.NearV3.Assembly.RcptDepositGlobalCommute
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.Near.Render RcptGen RcptP RoutingBoundedLayout

/-- Native DEP fields occupy their concrete offset in each full receipt. -/
theorem receipt_deposit_position (p : ReceiptPlan) (i : Nat) (hi:i<16) :
    (plannedReceiptRows p)[107+Vt p.input.receipt.predecessorId.length p.input.receipt.receiverId.length
      p.input.receipt.signerId.length p.input.receipt.signerPk.tag+i]?=some (.receipt p ⟨sDEP,i,16⟩) := by
  have hh:=field_lookup p.input (fields p.input.refund) 12 sDEP i
    (by cases p.input.refund <;> rfl) (by change i<16;exact hi)
  have hp:(((fields p.input.refund).take 12).flatMap (fun s=>segment s (fieldLen p.input s))).length=
      107+Vt p.input.receipt.predecessorId.length p.input.receipt.receiverId.length
        p.input.receipt.signerId.length p.input.receipt.signerPk.tag:=by
    cases p.input.refund <;> simp [fields,fieldLen,segment_length,Vt,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP] <;> omega
  rw [hp] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [hh]
  rfl

private theorem depositFinal_mem_cells (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) :
    let cell:=receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositFinalAux previous accounts fallback))) p ⟨sDEP,i,16⟩
    cell bef=Fp.ofNat (Seg.befB (nativeDepositData (accounts p) p.input.receipt) i) ∧
    cell lk=Fp.ofNat (Seg.lkB (nativeDepositData (accounts p) p.input.receipt) i) ∧
    cell st=Fp.ofNat (Seg.stB (nativeDepositData (accounts p) p.input.receipt) i) := by
  refine ⟨?_,?_,?_⟩
  · change depositAgeAux previous (depositAux accounts fallback) p ⟨sDEP,i,16⟩ bef=_
    simp [depositAgeAux,depositAux,st,r1,xb,sDEP,bef,lk]
  · change depositAgeAux previous (depositAux accounts fallback) p ⟨sDEP,i,16⟩ lk=_
    simp [depositAgeAux,depositAux,st,r1,xb,sDEP,bef,lk]
  · change depositAgeAux previous (depositAux accounts fallback) p ⟨sDEP,i,16⟩ st=_
    simp [depositAgeAux,depositAux,st,r1,xb,sDEP,bef,lk]

private theorem depositFinal_mem_bit (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i j : Nat) (hj:j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositFinalAux previous accounts fallback)))
      p ⟨sDEP,i,16⟩ (xb j)=frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) j := by
  have he:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7:=by omega
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change boolInput (xb 0) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 0)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 0 (by decide)
  · change boolInput (xb 1) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 1)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 1 (by decide)
  · change boolInput (xb 2) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 2)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 2 (by decide)
  · change boolInput (xb 3) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 3)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 3 (by decide)
  · change boolInput (xb 4) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 4)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 4 (by decide)
  · change boolInput (xb 5) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 5)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 5 (by decide)
  · change boolInput (xb 6) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 6)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 6 (by decide)
  · change boolInput (xb 7) (depositFinalAux previous accounts fallback p ⟨sDEP,i,16⟩ (xb 7)) = _
    simp only [depositFinalAux,depositAgeAux,xb,r1,sDEP,Nat.reduceAdd,Nat.reduceEqDiff,Nat.reduceLeDiff,
      Nat.reduceLT,false_and,and_false,ite_false]
    exact deposit_after_bit accounts constants pub digests tokens fallback p i 16 7 (by decide)

variable (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log pos i : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (ha:(plannedRows lists)[pos]?=some (.receipt p ⟨sDEP,i,16⟩))

include ha in
theorem native_deposit_mem_cells :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback) 0
    tr.cell 0 pos bef=Fp.ofNat (Seg.befB (nativeDepositData (accounts p) p.input.receipt) i) ∧
    tr.cell 0 pos lk=Fp.ofNat (Seg.lkB (nativeDepositData (accounts p) p.input.receipt) i) ∧
    tr.cell 0 pos st=Fp.ofNat (Seg.stB (nativeDepositData (accounts p) p.input.receipt) i) := by
  simp only [←depositFinal_complete_aux]
  have hb:=booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (depositFinalAux previous accounts (completeReceiptAux ctx k lists accountId accessId fallback)) headerFallback _ ha
  rw [RoutingQCandidate.patch_other _ _ _ bef (by decide),RoutingQCandidate.patch_other _ _ _ lk (by decide),
    RoutingQCandidate.patch_other _ _ _ st (by decide),hb bef (by decide),hb lk (by decide),hb st (by decide)]
  exact depositFinal_mem_cells previous accounts constants pub digests (receiptPlanToken ctx lists)
    (completeReceiptAux ctx k lists accountId accessId fallback) p i

include ha in
theorem native_deposit_mem_bit (j : Nat) (hj:j<8) :
    (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback) 0).cell 0 pos (xb j)=
      frameBit (Seg.aftB (nativeDepositData (accounts p) p.input.receipt) i) j := by
  simp only [←depositFinal_complete_aux]
  have hb:=booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (depositFinalAux previous accounts (completeReceiptAux ctx k lists accountId accessId fallback)) headerFallback _ ha
  have hcol:¬(xb 12≤xb j ∧ xb j≤xb 18):=by simp only [xb];omega
  rw [RoutingQCandidate.patch_other _ _ _ (xb j) hcol,hb (xb j) (by change decide (31≤138+j ∧ 138+j≤42)=false;simp;omega)]
  exact depositFinal_mem_bit previous accounts constants pub digests (receiptPlanToken ctx lists)
    (completeReceiptAux ctx k lists accountId accessId fallback) p i j hj

end ZkFormal.NearV3.Assembly.RcptSkeleton

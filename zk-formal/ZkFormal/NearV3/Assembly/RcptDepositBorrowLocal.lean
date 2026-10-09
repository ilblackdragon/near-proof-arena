import ZkFormal.NearV3.Assembly.RcptDepositBorrowFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def depositBorrowConstraints : List Expr := (cDep.drop 16).take 4

theorem deposit_big_cell (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) :
    receiptCell (booleanConstants (depositConstants accounts constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p row big=
      bitCell (nativeDepositData (accounts p) p.input.receipt).big := by
  change boolInput big (bitCell _)=_
  exact boolInput_preserves _ _ (bitCell_boolean _)

theorem receipt_deposit_borrow_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositBorrowConstraints,e.eval
      (receiptPair (booleanConstants (depositConstants accounts constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback)))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  let d := nativeDepositData (accounts p) p.input.receipt
  let cn := depositConstants accounts constants
  let tr := receiptPair (booleanConstants cn)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,16⟩ next
  have hg : tr.cell 0 0 sDEP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hc : tr.cell 0 0 c4=Fp.ofNat (Seg.dbr d i) :=
    (deposit_base_cells accounts cn pub digests tokens fallback p i 16).2.2.2.2.2.2.1
  have hb : tr.cell 0 0 (xb 46)=Fp.ofNat (Seg.dbr d (i+1)) :=
    deposit_borrow_bit accounts cn pub digests tokens fallback p i 16 h
  have ht : (bitsX 9 8).eval tr 0 0 pub=Fp.ofNat (Seg.totB d i) :=
    deposit_total_eval accounts cn pub digests tokens fallback p i 16 next
  have hq : (bitsX 18 8).eval tr 0 0 pub=Fp.ofNat (Seg.qB d i) :=
    deposit_storage_q_eval accounts cn pub digests tokens fallback p i 16 next h
  have hd : (bitsX 38 8).eval tr 0 0 pub=Fp.ofNat (Seg.ddv d i) :=
    deposit_difference_eval accounts cn pub digests tokens fallback p i 16 next h
  have hbig : tr.cell 0 0 big=bitCell d.big :=
    deposit_big_cell accounts constants pub digests tokens fallback p ⟨sDEP,i,16⟩
  have hnext (hn' : i+1<16) : tr.cell 0 ((0+1)%tr.height 0) c4=Fp.ofNat (Seg.dbr d (i+1)) := by
    change receiptCell (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p next c4=_
    rw [hn hn']
    exact (deposit_base_cells accounts cn pub digests tokens fallback p (i+1) 16).2.2.2.2.2.2.1
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  · have he := congrArg Fp.ofNat (deposit_ddv_step h i)
    simp only [ofNat_add_e,ofNat_mul_e] at he
    simp only [dp,eval_mul,eval_sub,eval_add,eval_smul,eval_c,hg,hc,ht,hq,hd,hb,natCast_eq]
    grind only
  · simp only [dp,eval_mul,eval_c,hg,hfs,hc]
    by_cases hz : i=0
    · subst i;change (1:Fp)*1*0=0;grind only
    · rw [if_neg hz];grind only
  · simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hb]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega)];grind only
  · simp only [dp,eval_mul3,eval_mul,eval_c,hg,hfe,hb,hbig]
    by_cases he : i+1=16
    · rw [if_pos he,he]
      cases hbig : d.big with
      | false =>simp only [bitCell,Bool.false_eq_true,ite_false];grind only
      | true =>rw [deposit_dbr_final h hbig];change (1:Fp)*1*1*0=0;grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

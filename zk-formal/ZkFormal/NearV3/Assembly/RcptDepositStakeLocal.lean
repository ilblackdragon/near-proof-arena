import ZkFormal.NearV3.Assembly.RcptDepositStakeFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def depositStakeConstraints : List Expr := (cDep.drop 20).take 5

theorem receipt_deposit_stake_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositStakeConstraints,e.eval
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
  have hr : tr.cell 0 0 r1=if i=1 then 1 else 0 := by
    rw [show tr.cell 0 0 r1=bitCell (i==1) from deposit_r1_cell accounts cn pub digests tokens fallback p i 16]
    simp only [bitCell,beq_iff_eq]
  have hst : tr.cell 0 0 st=Fp.ofNat (Seg.stB d i) :=
    (deposit_base_cells accounts cn pub digests tokens fallback p i 16).2.2.1
  have hbig : tr.cell 0 0 big=bitCell d.big :=
    deposit_big_cell accounts constants pub digests tokens fallback p ⟨sDEP,i,16⟩
  have hnext (hn' : i+1<16) : tr.cell 0 ((0+1)%tr.height 0) r1=if i=0 then 1 else 0 := by
    change receiptCell (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p next r1=_
    rw [hn hn',deposit_r1_cell]
    simp only [bitCell,beq_iff_eq,show i+1=1 ↔ i=0 from by omega]
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl
  · simp only [dp,eval_mul,eval_not,eval_c,hg];grind only
  · simp only [dp,eval_mul3,eval_c,hg,hfs,hr]
    by_cases hz : i=0
    · subst i;simp only [ite_true,show ¬(0:Nat)=1 from by decide,ite_false];grind only
    · rw [if_neg hz];grind only
  · simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hfs]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega)];grind only
  · simp only [eval_mul3,eval_not,eval_sub,eval_c,eval_k,hbig,hr]
    by_cases hi1 : i=1
    · subst i
      rw [if_pos rfl]
      cases hb : d.big with
      | true =>simp only [bitCell,ite_true];grind only
      | false =>
        have hd : tr.cell 0 0 (dl 0)=Fp.ofNat (Seg.stB d 0) := by
          exact deposit_storage_dl_cell accounts cn pub digests tokens fallback p 1 16 0 (by decide)
        have hgap : (bitsX 47 10).eval tr 0 0 pub=Fp.ofNat (770-d.stor) :=
          deposit_storage_gap_eval accounts cn pub digests tokens fallback p next hb
        simp only [bitCell,Bool.false_eq_true,ite_false,eval_sum_cons,eval_sum_nil,eval_smul,eval_c,hd,hst,hgap,natCast_eq]
        have he := congrArg Fp.ofNat (deposit_stor_small h hb)
        have hs := h.stake hb
        have hsum := congrArg Fp.ofNat (Nat.sub_add_cancel hs)
        simp only [ofNat_add_e,ofNat_mul_e] at he hsum
        grind only
    · rw [if_neg hi1];grind only
  · simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,hbig,hg,hfs,hr,hst]
    cases hb : d.big with
    | true =>simp only [bitCell,ite_true];grind only
    | false =>
      by_cases hi0 : i=0
      · subst i;simp only [ite_true,show ¬(0:Nat)=1 from by decide,ite_false,bitCell,Bool.false_eq_true];grind only
      · by_cases hi1 : i=1
        · subst i;simp only [ite_true,show ¬(1:Nat)=0 from by decide,ite_false,bitCell,Bool.false_eq_true];grind only
        · rw [show Seg.stB d i=0 from deposit_stB_small h hb (by omega)]
          change _ * _ * (0:Fp)=0
          grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

import ZkFormal.NearV3.Assembly.RcptDepositAddition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout
open ZkFormal.Near.Render RcptGen RcptP

def depositNonmaxConstraints : List Expr := (cDep.drop 4).take 3

theorem depositInverse_correct {d : RD} (h : DepositArithmeticOk d) :
    Fp.ofNat (Seg.runA d 15)*depositInverse d=1 := by
  have hn := deposit_runA_ne h
  have hb := deposit_runA_lt h 15 (by decide)
  have hz : Fp.ofNat (Seg.runA d 15)≠0 := by
    intro hz
    have he := congrArg Fp.toNat hz
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at he
    exact hn he
  exact Fp.mul_inv_cancel hz

theorem receipt_deposit_nonmax_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositNonmaxConstraints,e.eval
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback)))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  let d := nativeDepositData (accounts p) p.input.receipt
  let tr := receiptPair (booleanConstants constants)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,16⟩ next
  have hg : tr.cell 0 0 sDEP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hd : tr.cell 0 0 dsum=Fp.ofNat (Seg.runA d i) := rfl
  have hinv : tr.cell 0 0 invB=depositInverse d := deposit_inverse_cell accounts constants pub digests tokens fallback p i 16
  have ha : aftE.eval tr 0 0 pub=Fp.ofNat (Seg.aftB d i) :=
    deposit_after_eval accounts constants pub digests tokens fallback p i 16 next
  have hdn (hn' : i+1<16) : tr.cell 0 ((0+1)%tr.height 0) dsum=Fp.ofNat (Seg.runA d (i+1)) := by
    change receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p next dsum=_
    rw [hn hn'];rfl
  have han (hn' : i+1<16) : (bitsXn 0 8).eval tr 0 0 pub=Fp.ofNat (Seg.aftB d (i+1)) := by
    change (bitsX 0 8).eval tr 0 ((0+1)%tr.height 0) pub=_
    rw [eval_frame_bits tr 0 ((0+1)%tr.height 0) pub 0 (Seg.aftB d (i+1)) 8 ?_]
    · exact congrArg Fp.ofNat (Nat.mod_eq_of_lt (leBytes_getD_lt 16 _ (i+1)))
    · intro j hj
      change receiptCell (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p next (xb (0+j))=_
      rw [hn hn',Nat.zero_add]
      exact deposit_after_bit accounts constants pub digests tokens fallback p (i+1) 16 j hj
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl
  · simp only [dp,eval_mul3,eval_sub,eval_c,eval_k,hg,hfs,hd,ha]
    by_cases hz : i=0
    · subst i
      rw [show Seg.runA d 0=255-Seg.aftB d 0 from deposit_runA_zero h]
      simp only [ite_true,ofNat_sub (show Seg.aftB d 0≤255 from Nat.le_of_lt_succ (leBytes_getD_lt _ _ _)),natCast_eq]
      grind only
    · rw [if_neg hz];grind only
  · simp only [dp,eval_mul3,eval_not,eval_sub,eval_add,eval_c,eval_n,eval_k,hg,hfe,hd]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hdn (by omega),han (by omega)]
      rw [show Seg.runA d (i+1)=Seg.runA d i+(255-Seg.aftB d (i+1)) from deposit_runA_succ h i]
      simp only [ofNat_add_e,ofNat_sub (show Seg.aftB d (i+1)≤255 from Nat.le_of_lt_succ (leBytes_getD_lt _ _ _)),natCast_eq]
      grind only
  · simp only [dp,eval_mul3,eval_mul,eval_sub,eval_c,eval_k,hg,hfe,hd,hinv]
    by_cases he : i+1=16
    · have hi15 : i=15 := by omega
      subst i
      rw [if_pos (by decide),depositInverse_correct h]
      grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

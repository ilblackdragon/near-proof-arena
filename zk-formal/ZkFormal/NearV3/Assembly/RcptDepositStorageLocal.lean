import ZkFormal.NearV3.Assembly.RcptDepositStorageFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def depositStorageProductConstraints : List Expr := (cDep.drop 11).take 4

theorem byteDelay_offset (v : Nat→Nat) (j i : Nat) :
    byteDelay v j i=if j+1≤i then v (i-(j+1)) else 0 := by
  unfold byteDelay
  have hh : j<i ↔ j+1≤i := by omega
  simp only [hh]
  split
  · congr 1;omega
  · rfl

theorem receipt_deposit_storage_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositStorageProductConstraints,e.eval
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback)))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  let d := nativeDepositData (accounts p) p.input.receipt
  let tr := receiptPair (booleanConstants constants)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,16⟩ next
  have hg : tr.cell 0 0 sDEP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hc : tr.cell 0 0 c3=Fp.ofNat (chain (Seg.y3 d) i) :=
    (deposit_base_cells accounts constants pub digests tokens fallback p i 16).2.2.2.2.2.1
  have hst : tr.cell 0 0 st=Fp.ofNat (Seg.stB d i) :=
    (deposit_base_cells accounts constants pub digests tokens fallback p i 16).2.2.1
  have hq : (bitsX 18 8).eval tr 0 0 pub=Fp.ofNat (Seg.qB d i) :=
    deposit_storage_q_eval accounts constants pub digests tokens fallback p i 16 next h
  have hcarry : (bitsX 26 12).eval tr 0 0 pub=Fp.ofNat (chain (Seg.y3 d) (i+1)) :=
    deposit_storage_carry_eval accounts constants pub digests tokens fallback p i 16 next h
  have hd (j : Nat) (hj : j<7) : tr.cell 0 0 (dl j)=Fp.ofNat (byteDelay (Seg.stB d) j i) :=
    deposit_storage_dl_cell accounts constants pub digests tokens fallback p i 16 j hj
  have hconv : (RcptV3.conv S_LE (c st) (fun j=>c (dl j))).eval tr 0 0 pub=Fp.ofNat (Seg.y3 d i) := by
    have he := congrArg Fp.ofNat (convS_row (Seg.stB d) i)
    simp only [ofNat_add_e,ofNat_mul_e] at he
    change (sum [smul 0 (c st),smul 0 (c (dl 0)),smul 232 (c (dl 1)),smul 137 (c (dl 2)),
      smul 4 (c (dl 3)),smul 35 (c (dl 4)),smul 199 (c (dl 5)),smul 138 (c (dl 6))]).eval tr 0 0 pub=_
    simp only [eval_sum_cons,eval_sum_nil,eval_smul,eval_c,hst,
      hd 0 (by decide),hd 1 (by decide),hd 2 (by decide),hd 3 (by decide),hd 4 (by decide),hd 5 (by decide),hd 6 (by decide),
      byteDelay_offset,Nat.reduceAdd,natCast_eq]
    change _=Fp.ofNat (RcptGen.conv Rcpt.S_LE (Seg.stB d) i)
    simp only [show Fp.ofNat 0=(0:Fp) from rfl]
    grind only
  have hnext (hn' : i+1<16) : tr.cell 0 ((0+1)%tr.height 0) c3=Fp.ofNat (chain (Seg.y3 d) (i+1)) := by
    change receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p next c3=_
    rw [hn hn']
    exact (deposit_base_cells accounts constants pub digests tokens fallback p (i+1) 16).2.2.2.2.2.1
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  · have he := congrArg Fp.ofNat (Nat.mod_add_div (Seg.sq d i) 256)
    rw [deposit_sq_mod h hi,deposit_sq_div h] at he
    simp only [Seg.sq,ofNat_add_e,ofNat_mul_e] at he
    simp only [dp,eval_mul,eval_sub,eval_add,eval_smul,eval_c,hg,hc,hq,hcarry,hconv,natCast_eq]
    grind only
  · simp only [dp,eval_mul,eval_c,hg,hfs,hc]
    by_cases hz : i=0
    · subst i;change (1:Fp)*1*0=0;grind only
    · rw [if_neg hz];grind only
  · simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hcarry]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega)];grind only
  · simp only [dp,eval_mul3,eval_c,hg,hfe,hcarry]
    by_cases he : i+1=16
    · rw [if_pos he,he,deposit_c3d_final h];change (1:Fp)*1*0=0;grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

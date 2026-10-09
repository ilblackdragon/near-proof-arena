import ZkFormal.NearV3.Assembly.RcptDepositFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def depositAdditionConstraints : List Expr := cDep.take 4

theorem receipt_deposit_byte (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell constants (streamAux pub digests fallback) p ⟨sDEP,i,len⟩ b=
      Fp.ofNat (gasByte p.input.receipt.deposit i) := by
  rw [receipt_stream_byte,if_neg (show sDEP∉regStates by decide)]
  change Fp.ofNat (((u128 p.input.receipt.deposit).getD i 0).toNat)=_
  rw [gasByte_native]

theorem receipt_deposit_addition_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositAdditionConstraints,e.eval
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback)))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  let d := nativeDepositData (accounts p) p.input.receipt
  let tr := receiptPair (booleanConstants constants)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p ⟨sDEP,i,16⟩ next
  have hg : tr.cell 0 0 sDEP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hbef : tr.cell 0 0 bef=Fp.ofNat (Seg.befB d i) :=
    (deposit_base_cells accounts constants pub digests tokens fallback p i 16).1
  have hc : tr.cell 0 0 c1=Fp.ofNat (chain (Seg.y1 d) i) :=
    (deposit_base_cells accounts constants pub digests tokens fallback p i 16).2.2.2.1
  have hb : tr.cell 0 0 b=Fp.ofNat (Seg.depB d i) :=
    receipt_deposit_byte (booleanConstants constants) pub digests
      (tokenAux tokens (booleanReceiptAux (depositAux accounts fallback))) p i 16
  have ha : aftE.eval tr 0 0 pub=Fp.ofNat (Seg.aftB d i) :=
    deposit_after_eval accounts constants pub digests tokens fallback p i 16 next
  have hncarry : tr.cell 0 0 (xb 8)=Fp.ofNat (chain (Seg.y1 d) (i+1)) :=
    deposit_after_carry accounts constants pub digests tokens fallback p i 16 h
  have hnext (hn' : i+1<16) : tr.cell 0 ((0+1)%tr.height 0) c1=Fp.ofNat (chain (Seg.y1 d) (i+1)) := by
    change receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback))) p next c1=_
    rw [hn hn']
    exact (deposit_base_cells accounts constants pub digests tokens fallback p (i+1) 16).2.2.2.1
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  · have he := congrArg Fp.ofNat (Nat.mod_add_div (Seg.sa d i) 256)
    rw [deposit_sa_mod h hi,deposit_sa_div h] at he
    simp only [Seg.sa,Seg.y1,ofNat_add_e,ofNat_mul_e] at he
    simp only [dp,eval_mul,eval_sub,eval_add,eval_smul,eval_sum_cons,eval_sum_nil,eval_c,hg,hbef,hb,hc,ha,hncarry,natCast_eq]
    grind only
  · simp only [dp,eval_mul,eval_c,hg,hfs,hc]
    by_cases hz : i=0
    · subst i;change (1:Fp)*1*0=0;grind only
    · rw [if_neg hz];grind only
  · simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hncarry]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega)];grind only
  · simp only [dp,eval_mul3,eval_c,hg,hfe,hncarry]
    by_cases he : i+1=16
    · rw [if_pos he,he,deposit_c1d_final h];change (1:Fp)*1*0=0;grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

import ZkFormal.NearV3.Assembly.RcptDepositStorageLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render RcptGen RcptP

def depositDelayConstraints : List Expr :=
  (List.range 7).map (fun j=>mul3 dp (c fs) (c (dl j))) ++
  [mul3 dp (not (c fe)) (sub (n (dl 0)) (c st))] ++
  (List.range 6).map (fun j=>mul3 dp (not (c fe)) (sub (n (dl (j+1))) (c (dl j))))

theorem receipt_deposit_delay_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) (hi : i<16)
    (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩) :
    ∀e∈depositDelayConstraints,e.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (depositAux accounts fallback))) p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  let cn := booleanConstants constants
  let aux := tokenReceiptAux pub digests tokens (booleanReceiptAux
    (depositAux accounts fallback))
  let tr := receiptPair cn aux p ⟨sDEP,i,16⟩ next
  have hg : tr.cell 0 0 sDEP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  let d := nativeDepositData (accounts p) p.input.receipt
  have hc (j : Nat) (hj : j<7) : tr.cell 0 0 (dl j)=Fp.ofNat (byteDelay (Seg.stB d) j i) :=
    deposit_storage_dl_cell accounts constants pub digests tokens fallback p i 16 j hj
  have hnext (h : i+1<16) (j : Nat) (hj : j<7) :
      tr.cell 0 ((0+1)%(tr.height 0)) (dl j)=Fp.ofNat (byteDelay (Seg.stB d) j (i+1)) := by
    change receiptCell cn aux p next (dl j)=_
    rw [hn h]
    exact deposit_storage_dl_cell accounts constants pub digests tokens fallback p (i+1) 16 j hj
  have hst : tr.cell 0 0 st=Fp.ofNat (Seg.stB d i) :=
    (deposit_base_cells accounts constants pub digests tokens fallback p i 16).2.2.1
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [depositDelayConstraints,List.mem_append] at he
  rcases he with (he|he)|he
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    simp only [dp,eval_mul3,eval_c,hg,hfs,hc j hj']
    by_cases hz : i=0
    · subst i
      simp only [ite_true,byteDelay_zero,show Fp.ofNat 0=(0:Fp) from rfl]
      grind only
    · rw [if_neg hz];grind only
  · simp only [List.mem_singleton] at he
    subst e
    simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hst]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega) 0 (by decide),byteDelay_head]
      grind only
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' : j<6 := List.mem_range.mp hj
    simp only [dp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hc j (by omega)]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega) (j+1) (by omega),byteDelay_shift]
      grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

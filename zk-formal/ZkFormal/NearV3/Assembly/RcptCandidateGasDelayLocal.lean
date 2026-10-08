import ZkFormal.NearV3.Assembly.RcptCandidateGasDelayCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def candidateGasDelayConstraints : List Expr :=
  (List.range 8).map (fun i=>mul3 gp (c fs) (c (dl i))) ++
  [mul3 gp (Dsl.not (c fe)) (sub (n (dl 0)) (c pc)),
   mul3 gp (Dsl.not (c fe)) (sub (n (dl 4)) systemSurplus)] ++
  ([1,2,3,5,6,7].map fun i=>mul3 gp (Dsl.not (c fe)) (sub (n (dl i)) (c (dl (i-1)))))

theorem candidateGasDelayConstraints_mem : ∀e∈candidateGasDelayConstraints,e∈systemGasConstraints := by
  intro e he
  simp only [candidateGasDelayConstraints,List.mem_append] at he
  simp only [systemGasConstraints,gasConstraintsWith,List.mem_append]
  grind only

theorem candidateGasDelayConstraints_length : candidateGasDelayConstraints.length=16 := rfl

theorem receipt_candidateGasDelay_local (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) (hi : i<16)
    (next : Coord) (hn : i+1<16→next=⟨sGP,i+1,16⟩)
    (hr : p.input.receipt.gasPrice<256^16) (hp : ctx.gasPrice<256^16) :
    ∀e∈candidateGasDelayConstraints,e.eval (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,16⟩ next) 0 0 pub=0 := by
  let cn := booleanConstants (gasEffectiveConstants ctx constants)
  let aux := tokenReceiptAux pub digests tokens (booleanReceiptAux
    (candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))
  let tr := receiptPair cn aux p ⟨sGP,i,16⟩ next
  have hg : tr.cell 0 0 sGP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hc (j : Nat) (hj : j<8) : tr.cell 0 0 (dl j)=Fp.ofNat (candidateGasDelayByte ctx p.input.receipt j i) :=
    candidateGasDelay_cell ctx (gasEffectiveConstants ctx constants) pub digests tokens
      (gasEffectiveAux ctx (gasBorrowAux ctx fallback)) p i 16 j hj
  have hnext (h : i+1<16) (j : Nat) (hj : j<8) :
      tr.cell 0 ((0+1)%(tr.height 0)) (dl j)=Fp.ofNat (candidateGasDelayByte ctx p.input.receipt j (i+1)) := by
    change receiptCell cn aux p next (dl j)=_
    rw [hn h]
    exact candidateGasDelay_cell ctx (gasEffectiveConstants ctx constants) pub digests tokens
      (gasEffectiveAux ctx (gasBorrowAux ctx fallback)) p (i+1) 16 j hj
  have hpc : tr.cell 0 0 pc=Fp.ofNat (gasByte (gasBurnPrice ctx p.input.receipt) i) := by
    rw [← gasEffectiveByte_price]
    exact candidateGasDelay_pc_cell ctx (gasEffectiveConstants ctx constants) pub digests tokens fallback p i 16
  have hsur : systemSurplus.eval tr 0 0 pub=Fp.ofNat (gasByte (gasSurplusPrice ctx p.input.receipt) i) := by
    simpa only [gasNativeSurplusByte_price ctx p.input.receipt hr hp i hi] using candidateGasDelay_surplus_eval ctx constants pub digests tokens fallback p i 16 next
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [candidateGasDelayConstraints,List.mem_append] at he
  rcases he with (he|he)|he
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    simp only [gp,eval_mul3,eval_c,hg,hfs,hc j hj']
    by_cases hz : i=0
    · subst i
      simp only [ite_true,candidateGasDelay_zero,show Fp.ofNat 0=(0:Fp) from rfl]
      grind only
    · rw [if_neg hz];grind only
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    all_goals simp only [gp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hpc,hsur]
    all_goals by_cases he : i+1=16
    all_goals first
      | (rw [if_pos he];grind only)
      | skip
    all_goals rw [if_neg he]
    · rw [hnext (by omega) 0 (by decide),(candidateGasDelay_heads ctx p.input.receipt i).1]
      grind only
    · rw [hnext (by omega) 4 (by decide),(candidateGasDelay_heads ctx p.input.receipt i).2]
      grind only
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' : j<8 ∧ j-1<8 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;omega
    simp only [gp,eval_mul3,eval_not,eval_sub,eval_c,eval_n,hg,hfe,hc (j-1) hj'.2]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnext (by omega) j hj'.1,candidateGasDelay_shift ctx p.input.receipt j i hj]
      grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

import ZkFormal.NearV3.Assembly.RcptGasProductFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem candidateGasDelay_zero (ctx : ApplyCtx) (r : Receipt) (j : Nat) : candidateGasDelayByte ctx r j 0=0 := by
  simp only [candidateGasDelayByte,byteDelay_zero,ite_self]

theorem candidateGasDelay_heads (ctx : ApplyCtx) (r : Receipt) (i : Nat) :
    candidateGasDelayByte ctx r 0 (i+1)=gasByte (gasBurnPrice ctx r) i ∧
    candidateGasDelayByte ctx r 4 (i+1)=gasByte (gasSurplusPrice ctx r) i := by
  simp only [candidateGasDelayByte,Nat.reduceLT,ite_true,ite_false,Nat.sub_self,byteDelay_head,and_self]

theorem candidateGasDelay_shift (ctx : ApplyCtx) (r : Receipt) (j i : Nat)
    (hj : j∈[1,2,3,5,6,7]) : candidateGasDelayByte ctx r j (i+1)=candidateGasDelayByte ctx r (j-1) i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [candidateGasDelayByte,Nat.reduceLT,Nat.reduceSub,ite_true,ite_false]
  all_goals exact byteDelay_shift _ _ _

theorem gasBorrow_candidateDelay_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (candidateGasDelayAux ctx fallback)=candidateGasDelayAux ctx (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (candidateGasDelayAux ctx)
  · intro a b p row col he
    simp only [candidateGasDelayAux,he]
  · intro a p row col hs hc
    have hn : ¬(row.state=sGP ∧ dl 0≤col ∧ col<dl 8) := by
      simp only [c1,xb] at hc
      simp only [dl]
      omega
    simp only [candidateGasDelayAux,if_neg hn]

theorem gasEffective_candidateDelay_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (candidateGasDelayAux ctx fallback)=candidateGasDelayAux ctx (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (candidateGasDelayAux ctx)
  · intro a b p row col he
    simp only [candidateGasDelayAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem candidateGasDelay_pc_cell (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ pc=
      Fp.ofNat (gasEffectiveByte ctx p.input.receipt i) := rfl

theorem candidateGasDelay_difference_eval (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    DE.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (gasDifference ctx p.input.receipt i) := by
  simpa only [gasBorrow_candidateDelay_commute,←gasEffective_borrow_commute] using
    gasDifference_eval ctx constants pub digests tokens (candidateGasDelayAux ctx (gasEffectiveAux ctx fallback)) p i len next

theorem candidateGasDelay_surplus_eval (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    systemSurplus.eval (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (gasNativeSurplusByte ctx p.input.receipt i) := by
  let tr := receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
    (tokenReceiptAux pub digests tokens (booleanReceiptAux
      (candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ next
  have hg : tr.cell 0 0 gq=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice) &&
      !(p.input.receipt.predecessorId==AccountId.system)) := by
    change boolInput gq (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)
  change systemSurplus.eval tr 0 0 pub=_
  simp only [systemSurplus,eval_mul,eval_c,hg]
  rw [candidateGasDelay_difference_eval]
  by_cases hs : p.input.receipt.predecessorId==AccountId.system
  all_goals by_cases hp : ctx.gasPrice≤p.input.receipt.gasPrice
  all_goals simp only [gasNativeSurplusByte,gasRawSurplusByte,hs,hp,decide_true,decide_false,
    Bool.not_true,Bool.not_false,Bool.and_true,Bool.and_false,bitCell,Bool.false_eq_true,
    ite_true,ite_false,show Fp.ofNat 0=(0:Fp) from rfl]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

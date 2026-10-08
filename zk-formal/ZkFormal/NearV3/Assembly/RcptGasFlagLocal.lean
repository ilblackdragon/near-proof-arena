import ZkFormal.NearV3.Assembly.RcptGasFlagFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasFlagConstraints : List Expr := (cGas.drop 20).take 4

theorem gasBorrow_flag_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (gasFlagAux ctx fallback)=gasFlagAux ctx (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (gasFlagAux ctx)
  · intro a b p row col he
    simp only [gasFlagAux,he]
  · intro a p row col hs hc
    have hn : col≠sumD ∧ col≠invA := by
      simp only [c1,xb] at hc
      simp only [sumD,invA]
      omega
    simp only [gasFlagAux,hn.1,hn.2,and_false,ite_false]

set_option maxHeartbeats 2000000 in
theorem receipt_gasFlag_local (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16)
    (hr : p.input.refund=nativeRefund ctx p.input.receipt)
    (hg : p.input.receipt.gasPrice<256^16) (hc : ctx.gasPrice<256^16)
    (next : Coord) (hn : i+1<16→next=⟨sGP,i+1,16⟩) :
    ∀e∈gasFlagConstraints,e.eval
      (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
        (tokenReceiptAux pub digests tokens
          (booleanReceiptAux (gasFlagAux ctx (gasBorrowAux ctx fallback))))
        p ⟨sGP,i,16⟩ next) 0 0 pub=0 := by
  let cn := gasEffectiveConstants ctx constants
  let aux := gasFlagAux ctx (gasBorrowAux ctx fallback)
  let tr := receiptPair (booleanConstants cn) (tokenReceiptAux pub digests tokens (booleanReceiptAux aux)) p ⟨sGP,i,16⟩ next
  have hgp : tr.cell 0 0 sGP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hhr : tr.cell 0 0 RcptV3.hr=bitCell (nativeRefund ctx p.input.receipt) := by
    change bitCell p.input.refund=_
    rw [hr]
  have hgq : tr.cell 0 0 gq=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice) &&
      !(p.input.receipt.predecessorId==AccountId.system)) := by
    change boolInput gq (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)
  have hsum : tr.cell 0 0 sumD=Fp.ofNat (gasDifferenceSum ctx p.input.receipt (i+1)) := rfl
  have hinv : tr.cell 0 0 invA=gasFlagInverse ctx p.input.receipt := rfl
  have hd : DE.eval tr 0 0 pub=Fp.ofNat (gasDifference ctx p.input.receipt i) := by
    dsimp only [tr,aux]
    rw [←gasBorrow_flag_commute]
    exact gasDifference_eval ctx cn pub digests tokens (gasFlagAux ctx fallback) p i 16 next
  have hnSum (h : i+1<16) : tr.cell 0 ((0+1)%(tr.height 0)) sumD=
      Fp.ofNat (gasDifferenceSum ctx p.input.receipt (i+2)) := by
    change receiptCell (booleanConstants cn) (tokenReceiptAux pub digests tokens (booleanReceiptAux aux)) p next sumD=_
    rw [hn h]
    rfl
  have hdn (h : i+1<16) : DEn.eval tr 0 0 pub=Fp.ofNat (gasDifference ctx p.input.receipt (i+1)) := by
    change DE.eval (receiptPair (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux aux)) p next ⟨sGP,0,16⟩) 0 0 pub=_
    rw [hn h]
    dsimp only [aux]
    rw [←gasBorrow_flag_commute]
    exact gasDifference_eval ctx cn pub digests tokens (gasFlagAux ctx fallback) p (i+1) 16 ⟨sGP,0,16⟩
  intro e he
  change e.eval tr 0 0 pub=0
  change e∈[_,_,_,_] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  · simp only [gp,eval_mul,eval_mul3,eval_not,eval_c,hgp,hhr,hgq,hd]
    have hh := gasFlag_noRefund_product ctx p.input.receipt i
    grind only
  · simp only [gp,eval_mul3,eval_sub,eval_c,hgp,hfs,hsum,hd]
    by_cases hz : i=0
    · subst i
      simp only [ite_true,gasDifferenceSum,ZkFormal.Near.Render.RcptP.sumR,Nat.zero_add]
      grind only
    · rw [if_neg hz];grind only
  · simp only [gp,eval_mul3,eval_not,eval_sub,eval_add,eval_c,eval_n,hgp,hfe,hsum]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he,hnSum (by omega),hdn (by omega)]
      have hh : Fp.ofNat (gasDifferenceSum ctx p.input.receipt (i+2))=
          Fp.ofNat (gasDifferenceSum ctx p.input.receipt (i+1))+Fp.ofNat (gasDifference ctx p.input.receipt (i+1)) := by
        exact ZkFormal.Near.Render.RcptP.ofNat_add_e _ _
      rw [hh];grind only
  · simp only [gp,eval_mul3,eval_sub,eval_mul,eval_c,hgp,hfe,hsum,hinv,hhr]
    by_cases he : i+1=16
    · rw [if_pos he,he,gasFlag_inverse_correct ctx p.input.receipt hg hc]
      grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

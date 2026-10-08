import ZkFormal.NearV3.Assembly.RcptGasPriceCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

def gasBorrowConstraints : List Expr :=
  [ .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))),
    .mul (.mul gp (c fs)) (c c1), mul3 gp (Dsl.not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 gp (c fe) (sub (c (xb 8)) (Dsl.not (c ge))) ]

theorem gasBorrowConstraints_mem : ∀e∈gasBorrowConstraints,e∈cGas := by
  intro e he
  simp only [gasBorrowConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl <;> simp [cGas]

theorem receipt_gasBorrow_local (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) (hi : i<16)
    (next : Coord) (hn : i+1<16→next=⟨sGP,i+1,16⟩)
    (hr : p.input.receipt.gasPrice<256^16) (hc : ctx.gasPrice<256^16) :
    ∀e∈gasBorrowConstraints,e.eval (receiptPair (booleanConstants (nativePriceConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback)))
      p ⟨sGP,i,16⟩ next) 0 0 pub=0 := by
  let cn := booleanConstants (nativePriceConstants ctx constants)
  let aux := tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))
  let tr := receiptPair cn aux p ⟨sGP,i,16⟩ next
  have hg : tr.cell 0 0 sGP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hge : tr.cell 0 0 ge=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice)) := by
    change boolInput ge (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)
  have hbytes := receipt_gas_price_bytes ctx cn pub hpub digests (tokenAux tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p i 16 hi
  have hb : tr.cell 0 0 b=Fp.ofNat (gasByte p.input.receipt.gasPrice i) := hbytes.1
  have hp : tr.cell 0 0 (reg 0)=Fp.ofNat (gasByte ctx.gasPrice i) := hbytes.2
  have hbr : tr.cell 0 0 c1=Fp.ofNat (gasBorrow ctx p.input.receipt i) :=
    gasBorrow_cell ctx (nativePriceConstants ctx constants) pub digests tokens fallback p i 16
  have hbn : tr.cell 0 0 (xb 8)=Fp.ofNat (gasBorrow ctx p.input.receipt (i+1)) :=
    gasBorrow_next_bit_cell ctx (nativePriceConstants ctx constants) pub digests tokens fallback p i 16
  have hd : DE.eval tr 0 0 pub=Fp.ofNat (gasDifference ctx p.input.receipt i) :=
    gasDifference_eval ctx (nativePriceConstants ctx constants) pub digests tokens fallback p i 16 next
  intro e he
  change e.eval tr 0 0 pub=0
  simp only [gasBorrowConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl
  · simp only [gp,eval_mul,eval_sub,eval_add,eval_smul,eval_c,hg,hb,hp,hbr,hbn,hd]
    have he := congrArg Fp.ofNat (gasDifference_step ctx p.input.receipt i)
    simp only [ofNat_add_e,ofNat_mul_e,show Fp.ofNat 256=(256:Fp) from rfl] at he
    grind only
  · simp only [gp,eval_mul,eval_c,hg,hfs,hbr]
    by_cases hz : i=0
    · subst i
      rw [gasBorrow_zero]
      simp only [ite_true,show Fp.ofNat 0=(0:Fp) from rfl]
      grind only
    · rw [if_neg hz];grind only
  · simp only [gp,eval_mul3,eval_not,eval_sub,eval_c,hg,hfe,hbn,eval_n]
    by_cases he : i+1=16
    · rw [if_pos he];grind only
    · rw [if_neg he]
      have hh : tr.cell 0 ((0+1)%(tr.height 0)) c1=Fp.ofNat (gasBorrow ctx p.input.receipt (i+1)) := by
        change receiptCell cn aux p next c1=_
        rw [hn (by omega)]
        exact gasBorrow_cell ctx (nativePriceConstants ctx constants) pub digests tokens fallback p (i+1) 16
      rw [hh];grind only
  · simp only [gp,eval_mul3,eval_not,eval_sub,eval_c,hg,hfe,hbn,hge]
    by_cases he : i+1=16
    · rw [if_pos he,he,gasBorrow_final ctx p.input.receipt hr hc]
      by_cases hh : ctx.gasPrice≤p.input.receipt.gasPrice
      · simp only [hh,ite_true,bitCell,decide_true,show Fp.ofNat 0=(0:Fp) from rfl];grind only
      · simp only [hh,ite_false,bitCell,decide_false,Bool.false_eq_true,show Fp.ofNat 1=(1:Fp) from rfl];grind only
    · rw [if_neg he];grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton

import ZkFormal.NearV3.Assembly.RcptGasProductCells
import ZkFormal.NearV3.Assembly.RcptSystemGasZero

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasProduct_constraints_split : gasProductConstraints systemSurplus=
    gasSingleProduct (c pc) (c burnt) (c c2) (bitsX 9 11) (n c2) (fun j=>c (dl j)) ++
    gasSingleProduct systemSurplus (c ramt) (c c3) (bitsX 20 11) (n c3) (fun j=>c (dl (4+j))) := rfl

def nativeGasProductAux (ctx : ApplyCtx) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) : ReceiptPlan→Coord→Nat→Fp :=
  gasProductAux ctx (candidateGasDelayAux ctx (gasEffectiveAux ctx
    (gasBorrowAux ctx (gasTokenAux tokens fallback))))

theorem nativeGasProduct_delay_outer (ctx : ApplyCtx) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) : nativeGasProductAux ctx tokens fallback=
    candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx
      (gasProductAux ctx (gasTokenAux tokens fallback)))) := by
  unfold nativeGasProductAux
  rw [←candidateGasDelay_product_commute,←gasEffective_product_commute,←gasBorrow_product_commute]

theorem receipt_gasProduct_local (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sGP,i+1,16⟩)
    (hr : p.input.receipt.gasPrice<256^16) (hp : ctx.gasPrice<256^16)
    (ht : (tokens p).burnt=nativeBurn ctx p.input.receipt)
    (hb : nativeBurn ctx p.input.receipt<256^16)
    (hs : nativeRefundAmount ctx p.input.receipt<256^16) :
    ∀e∈gasProductConstraints systemSurplus,e.eval
      (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (nativeGasProductAux ctx tokens fallback)))
        p ⟨sGP,i,16⟩ next) 0 0 pub=0 := by
  let cn := gasEffectiveConstants ctx constants
  let lower := candidateGasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx (gasTokenAux tokens fallback)))
  let tr := receiptPair (booleanConstants cn)
    (tokenReceiptAux pub digests tokens (booleanReceiptAux (nativeGasProductAux ctx tokens fallback)))
    p ⟨sGP,i,16⟩ next
  have hburn : Params.G*gasBurnPrice ctx p.input.receipt<256^16 := by
    rw [←nativeBurn_price];exact hb
  have hsurp : Params.G*gasSurplusPrice ctx p.input.receipt<256^16 := by
    rw [←nativeRefundAmount_price];exact hs
  have hg : tr.cell 0 0 sGP=1 := rfl
  have hfs : tr.cell 0 0 fs=if i=0 then 1 else 0 := rfl
  have hfe : tr.cell 0 0 fe=if i+1=16 then 1 else 0 := rfl
  have hpc : (c pc).eval tr 0 0 pub=Fp.ofNat (gasByte (gasBurnPrice ctx p.input.receipt) i) := by
    change Fp.ofNat (gasEffectiveByte ctx p.input.receipt i)=_
    rw [gasEffectiveByte_price]
  have hburnt : (c burnt).eval tr 0 0 pub=Fp.ofNat (gasByte (Params.G*gasBurnPrice ctx p.input.receipt) i) := by
    change Fp.ofNat (gasByte (tokens p).burnt i)=_
    rw [ht,nativeBurn_price]
  have hc2 : (c c2).eval tr 0 0 pub=Fp.ofNat (gasMulCarry (gasBurnPrice ctx p.input.receipt) i) := rfl
  have hc3 : (c c3).eval tr 0 0 pub=Fp.ofNat (gasMulCarry (gasSurplusPrice ctx p.input.receipt) i) := rfl
  have hramt : (c ramt).eval tr 0 0 pub=Fp.ofNat (gasByte (Params.G*gasSurplusPrice ctx p.input.receipt) i) := rfl
  have hb2 : (bitsX 9 11).eval tr 0 0 pub=Fp.ofNat (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) :=
    gasProduct_burn_bits ctx cn pub digests tokens lower p i 16 next
  have hb3 : (bitsX 20 11).eval tr 0 0 pub=Fp.ofNat (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) :=
    gasProduct_surplus_bits ctx cn pub digests tokens lower p i 16 next
  have hn2 (h : i+1<16) : (n c2).eval tr 0 0 pub=Fp.ofNat (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) := by
    change receiptCell (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (nativeGasProductAux ctx tokens fallback))) p next c2=_
    rw [hn h];rfl
  have hn3 (h : i+1<16) : (n c3).eval tr 0 0 pub=Fp.ofNat (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) := by
    change receiptCell (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (nativeGasProductAux ctx tokens fallback))) p next c3=_
    rw [hn h];rfl
  have hsur : systemSurplus.eval tr 0 0 pub=Fp.ofNat (gasByte (gasSurplusPrice ctx p.input.receipt) i) := by
    change systemSurplus.eval (receiptPair (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (nativeGasProductAux ctx tokens fallback)))
      p ⟨sGP,i,16⟩ next) 0 0 pub=_
    rw [nativeGasProduct_delay_outer]
    rw [←gasNativeSurplusByte_price ctx p.input.receipt hr hp i hi]
    exact candidateGasDelay_surplus_eval ctx constants pub digests tokens
      (gasProductAux ctx (gasTokenAux tokens fallback)) p i 16 next
  have hd (j : Nat) (hj : j<8) : (c (dl j)).eval tr 0 0 pub=Fp.ofNat (candidateGasDelayByte ctx p.input.receipt j i) := by
    change receiptCell (booleanConstants cn)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (nativeGasProductAux ctx tokens fallback)))
      p ⟨sGP,i,16⟩ (dl j)=_
    rw [nativeGasProduct_delay_outer]
    exact candidateGasDelay_cell ctx cn pub digests tokens
      (gasEffectiveAux ctx (gasBorrowAux ctx (gasProductAux ctx (gasTokenAux tokens fallback)))) p i 16 j hj
  intro e he
  change e.eval tr 0 0 pub=0
  rw [gasProduct_constraints_split,List.mem_append] at he
  rcases he with he|he
  · apply gasSingleProduct_local tr 0 0 pub (c pc) (c burnt) (c c2) (bitsX 9 11) (n c2)
      (fun j=>c (dl j)) (gasBurnPrice ctx p.input.receipt) i hi hburn hg hfs hfe hpc hburnt hc2 hb2 hn2 ?_ e he
    intro j hj
    rw [hd j (by omega),candidateGasDelayByte,if_pos hj]
  · apply gasSingleProduct_local tr 0 0 pub systemSurplus (c ramt) (c c3) (bitsX 20 11) (n c3)
      (fun j=>c (dl (4+j))) (gasSurplusPrice ctx p.input.receipt) i hi hsurp hg hfs hfe hsur hramt hc3 hb3 hn3 ?_ e he
    intro j hj
    rw [hd (4+j) (by omega),candidateGasDelayByte,if_neg (by omega),show 4+j-4=j from by omega]

end ZkFormal.NearV3.Assembly.RcptSkeleton

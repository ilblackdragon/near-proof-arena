import ZkFormal.NearV3.Assembly.RcptGasBorrowFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Ordinary byte binding for the prepared block gas price. -/
def GasPublicBytes (ctx : ApplyCtx) (pub : List Fp) : Prop :=
  ∀i,i<16→pub.getD (PH_GP+i) 0=Fp.ofNat (gasByte ctx.gasPrice i)

theorem receipt_gas_price_bytes (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (hi : i<16) :
    receiptCell constants (streamAux pub digests fallback) p ⟨sGP,i,len⟩ b=Fp.ofNat (gasByte p.input.receipt.gasPrice i) ∧
    receiptCell constants (streamAux pub digests fallback) p ⟨sGP,i,len⟩ (reg 0)=Fp.ofNat (gasByte ctx.gasPrice i) := by
  constructor
  · rw [receipt_stream_byte,if_neg (show sGP∉regStates by decide)]
    change Fp.ofNat (((u128 p.input.receipt.gasPrice).getD i 0).toNat)=_
    rw [gasByte_native]
  · rw [receipt_stream_reg _ _ _ _ _ _ 0 (by decide),registerCell_read _ _ 0 (by decide),Nat.add_zero]
    rw [receiptStream_load pub digests p (state:=sGP) (es:=pubs PH_GP 16) (by simp [loads])]
    rw [registerLoad_exact p.input pub (state:=sGP) (es:=pubs PH_GP 16) (by simp [loads])]
    simp only [pubs,List.map_map,Function.comp_def,eval_pub]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]
    exact hpub i hi

end ZkFormal.NearV3.Assembly.RcptSkeleton

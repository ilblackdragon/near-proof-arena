import ZkFormal.NearV3.Assembly.RcptPredecessorFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

theorem predecessor_bytes (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hs : row.state=sP) :
    receiptCell constants (streamAux pub digests fallback) p row b=
      Fp.ofNat ((characterData p.input.receipt).pred.getD row.index 0) ∧
    receiptCell constants (streamAux pub digests fallback) p row (reg 0)=Fp.ofNat (sysB row.index) := by
  constructor
  · rw [receipt_stream_byte]
    simp only [hs,show sP∉regStates by decide,ite_false]
    simp only [nativeFieldByte,hs]
    change Fp.ofNat ((p.input.receipt.predecessorId.getD row.index 0).toNat)=_
    simp only [characterData,toNats,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases p.input.receipt.predecessorId[row.index]? <;> rfl
  · rw [receipt_stream_reg _ _ _ _ _ _ 0 (by decide)]
    rw [hs]
    have hh : receiptStream pub digests p sP=[115,121,115,116,101,109].map Fp.ofNat := rfl
    rw [hh]
    change ([115,121,115,116,101,109].map Fp.ofNat).getD row.index 0=Fp.ofNat ([115,121,115,116,101,109].getD row.index 0)
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ([115,121,115,116,101,109]:List Nat)[row.index]? <;> rfl

theorem predecessor_score_end (r : Receipt) (i : Nat) (hi : i+1=r.predecessorId.length) :
    Fp.ofNat (pP (characterData r))=Fp.ofNat (accP (characterData r) i)+
      (Fp.ofNat r.predecessorId.length-6)*(Fp.ofNat r.predecessorId.length-6) := by
  unfold pP
  rw [ofNat_mod,ofNat_add_e,ofNat_sqd]
  have he : (characterData r).pred.length=r.predecessorId.length := by simp [characterData,toNats]
  rw [he,show r.predecessorId.length-1=i by omega]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton

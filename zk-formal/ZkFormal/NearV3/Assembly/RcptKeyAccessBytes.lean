import ZkFormal.NearV3.Assembly.RcptKeyAccountPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem keyPk_character_nibbles (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    let tr := receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (characterAux (keyAux accountId accessId fallback))))
      p ⟨sPK,i,len⟩ ⟨sPK,i,len⟩
    hiPK.eval tr 0 0 pub=Fp.ofNat (keyByte p ⟨sPK,i,len⟩/16) ∧
      loPK.eval tr 0 0 pub=Fp.ofNat (keyByte p ⟨sPK,i,len⟩%16) := by
  simpa only [key_character_commute] using keyPk_nibbles_eval accountId accessId constants pub digests tokens
    (characterAux fallback) p i len

theorem receipt_key_pk_byte (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hs : row.state=sPK) :
    receiptCell constants (streamAux pub digests fallback) p row b=Fp.ofNat (keyByte p row) := by
  rw [receipt_stream_byte,hs,if_neg (show sPK∉regStates by decide)]
  simp only [nativeFieldByte,keyByte,hs,sP,sV,sRID,sS,sPK,Nat.reduceEqDiff,ite_false,ite_true]

theorem receipt_key_tag_byte (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hs : row.state=sKT) (hi : row.index<fieldLen p.input row.state) :
    receiptCell constants (streamAux pub digests fallback) p row b=Fp.ofNat p.input.receipt.signerPk.tag := by
  have hz : row.index=0 := by
    rw [hs] at hi
    change row.index<1 at hi
    omega
  rw [receipt_stream_byte,hs,if_pos (show sKT∈regStates by decide)]
  simp only [receiptStream,sKT,sXRI,sXLH,Nat.reduceEqDiff,false_or,ite_false]
  change (registerLoad p.input pub sKT).getD row.index 0=_
  rw [registerLoad_exact p.input pub (state:=sKT) (es:=[c kt]) (by simp [loads])]
  rw [hz]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton

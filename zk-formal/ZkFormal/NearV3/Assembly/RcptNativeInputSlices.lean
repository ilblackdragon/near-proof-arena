import ZkFormal.NearV3.Assembly.RcptNativeFieldBytes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)

private abbrev nativeTrace := RoutingQCandidate.patchTrace
  (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0

include hb in
theorem native_predecessor_slice  :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).p=(p.input.receipt.predecessorId).map UInt8.toNat := by
  have hh := native_field_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb
    1 sP (4) (p.input.receipt.predecessorId)
    (by cases p.input.refund <;> rfl)
    (by cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,Vt] <;> omega)
    (by simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,u128,leN])
    (by decide) (fun i=>rfl)
  simpa only [rcptOf,inputShape,u128,leN_length] using hh

include hb in
theorem native_signer_slice  :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).s=(p.input.receipt.signerId).map UInt8.toNat := by
  have hh := native_field_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb
    7 sS (45+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length) (p.input.receipt.signerId)
    (by cases p.input.refund <;> rfl)
    (by cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,Vt] <;> omega)
    (by simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,u128,leN])
    (by decide) (fun i=>rfl)
  simpa only [rcptOf,inputShape,u128,leN_length] using hh

include hb in
theorem native_publickey_slice (hpk : p.input.receipt.signerPk.data.length=32+32*p.input.receipt.signerPk.tag) :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).pk=(p.input.receipt.signerPk.data).map UInt8.toNat := by
  have hh := native_field_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb
    9 sPK (46+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+p.input.receipt.signerId.length) (p.input.receipt.signerPk.data)
    (by cases p.input.refund <;> rfl)
    (by cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,Vt] <;> omega)
    (by simp [hpk,fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,u128,leN])
    (by decide) (fun i=>rfl)
  simpa only [rcptOf,inputShape,hpk,u128,leN_length] using hh

include hb in
theorem native_gasprice_slice  :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).gp=(u128 p.input.receipt.gasPrice).map UInt8.toNat := by
  have hh := native_field_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb
    10 sGP (78+Vt p.input.receipt.predecessorId.length p.input.receipt.receiverId.length p.input.receipt.signerId.length p.input.receipt.signerPk.tag) (u128 p.input.receipt.gasPrice)
    (by cases p.input.refund <;> rfl)
    (by cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,Vt] <;> omega)
    (by simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,u128,leN])
    (by decide) (fun i=>rfl)
  simpa only [rcptOf,inputShape,u128,leN_length] using hh

include hb in
theorem native_deposit_slice  :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).dep=(u128 p.input.receipt.deposit).map UInt8.toNat := by
  have hh := native_field_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb
    12 sDEP (107+Vt p.input.receipt.predecessorId.length p.input.receipt.receiverId.length p.input.receipt.signerId.length p.input.receipt.signerPk.tag) (u128 p.input.receipt.deposit)
    (by cases p.input.refund <;> rfl)
    (by cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,Vt] <;> omega)
    (by simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,u128,leN])
    (by decide) (fun i=>rfl)
  simpa only [rcptOf,inputShape,u128,leN_length] using hh

end ZkFormal.NearV3.Assembly.RcptSkeleton

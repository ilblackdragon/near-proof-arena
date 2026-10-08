import ZkFormal.NearV3.Assembly.RcptNativeInputSlices

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem native_borsh_bytes (xs : Bytes) (hl : xs.length≤64) :
    (borshBytes xs).map UInt8.toNat=RcptV.borshN (xs.map UInt8.toNat) := by
  have hn : xs.length<256 := by omega
  simp [borshBytes,RcptV.borshN,u32r,u32,leN,Nat.mod_eq_of_lt hn,Nat.div_eq_of_lt hn,List.map_append]

theorem native_publickey_bytes (pk : PublicKey) (ht : pk.tag≤1) :
    pk.encode.map UInt8.toNat=pk.tag::pk.data.map UInt8.toNat := by
  have hn : pk.tag<256 := by omega
  simp [PublicKey.encode,u8,leN,Nat.mod_eq_of_lt hn]

/-- Exact native receipt serialization from the honest physical view, including
both key tags and system receipts. No reconstructed-receipt equality is assumed. -/
theorem native_receipt_encoding (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hw : p.input.receipt.wf=true) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 (inputShape pre.length p.input)).enc=p.input.receipt.encode.map UInt8.toNat := by
  have hl : p.input.receipt.predecessorId.length≤64 ∧ p.input.receipt.receiverId.length≤64 ∧
      p.input.receipt.signerId.length≤64 ∧ p.input.receipt.signerPk.tag≤1 ∧
      p.input.receipt.receiptId.length=32 ∧
      p.input.receipt.signerPk.data.length=32+32*p.input.receipt.signerPk.tag := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  have hid : (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 (inputShape pre.length p.input)).rid=p.input.receipt.receiptId.map UInt8.toNat := by
    change colAt (RoutingQCandidate.patchTrace _ 0) 0 _ 32 b=_
    rw [patch_byte_slice]
    exact native_rid_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb hl.2.2.2.2.1
  unfold RcptV.enc
  rw [native_predecessor_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb,
    native_receiver_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb,hid,
    native_signer_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb,
    native_publickey_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb hl.2.2.2.2.2,
    native_gasprice_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb,
    native_deposit_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb]
  simp only [Receipt.encode,List.map_append,native_borsh_bytes _ hl.1,native_borsh_bytes _ hl.2.1,
    native_borsh_bytes _ hl.2.2.1,native_publickey_bytes _ hl.2.2.2.1,rcptOf,inputShape]
  simp [tailN,u32,leN,List.append_assoc]

end ZkFormal.NearV3.Assembly.RcptSkeleton

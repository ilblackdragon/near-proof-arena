import ZkFormal.NearV3.Candidates.NativeQueryKeyTraffic
import ZkFormal.NearV3.Assembly.RcptNativePeoSlices
import ZkFormal.NearV3.Assembly.RcptNativeInputSlices
namespace ZkFormal.NearV3.Candidates.NativeReceiptKeySymbols
open ZkFormal.Algebra NearSpec NearSpecV3 ZkFormal.Near Assembly RcptSkeleton RcptV3Proof

theorem nibbles_map (bs : Bytes) :
    nibbles bs=(bs.map UInt8.toNat).flatMap (fun b=>[b/16,b%16]) := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simp [nibbles,ih]

theorem account_symbols (x : RcptE) (r : Receipt)
    (hv:x.v=r.receiverId.map UInt8.toNat) :
    x.keySyms=accountKeyPath r.receiverId++[SYM_END] := by
  simp [RcptV.keySyms,hv,accountKeyPath,nibbles,nibbles_map]

theorem access_symbols (x : RcptE) (r : Receipt)
    (hs:x.s=r.signerId.map UInt8.toNat) (ht:x.kt=r.signerPk.tag)
    (hp:x.pk=r.signerPk.data.map UInt8.toNat)
    (he:r.signerId=r.receiverId) (hb:r.signerPk.tag<256) :
    x.akSyms=keyAccessKey r.receiverId r.signerPk++[SYM_END] := by
  simp [RcptE.akSyms,hs,ht,hp,he,keyAccessKey,PublicKey.encode,u8,leN,
    nibbles_map,List.map_append,Nat.mod_eq_of_lt hb]

theorem physical_account_symbols (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb:plannedRows lists=pre++plannedReceiptRows p++post) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 (inputShape pre.length p.input)).keySyms=
      accountKeyPath p.input.receipt.receiverId++[SYM_END] :=
  account_symbols _ _ (native_receiver_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb)

theorem physical_access_symbols (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb:plannedRows lists=pre++plannedReceiptRows p++post)
    (hw:p.input.receipt.wf=true) (he:p.input.receipt.signerId=p.input.receipt.receiverId) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 (inputShape pre.length p.input)).akSyms=
      keyAccessKey p.input.receipt.receiverId p.input.receipt.signerPk++[SYM_END] := by
  have htag:p.input.receipt.signerPk.tag≤1 := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,
      Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  have hpk:p.input.receipt.signerPk.data.length=32+32*p.input.receipt.signerPk.tag := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,
      Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  exact access_symbols _ _
    (native_signer_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb)
    rfl (native_publickey_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb hpk)
    he (by omega)

end ZkFormal.NearV3.Candidates.NativeReceiptKeySymbols

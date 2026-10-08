import ZkFormal.NearV3.Candidates.ReceiptPreparedFields
import ZkFormal.NearV3.Assembly.RcptNativeBodyLength

namespace ZkFormal.NearV3.Candidates.ReceiptPreparedFinalPublic
open NearSpec NearSpecV3 Sched ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton

theorem final_public {cb wb : Bytes} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} (overhead : Nat) (lists : List (List Input))
    (hp : prepD0 cb (nativeHint k w m)=.ok p) (hk : walkD0 cb=.ok k)
    (hd : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w)
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hf : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund (m.ctx k) x.receipt) :
    FinalPublicBytes lists m.result (ZkFormal.Udr.pubOf Fp (Public.preparedBytes
      (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)) := by
  obtain ⟨hn,hb,_,ht⟩:=ReceiptPreparedFields.native_fields hp hk hd hc hm
  have hlen : p.hdr.n=lists.flatten.length := by
    rw [hn,←hls,List.length_map]
  have hrun : applyNewChunk prims (m.ctx k) m.pre (lists.flatten.map Input.receipt)=.ok m.result := by
    rw [hls];exact hm.run
  have hbody : p.body.length=8+(lists.flatten.map refundLength).sum := by
    rw [hb]
    exact applyNewChunk_planned_body_length (m.ctx k) lists hw hf hrun
  let q:=RoutingBoundedLayout.boundedPrep p k.L k.H.shardId
  have hr : Public.RootsSized q := by exact prepD0_roots (p:=p) hp
  constructor
  · intro i hi
    rw [Public.pub_getD,ReceiptPreparedFields.count_byte q overhead i hr hi]
    change Fp.ofNat (((u32 p.hdr.n).getD i 0).toNat)=_
    rw [hlen]
  · intro i hi
    rw [Public.pub_getD,ReceiptPreparedFields.body_byte q overhead i hr hi]
    change Fp.ofNat (((u32 p.body.length).getD i 0).toNat)=_
    rw [hbody]
  · intro i hi
    rw [Public.pub_getD,ReceiptPreparedFields.burnt_byte q overhead i hr hi]
    change Fp.ofNat (((u128 p.hdr.balanceBurnt).getD i 0).toNat)=_
    rw [ht]

theorem own_public {cb wb : Bytes} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} (overhead : Nat)
    (hp : prepD0 cb (nativeHint k w m)=.ok p) (hk : walkD0 cb=.ok k)
    (hd : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w) :
    ∀i<8,(ZkFormal.Udr.pubOf Fp (Public.preparedBytes
      (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)).getD (PH_OWN+i) 0=
      Fp.ofNat (((u64 k.H.shardId).getD i 0).toNat) := by
  intro i hi
  let q:=RoutingBoundedLayout.boundedPrep p k.L k.H.shardId
  have hr : Public.RootsSized q := by exact prepD0_roots (p:=p) hp
  rw [Public.pub_getD,ReceiptPreparedFields.own_byte q overhead i hr hi]
  change Fp.ofNat (((u64 p.hdr.own).getD i 0).toNat)=_
  rw [(ReceiptPreparedFields.native_fields hp hk hd hc hm).2.2.1]

end ZkFormal.NearV3.Candidates.ReceiptPreparedFinalPublic

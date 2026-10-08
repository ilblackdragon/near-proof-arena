import ZkFormal.NearV3.Assembly.RcptRoutingComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def nativeRoutingIndex (k : WalkD0) (r : Receipt) : Nat :=
  (selectInterval k.L k.H.shardId r.receiverId).getD 0

def nativeRoutingInterval (k : WalkD0) (p : ReceiptPlan) : Option Bytes×Option Bytes :=
  (boundedIntervals k.L k.H.shardId).getD (nativeRoutingIndex k p.input.receipt) (none,none)

def nativeRoutingConstants (k : WalkD0) (fallback : ReceiptPlan→Nat→Fp) (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=q then Fp.ofNat (nativeRoutingIndex k p.input.receipt) else fallback p col

theorem native_routing_selected {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hw : decodeStateWitness bs=.ok w)
    (rp : ReceiptPlan) (hr : rp.input.receipt∈appliedReceipts k w) :
    nativeRoutingIndex k rp.input.receipt<128 ∧
    inInterval rp.input.receipt.receiverId (nativeRoutingInterval k rp)=true ∧
    (∀v∈(nativeRoutingInterval k rp).2.getD [],0<v.toNat) ∧
    ∀pos,pos≤rp.input.receipt.receiverId.length→
      routeKey (boundedPrep p k.L k.H.shardId).bnds (nativeRoutingIndex k rp.input.receipt) pos∈
        Public.boundaryRecords (boundedPrep p k.L k.H.shardId) := by
  obtain ⟨ix,hix,hlt,hiv,hkeys⟩ := applied_receipt_selection hp hk hw hr
  have he : nativeRoutingIndex k rp.input.receipt=ix := by simp only [nativeRoutingIndex,hix,Option.getD_some]
  refine ⟨by simpa only [he] using hlt,?_,?_,?_⟩
  · simpa only [nativeRoutingInterval,he,boundedPrep] using hiv
  · exact normalized_endpoint_positive hk (by simpa only [he] using (selectInterval_valid _ _ _ hix).1)
  · simpa only [he] using hkeys

theorem native_routing_plan {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hw : decodeStateWitness bs=.ok w)
    (lists : List (List Input)) (hls : lists.flatten.map Input.receipt=appliedReceipts k w) :
    (∀rp,rp.input∈lists.flatten→inInterval rp.input.receipt.receiverId (nativeRoutingInterval k rp)=true) ∧
    (∀rp,rp.input∈lists.flatten→∀v∈(nativeRoutingInterval k rp).2.getD [],0<v.toNat) := by
  have hh (rp : ReceiptPlan) (hr : rp.input∈lists.flatten) :=
    native_routing_selected hp hk hw rp (by rw [←hls];exact List.mem_map.mpr ⟨rp.input,hr,rfl⟩)
  exact ⟨fun rp hr=>(hh rp hr).2.1,fun rp hr=>(hh rp hr).2.2.1⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton

import ZkFormal.NearV3.Assembly.RoutingNativeSelection
import ZkFormal.NearV3.Assembly.RoutingPhysicalComplete

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Routing fields for one receiver byte or its end marker. The receiver's
comparison-state bits/inverses and all other receipt fields remain owned by the
full receipt renderer; this constructor makes no TableLocal claim by itself. -/
def routeColumns (bounds : List (Option Bytes×Option Bytes)) (idx pos : Nat)
    (base : Nat→Fp) (col : Nat) : Fp :=
  let iv := bounds.getD idx (none,none)
  if col=q then Fp.ofNat idx else
  if col=iB then Fp.ofNat pos else
  if col=loB then Fp.ofNat (((iv.1.getD []).getD pos 0).toNat) else
  if col=hiB then Fp.ofNat (((iv.2.getD []).getD pos 0).toNat) else
  if col=hnB then (if iv.2.isNone then 1 else 0) else base col

def routedColumnsTrace (bounds : List (Option Bytes×Option Bytes)) (idx pos : Nat)
    (base : Trace Fp) : Trace Fp :=
  ⟨base.log,fun t r=>routeColumns bounds idx pos (base.cell t r)⟩

theorem routeColumns_key (bounds : List (Option Bytes×Option Bytes)) (idx pos : Nat)
    (hi : idx<128) (hp : pos<65) (base : Trace Fp) (t r : Nat) :
    RoutingQCandidate.physicalBoundaryKey (routedColumnsTrace bounds idx pos base) t r=
      routeKey bounds idx pos := by
  have hx : 65*idx+pos<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;omega
  have hc : (65:Fp)*Fp.ofNat idx+Fp.ofNat pos=Fp.ofNat (65*idx+pos) := by
    change (65:Fp)*(idx: Fp)+(pos: Fp)=((65*idx+pos:Nat):Fp)
    grind
  have hb (b : UInt8) : (Fp.ofNat b.toNat).toNat=b.toNat := by
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have := b.toNat_lt
    unfold ZkFormal.Algebra.P;omega
  simp only [RoutingQCandidate.physicalBoundaryKey,routedColumnsTrace,routeColumns,
    q,iB,loB,hiB,hnB,ite_true,ite_false,show ¬(257=249) by decide,
    show ¬(253=249) by decide,show ¬(253=257) by decide,
    show ¬(254=249) by decide,show ¬(254=257) by decide,show ¬(254=253) by decide,
    show ¬(255=249) by decide,show ¬(255=257) by decide,show ¬(255=253) by decide,
    show ¬(255=254) by decide]
  rw [hc,Fp.toNat_ofNat,Nat.mod_eq_of_lt hx,hb,hb]
  dsimp only [routeKey]
  split <;> simp_all <;> rfl

/-- Physical key coverage of the actual generated routing fields, including the
end-marker position, for every receipt in the decoded native applied list. -/
theorem applied_receipt_columns {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} (hprep : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeStateWitness bs=.ok w) {receipt : Receipt}
    (hr : receipt∈appliedReceipts k w) :
    ∃idx,selectInterval k.L k.H.shardId receipt.receiverId=some idx ∧ idx<128 ∧
      ∀pos,pos≤receipt.receiverId.length → ∀base t r,
        RoutingQCandidate.physicalBoundaryKey
          (routedColumnsTrace (boundedPrep p k.L k.H.shardId).bnds idx pos base) t r∈
          Public.boundaryRecords (boundedPrep p k.L k.H.shardId) := by
  obtain ⟨idx,hsel,hidx,hiv,hkeys⟩ := applied_receipt_selection hprep hk hw hr
  have hlen : receipt.receiverId.length≤64 := by
    have h := appliedReceipts_wf hw receipt hr
    simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at h
    grind only
  refine ⟨idx,hsel,hidx,?_⟩
  intro pos hpos base t r
  rw [routeColumns_key _ idx pos hidx (by omega)]
  exact hkeys pos hpos

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout

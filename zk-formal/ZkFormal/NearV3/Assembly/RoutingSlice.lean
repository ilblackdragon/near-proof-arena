import ZkFormal.NearV3.Assembly.RoutingSpanQ

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

def routeSlice (acct : Bytes) (bounds : List (Option Bytes×Option Bytes)) (idx : Nat) : Trace Fp :=
  spanQPatch (routeSpan acct (bounds.getD idx (none,none)) 7) idx

theorem routeSlice_key (acct : Bytes) (bounds : List (Option Bytes×Option Bytes))
    (idx pos : Nat) (hq : idx<128) (hp : pos<65) (hlen : pos≤acct.length) :
    RoutingQCandidate.physicalBoundaryKey (routeSlice acct bounds idx) 0 pos=
      routeKey bounds idx pos := by
  rw [←routeColumns_key bounds idx pos hq hp (routeSlice acct bounds idx) 0 pos]
  simp only [RoutingQCandidate.physicalBoundaryKey,routeSlice,spanQPatch,routeSpan,if_pos hlen,
    routedColumnsTrace,routeColumns]
  rfl

/-- A coherent honest routing slice, including canonical q bits and exact physical
public-boundary keys. Other receipt groups and final trace placement remain open. -/
theorem applied_receipt_route_slice {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeStateWitness bs=.ok w) {r : Receipt} (hr : r∈appliedReceipts k w)
    (pub : List Fp) :
    ∃idx,selectInterval k.L k.H.shardId r.receiverId=some idx ∧ idx<128 ∧
      let tr := routeSlice r.receiverId (boundedPrep p k.L k.H.shardId).bnds idx
      ∀pos,pos≤r.receiverId.length →
        RoutingQCandidate.physicalBoundaryKey tr 0 pos∈
          Public.boundaryRecords (boundedPrep p k.L k.H.shardId) ∧
        (∀e∈cRoute,e.eval tr 0 pos pub=0) ∧
        RoutingQCandidate.qBound.eval tr 0 pos pub=0 ∧
        ∀j,j<7 → tr.cell 0 pos (xb (12+j))=0 ∨ tr.cell 0 pos (xb (12+j))=1 := by
  obtain ⟨idx,hs,hi,hrows⟩ := applied_receipt_route_span hp hk hw hr pub
  have hwf := appliedReceipts_wf hw r hr
  have hlen : r.receiverId.length≤64 := by
    simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hwf
    grind only
  refine ⟨idx,hs,hi,?_⟩
  dsimp only
  intro pos hpos
  have hrow := hrows pos hpos
  refine ⟨?_,?_,?_⟩
  · rw [routeSlice_key _ _ idx pos hi (by omega) hpos]
    exact hrow.1
  · exact spanQPatch_route _ idx 0 pos pub hrow.2
  · exact spanQPatch_bound _ idx 0 pos hi pub

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout

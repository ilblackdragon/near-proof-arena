import ZkFormal.NearV3.Assembly.RoutingPhysicalRanks
import ZkFormal.NearV3.Rcpt.Extract.V.BoundaryTrafficRows

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem counterPatch_boundary_row (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (users : Nat→Nat) (sd : Bool) :
    rowTraffic RcptV3.interactions (counterPatch tr t users) t r pub B_BND sd=
      if tr.cell t r gBd=1 then
        [(physicalBoundaryKey tr t r++[if sd then users r+1 else users r]).toFp] else [] := by
  have h0 : Fp.ofNat (users r)+0=Fp.ofNat (users r) := by grind
  have h1 : Fp.ofNat (users r)+1=Fp.ofNat (users r+1) := by
    change (users r : Fp)+1=((users r+1 : Nat) : Fp)
    grind
  rw [rowT_bnd]
  cases sd <;>
    simp [counterPatch,physicalBoundaryKey,Msg.toFp,gt,BND_STRIDE,
      q,iB,loB,hiB,hnB,uB,gBd,Fp.ofNat_toNat,h0,h1] <;> congr 3 <;> grind

def physicalCounterMessages (tr : Trace Fp) (t : Nat) (sd : Bool) : List Msg :=
  (List.range (tr.height t)).filterMap (fun r=>if tr.cell t r gBd=1 then
    some (physicalBoundaryKey tr t r++
      [if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r]) else none)

theorem physical_counter_messages (tr : Trace Fp) (t : Nat) (pub : List Fp) (sd : Bool) :
    ((List.range (tr.height t)).flatMap (fun r=>
      rowTraffic RcptV3.interactions (counterPatch tr t (physicalBoundaryRank tr t)) t r pub B_BND sd))=
      (physicalCounterMessages tr t sd).map Msg.toFp := by
  unfold physicalCounterMessages
  rw [List.map_filterMap]
  have gen : ∀rs : List Nat,
      rs.flatMap (fun r=>rowTraffic RcptV3.interactions
        (counterPatch tr t (physicalBoundaryRank tr t)) t r pub B_BND sd)=
      rs.filterMap (fun r=>(if tr.cell t r gBd=1 then
        some (physicalBoundaryKey tr t r++
          [if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r]) else none).map Msg.toFp) := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      rw [List.flatMap_cons,List.filterMap_cons,counterPatch_boundary_row,ih]
      split <;> simp
  exact gen _

theorem physical_counter_count (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (sd : Bool) (msg : List Fp) :
    tableBusCount RcptV3.interactions (counterPatch tr t (physicalBoundaryRank tr t)) t pub B_BND sd msg=
      ((physicalCounterMessages tr t sd).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (tr.height t)).flatMap _).count msg=_
  rw [physical_counter_messages]

end ZkFormal.NearV3.Assembly.RoutingQCandidate

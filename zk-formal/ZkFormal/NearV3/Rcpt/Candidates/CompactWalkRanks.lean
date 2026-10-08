import ZkFormal.NearV3.Rcpt.Candidates.CompactWalkPhysical
import ZkFormal.NearV3.Rcpt.Candidates.UpsJointTraffic
import ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

theorem compact_prefix_edges (p : List WStep3) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hR : compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub : List Fp) (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions (Candidates.CompactHeight.trace (physicalPrefixUps p Is))
      t pub B_EDGE sd msg=
      ((counterMessages (p.filterMap edgeKey) (walkEdgeKeys (upsWalkInventory Is)) sd).map Msg.toFp).count msg := by
  rw [compact_physical_walk_count _ hR t pub B_EDGE (Or.inl rfl) sd msg,
    actual_prefix_edges p Is ho hl sd,reduceMessages_toFp]

theorem compact_prefix_bitmaps (p : List WStep3) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I) (hR : compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub : List Fp) (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions (Candidates.CompactHeight.trace (physicalPrefixUps p Is))
      t pub B_BMAP sd msg=
      ((counterMessages (p.filterMap bitmapKey) (walkBmapKeys (upsWalkInventory Is)) sd).map Msg.toFp).count msg := by
  rw [compact_physical_walk_count _ hR t pub B_BMAP (Or.inr rfl) sd msg,
    actual_prefix_bitmaps p Is ho sd,reduceMessages_toFp]

/-- UPB ranking preserves the exact shared EDGE counter traffic on the actual
compact trace, so the two counter constructions use one physical witness. -/
theorem compact_patched_prefix_edges (p : List WStep3) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hR : compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub : List Fp)
    (hlocal : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t pub)
    (rank : Nat→Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions
      (patchWindowCounters (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t rank)
      t pub B_EDGE sd msg=
      ((counterMessages (p.filterMap edgeKey) (walkEdgeKeys (upsWalkInventory Is)) sd).map Msg.toFp).count msg := by
  rw [Candidates.WindowPatchOtherTraffic.count hlocal rank B_EDGE (by decide)]
  exact compact_prefix_edges p Is ho hl hR t pub sd msg

theorem compact_patched_prefix_bitmaps (p : List WStep3) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I) (hR : compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub : List Fp)
    (hlocal : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t pub)
    (rank : Nat→Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount compactTable.interactions
      (patchWindowCounters (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t rank)
      t pub B_BMAP sd msg=
      ((counterMessages (p.filterMap bitmapKey) (walkBmapKeys (upsWalkInventory Is)) sd).map Msg.toFp).count msg := by
  rw [Candidates.WindowPatchOtherTraffic.count hlocal rank B_BMAP (by decide)]
  exact compact_prefix_bitmaps p Is ho hR t pub sd msg

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

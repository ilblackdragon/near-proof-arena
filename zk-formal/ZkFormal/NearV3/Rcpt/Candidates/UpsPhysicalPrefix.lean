import ZkFormal.NearV3.Rcpt.Candidates.UpsPhysicalBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupJointInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows

/-- The physical shared EDGE/BMAP counter starts after all preceding consumers. -/
def physicalPrefixUps (p : List WStep3) (Is : List UpsInst) : List UpsInst :=
  (rankUpsList p Is).map syncUps

theorem physicalPrefixUps_instOk (p : List WStep3) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I) : ∀J∈physicalPrefixUps p Is,InstOk J := by
  intro J hJ
  obtain ⟨I,hI,rfl⟩:=List.mem_map.mp hJ
  exact syncUps_instOk I (rankUpsList_instOk Is p ho I hI)

theorem physicalPrefixUps_parts (p : List WStep3) (Is : List UpsInst)
    (ho : ∀I∈Is,NativePartFamily I) : ∀J∈physicalPrefixUps p Is,NativePartFamily J := by
  intro J hJ
  obtain ⟨I,hI,rfl⟩:=List.mem_map.mp hJ
  exact syncUps_parts I (rankUpsList_parts Is p ho I hI)

theorem actual_prefix_edges (p : List WStep3) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6) (sd : Bool) :
    upsWalkMessages (physicalPrefixUps p Is) B_EDGE sd=
      (counterMessages (p.filterMap edgeKey) (walkEdgeKeys (upsWalkInventory Is)) sd).map reduceMessage := by
  rw [physicalPrefixUps,synced_list_edges _ (rankUpsList_arity Is p hl),
    rankUpsList_flatten Is p ho,ranked_edge_traffic]
  simp only [walkEdgeKeys,walkBmapKeys,ups_inventory_flat,edgeKey,bitmapKey]
  rfl

theorem actual_prefix_bitmaps (p : List WStep3) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I) (sd : Bool) :
    upsWalkMessages (physicalPrefixUps p Is) B_BMAP sd=
      (counterMessages (p.filterMap bitmapKey) (walkBmapKeys (upsWalkInventory Is)) sd).map reduceMessage := by
  rw [physicalPrefixUps,synced_list_bitmaps,rankUpsList_flatten Is p ho,ranked_bitmap_traffic]
  simp only [walkEdgeKeys,walkBmapKeys,ups_inventory_flat,edgeKey,bitmapKey]
  rfl

theorem prefix_physical_edge_count (p : List WStep3) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hs : UpsShape (physicalPrefixUps p Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalPrefixUps p Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalPrefixUps p Is) r x:Int):Fp))
    (sd : Bool) (m : List Fp) :
    tableBusCount UpsV3.interactions tr t pub B_EDGE sd m=
      ((counterMessages (p.filterMap edgeKey) (walkEdgeKeys (upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [physical_walk_bus_count _ hs tr t pub hL hlog hcell B_EDGE (Or.inl rfl) sd m,
    actual_prefix_edges p Is ho hl sd,reduceMessages_toFp]

theorem prefix_physical_bitmap_count (p : List WStep3) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hs : UpsShape (physicalPrefixUps p Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalPrefixUps p Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalPrefixUps p Is) r x:Int):Fp))
    (sd : Bool) (m : List Fp) :
    tableBusCount UpsV3.interactions tr t pub B_BMAP sd m=
      ((counterMessages (p.filterMap bitmapKey) (walkBmapKeys (upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [physical_walk_bus_count _ hs tr t pub hL hlog hcell B_BMAP (Or.inr rfl) sd m,
    actual_prefix_bitmaps p Is ho sd,reduceMessages_toFp]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

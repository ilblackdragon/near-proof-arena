import ZkFormal.NearV3.Rcpt.Candidates.CompactMidrootPhysical
import ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

theorem prefix_midroot_records (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map (fun I=>[I.tau,I.rid]++I.mid)=Is.map (fun I=>[I.tau,I.rid]++I.mid) := by
  induction Is generalizing p with
  | nil=>rfl
  | cons I Is ih=>
    simpa only [physicalPrefixUps,rankUpsList,List.map_cons,syncUps,rankUps] using congrArg
      (List.cons ([I.tau,I.rid]++I.mid)) (ih (p++fourSteps I))

theorem prefix_mid_digests (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map UpsInst.mid=Is.map UpsInst.mid := by
  induction Is generalizing p with
  | nil=>rfl
  | cons I Is ih=>
    simpa only [physicalPrefixUps,rankUpsList,List.map_cons,syncUps,rankUps] using congrArg
      (List.cons I.mid) (ih (p++fourSteps I))

theorem compact_patched_midroot_recv (p : List WStep3) (Is : List UpsInst)
    (hl : ∀I∈Is,I.mid.length=32) (hR : compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub : List Fp)
    (hlocal : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t pub)
    (rank : Nat→Nat) (msg : List Fp) :
    tableBusCount compactTable.interactions
      (patchWindowCounters (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t rank)
      t pub B_MIDROOT false msg=
      ((Is.map (fun I=>[I.tau,I.rid]++I.mid)).map Msg.toFp).count msg := by
  have hmid : ∀I∈physicalPrefixUps p Is,I.mid.length=32 := by
    intro I hi
    have hm : I.mid∈(physicalPrefixUps p Is).map UpsInst.mid:=List.mem_map.mpr ⟨I,hi,rfl⟩
    rw [prefix_mid_digests] at hm
    obtain ⟨J,hJ,hmid⟩:=List.mem_map.mp hm
    rw [←hmid]
    exact hl J hJ
  rw [Candidates.WindowPatchOtherTraffic.count hlocal rank B_MIDROOT (by decide),
    compact_physical_midroot_recv _ hR hmid t pub msg,prefix_midroot_records]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

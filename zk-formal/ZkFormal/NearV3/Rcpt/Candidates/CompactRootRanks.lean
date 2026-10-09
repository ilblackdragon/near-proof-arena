import ZkFormal.NearV3.Rcpt.Candidates.CompactRootPhysical
import ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

theorem prefix_root_records (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map (fun I=>[I.tau+1]++I.post)=Is.map (fun I=>[I.tau+1]++I.post) := by
  induction Is generalizing p with
  | nil=>rfl
  | cons I Is ih=>
    simpa only [physicalPrefixUps,rankUpsList,List.map_cons,syncUps,rankUps] using congrArg
      (List.cons ([I.tau+1]++I.post)) (ih (p++fourSteps I))

theorem prefix_post_digests (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map UpsInst.post=Is.map UpsInst.post := by
  induction Is generalizing p with
  | nil=>rfl
  | cons I Is ih=>
    simpa only [physicalPrefixUps,rankUpsList,List.map_cons,syncUps,rankUps] using congrArg
      (List.cons I.post) (ih (p++fourSteps I))

theorem compact_patched_root_send (p : List WStep3) (Is : List UpsInst)
    (hl : ∀I∈Is,I.post.length=32) (hR : compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub : List Fp)
    (hlocal : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t pub)
    (rank : Nat→Nat) (msg : List Fp) :
    tableBusCount compactTable.interactions
      (patchWindowCounters (Candidates.CompactHeight.trace (physicalPrefixUps p Is)) t rank)
      t pub B_ROOT true msg=
      ((Is.map (fun I=>[I.tau+1]++I.post)).map Msg.toFp).count msg := by
  have hmid : ∀I∈physicalPrefixUps p Is,I.post.length=32 := by
    intro I hi
    have hm : I.post∈(physicalPrefixUps p Is).map UpsInst.post:=List.mem_map.mpr ⟨I,hi,rfl⟩
    rw [prefix_post_digests] at hm
    obtain ⟨J,hJ,hmid⟩:=List.mem_map.mp hm
    rw [←hmid]
    exact hl J hJ
  rw [Candidates.WindowPatchOtherTraffic.count hlocal rank B_ROOT (by decide),
    compact_physical_root_send _ hR hmid t pub msg,prefix_root_records]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

import ZkFormal.NearV3.Assembly.SourceSeeds
import ZkFormal.NearV3.Assembly.SourceShuffle
import ZkFormal.NearV3.Assembly.ExecutionViews
import ZkFormal.NearV3.Rcpt.Candidates.DictionaryCount

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

private theorem slotDescriptors_keys_length (b : Blk) (slots : List (ChunkSlot × ChunkInner)) :
    (Rcpt.Candidates.slotDescriptors b slots).length =
      (slots.filterMap fun (s,ci) => if s.heightIncluded == b.hdr.height then
        some (chunkHash s.inner ci.encodedMerkleRoot) else none).length := by
  induction slots with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨s,ci⟩
    simp only [Rcpt.Candidates.slotDescriptors, List.flatMap_cons, List.filterMap_cons]
    split <;> simp_all [Rcpt.Candidates.slotDescriptors]

theorem checkD0_sourceKeys_count {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    (distinctKeys w.entries).length = (sourceKeysV3 k).length := by
  rw [Rcpt.Candidates.checkD0_dictionary_count hk hw h]
  simp only [sourceKeysV3, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro b _
  exact slotDescriptors_keys_length b b.slots

def nativeExecutionViews (k : WalkD0) (w : StateWitness) (m : MainExecutionV3)
    (steps : List ImplicitStepV3) : ExtV3 :=
  executionViews k w m steps (sourceDictionarySeeds (sourceKeysV3 k) w.entries)

theorem nativeExecutionViews_entries {k w m steps bs}
    (hd : decodeStateWitness bs = .ok w) :
    (stateWitnessOfV3 k (nativeExecutionViews k w m steps)).entries = w.entries :=
  sourceDictionarySeeds_entries hd _

theorem checkD0a_source_semantics {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    SourceSemanticsV3 k (nativeExecutionViews k w m steps) := by
  have hr := (relD0a_iff B cb wb).mpr h
  have hd := hw
  unfold decodeW at hd
  obtain ⟨⟨bs,codes⟩,_,hd⟩ := ReexecV3D0.bind_ok' hd
  unfold checkD0a at h
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' h
  cases u
  have he := nativeExecutionViews_entries (k := k) (m := m) (steps := steps) hd
  constructor
  · exact sourceDictionarySeeds_selected hd (checkD0_sources_verified hk hw hc)
  · intro b hb
    have hs := checkD0_sources_shuffle hk hw hc b hb
    simpa only [nativeExecutionViews, executionViews, sourceDictionarySeeds_entries hd,
      selectedEntries] using hs
  · exact (sourceDictionarySeeds_entries hd _).symm ▸ checkD0_sourceKeys_count hk hw hc
  · rw [appliedReceipts_eq_flatMap]
    change k.sourceBlks.flatMap (blockApplied _ _ _) = _
    rw [he]
    rw [← appliedReceipts_eq_flatMap]
    exact (executionViews_applied hd).symm
  · have ha := hr.2.2.1
    simp only [a2, hk, hw, List.all_eq_true, beq_iff_eq] at ha
    simpa only [usedProofs, he] using ha

end ZkFormal.NearV3.Assembly

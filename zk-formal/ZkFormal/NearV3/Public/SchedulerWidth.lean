import ZkFormal.NearV3.Public.Prepared

/-! Fixed payload widths follow from the scheduler's actual public renderer. -/
namespace ZkFormal.NearV3.Public
open Sched

private theorem key_width (tau : Nat) (seed : ByteString) :
    ∀ row ∈ keyRecs tau seed, row.length = 7 := by
  intro row hr; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr; rfl
private theorem ash_width (tau : Nat) (ash : ByteString) :
    ∀ row ∈ ashRecs tau ash, row.length = 7 := by
  intro row hr; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr; rfl
private theorem fwd_width (P : InstPub) (fwd : List (Nat × Nat)) :
    ∀ row ∈ fwdRecs P fwd, row.length = 7 := by
  intro row hr; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr; rfl
private theorem raw_width (tau : Nat) (P : InstPub) :
    ∀ row ∈ rawRecs tau P, row.length = 11 := by
  intro row hr; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
  simp [b2]
private theorem shard_width (tau : Nat) (P : InstPub) :
    ∀ row ∈ shardRecs tau P, row.length = 11 := by
  intro row hr
  obtain ⟨side,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
  rfl
private theorem link_width (tau : Nat) (P : InstPub) :
    ∀ row ∈ linkRecs tau P, row.length = 11 := by
  intro row hr; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
  simp [srcFields,b2]

theorem dl_width (tau : Nat) (ids : List Nat) :
    ∀ row ∈ dlRecs tau ids, row.length = 5 := by
  intro row hr
  obtain ⟨k,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨o,_,rfl⟩ := List.mem_map.mp hr
  rfl

theorem render_pubb_width (Ps : List InstPub) (fwd : List (Nat × Nat)) :
    ∀ row ∈ (render Ps fwd).pubb, row.length = 7 := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨tau,_,hr⟩ := List.mem_flatMap.mp hr
    rcases List.mem_append.mp hr with hr | hr
    · exact key_width _ _ row hr
    · exact ash_width _ _ row hr
  · exact fwd_width _ _ row hr

theorem render_par_width (Ps : List InstPub) (fwd : List (Nat × Nat)) :
    ∀ row ∈ (render Ps fwd).par, row.length = 11 := by
  intro row hr
  obtain ⟨tau,_,hr⟩ := List.mem_flatMap.mp hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · obtain rfl := List.mem_singleton.mp hr; rfl
        · split at hr
          · simp at hr
          · obtain rfl := List.mem_singleton.mp hr; rfl
      · exact raw_width _ _ row hr
    · exact shard_width _ _ row hr
  · exact link_width _ _ row hr

end ZkFormal.NearV3.Public

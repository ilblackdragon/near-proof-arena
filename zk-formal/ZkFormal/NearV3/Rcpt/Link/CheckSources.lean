import ZkFormal.NearV3.Rcpt.Link.WitnessSources
import NearSpecV3.ChunkValidationV0a

namespace ZkFormal.NearV3
open NearSpec NearSpecV3 Sched

/-- A successful real validator check supplies the decoded witness and all selected source
path guarantees, without a separately assumed decoder oracle. -/
theorem checkD0_source_paths {cb wb : Bytes} (h : checkD0 cb wb = .ok ()) :
    ∃ raw codes w,
      decodeWitnessFile wb = .ok (raw, codes) ∧
      decodeStateWitness raw = .ok w ∧
      lenT raw ≤ 8388608 ∧
      (∀ key e, lookupLast key w.entries = some e →
        ∀ step ∈ e.proof.path, step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1)) := by
  unfold checkD0 at h
  obtain ⟨c, hc, h⟩ := bind_ok h
  obtain ⟨⟨raw, codes⟩, hf, h⟩ := bind_ok h
  obtain ⟨_, hcodes, h⟩ := bind_ok h
  obtain ⟨_, hsize, h⟩ := bind_ok h
  obtain ⟨w, hw, h⟩ := bind_ok h
  refine ⟨raw, codes, w, hf, hw, ?_, ?_⟩
  · have hh := check_ok hsize
    simpa using hh
  · intro key e he
    exact lookupLast_path_shape hw he

/-- D0a retains the same concrete source witness and decoding guarantees. -/
theorem relD0a_source_paths {B : Nat} {cb wb : Bytes} (h : RelD0a B cb wb) :
    ∃ raw codes w,
      decodeWitnessFile wb = .ok (raw, codes) ∧
      decodeStateWitness raw = .ok w ∧
      lenT raw ≤ 8388608 ∧
      (∀ key e, lookupLast key w.entries = some e →
        ∀ step ∈ e.proof.path, step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1)) := by
  apply checkD0_source_paths
  have hh := h.1
  unfold RelD0 acceptsD0 at hh
  cases hc : checkD0 cb wb with
  | error e => simp [hc] at hh
  | ok u => cases u; rfl

end ZkFormal.NearV3

import ZkFormal.NearV3.Rcpt.Link.ProofDecode

namespace ZkFormal.NearV3
open NearSpec NearSpecV3 Sched

/-- All source proofs in a successfully decoded real witness have valid path windows. -/
theorem decodeStateWitness_path_shape {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) :
    ∀ e ∈ w.entries, ∀ step ∈ e.proof.path,
      step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1) := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact pVec_pred pEntry
      (fun e => ∀ step ∈ e.proof.path, step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1))
      (fun _ _ _ hh => pEntry_path_shape hh) (by assumption)

/-- Last-wins lookup selects an entry that really occurred in the decoded witness. -/
theorem lookupLast_mem {key : Bytes} {entries : List ProofEntry} {e : ProofEntry}
    (h : lookupLast key entries = some e) : e ∈ entries := by
  induction entries with
  | nil => simp [lookupLast] at h
  | cons a rest ih =>
    simp only [lookupLast] at h
    split at h
    · rename_i v hv
      cases h
      exact List.mem_cons_of_mem a (ih hv)
    · split at h
      · cases h; exact List.mem_cons_self
      · cases h

/-- Selected proof entries inherit the concrete decoder guarantees needed by the renderer. -/
theorem lookupLast_path_shape {bs : Bytes} {w : StateWitness} (hw : decodeStateWitness bs = .ok w)
    {key : Bytes} {e : ProofEntry} (he : lookupLast key w.entries = some e) :
    ∀ step ∈ e.proof.path, step.1.length = 32 ∧ (step.2 = 0 ∨ step.2 = 1) :=
  decodeStateWitness_path_shape hw e (lookupLast_mem he)

end ZkFormal.NearV3

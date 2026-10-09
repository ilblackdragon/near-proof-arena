import ZkFormal.NearV3.Rcpt.Candidates.PreparedNonempty
import ZkFormal.NearV3.Assembly.SourceComplete

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched Assembly

private theorem checkedSourceBlock_trace (entries : List ProofEntry) (own : Nat) (L : Layout)
    (b : Blk) (acc : List Receipt × Nat) {step : ForInStep (List Receipt × Nat)}
    (h : checkedSourceBlock entries own L b acc = .ok step) :
    (∃ next, step = .yield next) ∧
      ((∀ x ∈ b.slots, SourceSlotValid entries own b x) →
        ∃ shuffled, shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled) := by
  unfold checkedSourceBlock at h
  obtain ⟨out, ho, h⟩ := bind_ok h
  split at h
  · rename_i shuffled hs
    obtain ⟨_, he, h⟩ := bind_ok h
    cases he
    cases h
    refine ⟨⟨_, rfl⟩, ?_⟩
    intro hv
    have hh := checkedSourceSlots_complete entries own b b.slots hv acc.2 []
    rw [ho] at hh
    have hl := congrArg Prod.snd (Except.ok.inj hh)
    refine ⟨shuffled, ?_⟩
    simpa only [hl, List.nil_append] using hs
  · obtain ⟨_, he, _⟩ := bind_ok h
    cases he

/-- Successful validation counts source occurrences, including repeated keys. -/
theorem checkedSourceLoop_count (entries : List ProofEntry) (own : Nat) (L : Layout)
    (blocks : List Blk) {out : List Receipt × Nat}
    (h : forIn blocks ([], 0) (checkedSourceBlock entries own L) = .ok out) :
    out.2 = (blocks.map fun B => (slotDescriptors B B.slots).length).sum := by
  have hv := checkedSourceLoop_valid entries own L blocks h
  have hs := forIn_all_yield _ _ (checkedSourceBlock_trace entries own L) blocks ([], 0) out h
  have hc := checkedSourceLoop_complete entries own L blocks hv
    (fun b hb => hs b hb (hv b hb)) ([], 0)
  rw [h] at hc
  have he := congrArg Prod.snd (Except.ok.inj hc)
  simp only [Nat.zero_add] at he
  rw [he]
  congr 1
  apply List.map_congr_left
  intro B hB
  have hh := congrArg List.length (slotDescriptors_selected entries own B B.slots (hv B hB))
  simp only [List.length_map] at hh
  have heq : selectedEntries entries B B.slots = selectedProofs entries B B.slots := by
    unfold selectedEntries selectedProofs
    congr 1
  rw [heq]
  exact hh.symm

set_option maxHeartbeats 4000000 in
/-- The native dictionary guard counts distinct encoded keys against all source
occurrences. It does not assert that selected source keys are distinct. -/
theorem checkD0_dictionary_count {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    (distinctKeys w.entries).length =
      (k.sourceBlks.map fun B => (slotDescriptors B B.slots).length).sum := by
  unfold walkD0 at hk
  repeat' (first
    | (have hh := hk; clear hk; obtain ⟨_, _, hk⟩ := bind_ok hh; clear hh)
    | (split at hk)
    | (dsimp only at hk))
  all_goals try (cases hk; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    unfold decodeW at hw
    obtain ⟨⟨raw, codes⟩, hfile, hw⟩ := bind_ok hw
    unfold checkD0 at h
    repeat' (first
      | (have hh := h; clear h; obtain ⟨_, _, h⟩ := bind_ok hh; clear hh)
      | (split at h)
      | (dsimp only at h))
    all_goals try (cases h; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp_all only [Except.mapError, Except.ok.injEq, Prod.mk.injEq, pure, Except.pure, Option.some.injEq]
      have hv := checkedSourceLoop_count _ _ _ _ (by assumption)
      have hn := check_ok (by assumption : check ((distinctKeys _).length == _) _ = .ok _)
      simp only [beq_iff_eq] at hn
      grind only

/-- Exact cardinality relation retained by real preparation. Unused dictionary
entries remain permitted when source keys repeat. -/
theorem prepD0_dictionary_count {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {hint : Hint} {p : Prep} (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (hc : checkD0 cb wb = .ok ()) (hp : prepD0 cb hint = .ok p) :
    (distinctKeys w.entries).length = p.lists.length := by
  rw [checkD0_dictionary_count hk hw hc,
    preparedSourceLists_length k.sourceBlks (prepD0_source_lists hp hk)]

theorem distinctKeys_length_le (entries : List ProofEntry) :
    (distinctKeys entries).length ≤ entries.length := by
  induction entries with
  | nil => simp [distinctKeys]
  | cons e es ih =>
    simp only [distinctKeys, List.length_cons]
    split <;> (try simp only [List.length_cons]) <;> omega

/-- Native dictionary cardinality provides room for every source occurrence,
including the empty repeated-proof headers charged by the candidate renderer. -/
theorem prepD0_sources_le_entries {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {hint : Hint} {p : Prep} (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (hc : checkD0 cb wb = .ok ()) (hp : prepD0 cb hint = .ok p) :
    p.lists.length ≤ w.entries.length := by
  rw [← prepD0_dictionary_count hk hw hc hp]
  exact distinctKeys_length_le _

end ZkFormal.NearV3.Rcpt.Candidates

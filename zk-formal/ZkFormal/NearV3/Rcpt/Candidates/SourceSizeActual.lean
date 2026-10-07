import ZkFormal.NearV3.Rcpt.Candidates.DedupSizeBound

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3

/-- Honest deduplicated source SIZE fits the actual unchanged raw witness budget.
Repeated empty headers are paid by encoded dictionary overhead, whose native
cardinality counts occurrences rather than unique selected source keys. -/
theorem relD0a_size_bound {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    DedupRender.size (blocks p.lists w.entries) ≤ witnessBytes := by
  obtain ⟨hb, _, hs⟩ := relD0a_inputs h hp hf hw
  have hl : ∀ j, j < p.lists.length → lookupLast (p.lists.getD j ⟨[],0,[]⟩).key w.entries =
      some (entryAt p.lists w.entries j) :=
    fun j hj => entryAt_lookup p.lists w.entries (hs j hj)
  have hn := firstSourceEntries_keys_nodup p.lists w.entries (entryAt p.lists w.entries) hl
  have hc := raw_computed_size_charge hw (firstSourceEntries p.lists (entryAt p.lists w.entries)) hn (by
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hh := hl j (firstSourceIndices_lt p.lists hj)
    rw [lookupLast_key hh]
    exact hh)
  have hz := size_le_computed p.lists w.entries (by
    intro j hj hd
    exact relD0a_repeated_L12 h hp hf hw hj (sourceDup_repeated p.lists hj hd))
  obtain ⟨k, sw, hk, hsw, _, _⟩ := relD0a_sources_verified h
  have hd : decodeW wb = .ok w := by simp [decodeW, hf, hw, bind, Except.bind]
  have hncheck : checkD0 cb wb = .ok () := by
    have hh := h.1
    unfold RelD0 acceptsD0 at hh
    cases he : checkD0 cb wb with
    | error err => simp [he] at hh
    | ok u => cases u; rfl
  have he := prepD0_sources_le_entries hk hd hncheck hp
  rw [lenT_eq_length] at hb
  omega

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile

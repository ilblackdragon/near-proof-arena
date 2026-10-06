import ZkFormal.NearV3.Sched.Link.CodecSV
import ZkFormal.NearV3.Sched.Link.MemSend

/-!
# `ParSmall` from `PubIdx`

If the public `SPAR` sends are `render`'s `par` records, then every raw-request record has
`τ < 256` and `s, r < 64`, and every scan-parameter record has `n ≤ 64`. The per-instance
facts come from `prepD0_rawOk` and `SchedPubOk` (`n ≤ 64`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

theorem parSmall_of_idx {AP : AirP} {pub : List Fp} (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256)
    (hP : ∀ τ, τ < Ps.length → RawOk (Ps.getD τ instD) ∧ (Ps.getD τ instD).n ≤ 64) :
    ParSmall AP pub := by
  have mem : ∀ M : List Fp, 1 ≤ pubCount AP pub B_SPAR true M →
      ∃ τ, τ < Ps.length ∧ ∃ r ∈ parBlock τ (Ps.getD τ instD), r.map Fp.ofNat = M := by
    intro M hM
    rw [I.count, hrec] at hM
    obtain ⟨r, hr, e⟩ := List.mem_map.1 (List.count_pos_iff.1 hM)
    rw [render_par, List.mem_flatMap] at hr
    obtain ⟨τ, hτ, hr⟩ := hr
    exact ⟨τ, List.mem_range.1 hτ, r, hr, e⟩
  have u : ∀ a : Nat, a < 2013265921 → (Fp.ofNat a).toNat = a := fun a h => toNat_ofNat_lt' h
  have tagne : ∀ (r : List Nat) (a b : Nat), r[1]? = some a → a < 8 → b < 8 → a ≠ b →
      (r.map Fp.ofNat)[1]? ≠ some (Fp.ofNat b) := by
    intro r a b hr ha hb hab e
    rw [List.getElem?_map, hr] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact hab (ofNat_inj' (by omega) (by omega) e)
  refine ⟨fun M hM ht => ?_, fun M hM ht => ?_⟩
  · obtain ⟨τ, hτ, r, hr, rfl⟩ := mem M hM
    obtain ⟨RO, hn⟩ := hP τ hτ
    rw [parBlock_split, List.mem_append] at hr
    rcases hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact absurd ht (tagne _ 0 PT_RAW (by simp [parCodec]) (by decide) (by decide) (by decide))
    simp only [parRest, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · split at hr
      · simp at hr
      · simp only [List.mem_singleton] at hr; subst hr
        exact absurd ht (tagne _ 1 PT_RAW (by simp [parScan, PT_SCAN]) (by decide) (by decide) (by decide))
    · simp only [rawRecs, List.mem_map] at hr
      obtain ⟨⟨q, c⟩, hqc, rfl⟩ := hr
      have hq : q ∈ (Ps.getD τ instD).raw := (List.of_mem_zip hqc).1
      obtain ⟨hs, hr', -⟩ := RO.raw q hq
      simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.map_map, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, b2]
      simp only [List.getElem?_append_right, List.length_map, List.length_range, Function.comp_def]
      refine ⟨by rw [u _ (by omega)]; omega, ?_, ?_⟩
      · simp [List.getElem?_append_right, u _ (show q.s < 2013265921 by omega)]
        omega
      · simp [List.getElem?_append_right, u _ (show q.r < 2013265921 by omega)]
        omega
    · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨side, -, x, -, rfl⟩ := hr
      exact absurd ht (tagne _ 3 PT_RAW (by simp [PT_SHD]) (by decide) (by decide) (by decide))
    · simp only [linkRecs, List.mem_map] at hr
      obtain ⟨l, -, rfl⟩ := hr
      exact absurd ht (tagne _ 4 PT_RAW (by simp [PT_LINK]) (by decide) (by decide) (by decide))
  · obtain ⟨τ, hτ, r, hr, rfl⟩ := mem M hM
    obtain ⟨-, hn⟩ := hP τ hτ
    rw [parBlock_split, List.mem_append] at hr
    rcases hr with hr | hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact absurd ht (tagne _ 0 PT_SCAN (by simp [parCodec]) (by decide) (by decide) (by decide))
    simp only [parRest, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · split at hr
      · simp at hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp [parScan, b3]
        have hn' := hn
        simp only [List.getD_eq_getElem?_getD] at hn'
        exact Nat.le_trans (Nat.mod_le _ _) hn'
    · simp only [rawRecs, List.mem_map] at hr
      obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
      exact absurd ht (tagne _ 2 PT_SCAN (by simp [PT_RAW]) (by decide) (by decide) (by decide))
    · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨side, -, x, -, rfl⟩ := hr
      exact absurd ht (tagne _ 3 PT_SCAN (by simp [PT_SHD]) (by decide) (by decide) (by decide))
    · simp only [linkRecs, List.mem_map] at hr
      obtain ⟨l, -, rfl⟩ := hr
      exact absurd ht (tagne _ 4 PT_SCAN (by simp [PT_LINK]) (by decide) (by decide) (by decide))

end ZkFormal.NearV3.Sched

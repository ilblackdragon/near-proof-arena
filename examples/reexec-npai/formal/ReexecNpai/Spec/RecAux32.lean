import ReexecNpai.Spec.RecAux31

/-!
# Record parse: one record (`pRecord; LTU 4 10 9`)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m : M}

theorem rec_wp (h : ParseInv cb pb rs R N o A K S m) (hlt : o < pb.length) :
    wp P (Inp pub cb pb) (.seq pRecord (LTU 4 10 9)) m (RecPost cb pb rs R N o A) := by
  have hpl := h.st.plen
  simp only [PMAX] at hpl
  rw [wp_seq, pRecord_split, rec_wp_seqs_append _ _ (by simp [recPre]) (by simp)]
  refine wp_mono (recPre_wp (q := PF + o) h.st.k1 h.st.k8 h.rP (by simp only [PF] at *; omega)) ?_
  rintro m1 ⟨hcap, hm1, h10, h0, h1, fr⟩
  rw [h.re] at hcap
  have hs := RecStart.mk' h hlt hcap hm1 h10 h0 fr
  have hk0 := hs.r0
  have hkl : u8At pb o < 256 := u8At_lt pb o
  have hb : (m.mem (PF + o)).toNat = u8At pb o := byteProof h.st.proof hlt
  rw [hb] at h1
  simp only [seqs, wp_seq]
  rw [wp_ite]
  refine ⟨fun h1z => ?_, fun h1nz => ?_⟩
  · have hk12 : ¬ (u8At pb o = 1 ∨ u8At pb o = 2) := by intro hc; rw [h1, if_pos hc] at h1z; simp at h1z
    rw [rec_wp_seqs_append _ _ (by simp [recExtL]) (by simp)]
    refine wp_of_spec (recExt_twp hs.k1 hs.k8 hk0) ?_
    rintro m1' c ⟨hm', hr1, hfr', -⟩
    have hs' := hs.mono hm' (fun j h1 _ => hfr' j h1)
    simp only [seqs]
    rw [wp_ite]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · rw [rec_wp_seqs_append _ _ (by simp [recBrL]) (by simp)]
      refine wp_mono (recBr_wp hs'.k1 hs'.k8 hs'.r0 hkl) ?_
      rintro m1'' ⟨hk, hm'', hfr''⟩
      have hs'' := hs'.mono hm'' hfr''
      simp only [seqs]
      exact wp_mono (br_body_wp hs'' hk) (fun m2 hb => push_wp hb (fun _ h => h))
    · have hk3 : u8At pb o = 3 := by
        rw [hr1] at hnz; by_cases hc : u8At pb o = 3
        · exact hc
        · simp [hc] at hnz
      exact wp_mono (ext_body_wp hs' hk3) (fun m2 hb => push_wp hb (fun _ h => h))
  · have hk12 : u8At pb o = 1 ∨ u8At pb o = 2 := by
      rw [h1] at h1nz; by_cases hc : u8At pb o = 1 ∨ u8At pb o = 2
      · exact hc
      · simp only [hc, ↓reduceIte] at h1nz; exact absurd rfl h1nz
    have hk : u8At pb o = if decide (u8At pb o = 1) then 1 else 2 := by
      by_cases h1' : u8At pb o = 1 <;> simp [h1'] <;> omega
    exact wp_mono (leaf_body_wp hs hk) (fun m2 hb => push_wp hb (fun _ h => h))

theorem rec_twp (h : ParseInv cb pb rs R N o A K S m) (hlt : o < pb.length) (hcap : A.length < NCAP)
    {stk' : List PTrie} {o' : Nat}
    (hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) = some (stk', pb.drop o'))
    (ho' : o' ≤ pb.length) :
    twp P (Inp pub cb pb) (.seq pRecord (LTU 4 10 9)) m (fun m' c =>
      RecPostT cb pb rs R N o' A m' ∧ c ≤ 80 * (o' - o)) := by
  have hpl := h.st.plen
  simp only [PMAX] at hpl
  -- the kind
  have hkind : u8At pb o = 1 ∨ u8At pb o = 2 ∨ u8At pb o = 3 ∨ u8At pb o = 4 ∨ u8At pb o = 5 ∨
      u8At pb o = 6 := by
    have hd' := hd
    rw [decRec_pos] at hd'
    unfold recPos at hd'
    rw [if_pos (by omega)] at hd'
    by_cases c1 : u8At pb o = 1; · exact Or.inl c1
    by_cases c2 : u8At pb o = 2; · exact Or.inr (Or.inl c2)
    by_cases c3 : u8At pb o = 3; · exact Or.inr (Or.inr (Or.inl c3))
    by_cases c4 : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6
    · exact Or.inr (Or.inr (Or.inr c4))
    · rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4] at hd'; simp at hd'
  rw [twp_seq, pRecord_split, rec_twp_seqs_append _ _ (by simp [recPre]) (by simp)]
  refine twp_mono (recPre_twp (q := PF + o) h.st.k1 h.st.k8 h.rP (by simp only [PF] at *; omega)
    (by rw [h.re]; exact hcap)) ?_
  rintro m1 c1 ⟨hm1, h10, h0, h1, fr, hc1⟩
  have hs := RecStart.mk' h hlt hcap hm1 h10 h0 fr
  have hk0 := hs.r0
  have hb : (m.mem (PF + o)).toNat = u8At pb o := byteProof h.st.proof hlt
  rw [hb] at h1
  simp only [seqs, twp_seq]
  by_cases hk12 : u8At pb o = 1 ∨ u8At pb o = 2
  · refine twp_ite_ne (by rw [h1, if_pos hk12]; decide) ?_
    have hk : u8At pb o = if decide (u8At pb o = 1) then 1 else 2 := by
      by_cases h1' : u8At pb o = 1 <;> simp [h1'] <;> omega
    refine twp_mono (leaf_body_twp hs hk hd ho') ?_
    intro m2 c2 hb2
    refine twp_mono (push_twp hb2 (Q := fun m4 c => RecPostT cb pb rs R N o' A m4 ∧
      c1 + ((c2 + c) + 2) ≤ 80 * (o' - o)) (fun m4 hX hp => ⟨hp, by omega⟩)) ?_
    intro m3 c3 h3
    refine twp_mono h3 ?_
    intro m4 c4 h4
    exact ⟨h4.1, by have := h4.2; omega⟩
  · refine twp_ite_zero (by rw [h1, if_neg hk12]) ?_
    rw [rec_twp_seqs_append _ _ (by simp [recExtL]) (by simp)]
    refine twp_mono (recExt_twp hs.k1 hs.k8 hk0) ?_
    rintro m1' ce ⟨hm', hr1, hfr', hce⟩
    have hs' := hs.mono hm' (fun j h1 _ => hfr' j h1)
    simp only [seqs]
    by_cases hk3 : u8At pb o = 3
    · refine twp_ite_ne (by rw [hr1, if_pos hk3]; decide) ?_
      refine twp_mono (ext_body_twp hs' hk3 hd ho') ?_
      intro m2 c2 hb2
      refine twp_mono (push_twp hb2 (Q := fun m4 c => RecPostT cb pb rs R N o' A m4 ∧
        c1 + (ce + (c2 + 2) + c + 1) ≤ 80 * (o' - o)) (fun m4 hX hp => ⟨hp, by omega⟩)) ?_
      intro m3 c3 h3
      refine twp_mono h3 ?_
      intro m4 c4 h4
      exact ⟨h4.1, by have := h4.2; omega⟩
    · refine twp_ite_zero (by rw [hr1, if_neg hk3]) ?_
      have hk : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6 := by omega
      rw [rec_twp_seqs_append _ _ (by simp [recBrL]) (by simp)]
      refine twp_mono (recBr_twp hs'.k1 hs'.k8 hs'.r0 hk) ?_
      rintro m1'' cr ⟨hm'', hfr'', hcr⟩
      have hs'' := hs'.mono hm'' hfr''
      simp only [seqs]
      refine twp_mono (br_body_twp hs'' hk hd ho') ?_
      intro m2 c2 hb2
      refine twp_mono (push_twp hb2 (Q := fun m4 c => RecPostT cb pb rs R N o' A m4 ∧
        c1 + (ce + (cr + c2 + 1) + c + 1) ≤ 80 * (o' - o)) (fun m4 hX hp => ⟨hp, by omega⟩)) ?_
      intro m3 c3 h3
      refine twp_mono h3 ?_
      intro m4 c4 h4
      exact ⟨h4.1, by have := h4.2; omega⟩

end

end ReexecNpai

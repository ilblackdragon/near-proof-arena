import ReexecNpai.Spec.RecAux13
import ReexecNpai.Spec.RecAux10

/-!
# Record parse: extension checks ↔ positional facts
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pb : Bytes} {o : Nat}

theorem extFacts_of_chk {m1 m2 : M} (hpf1 : readMem m1.mem PF pb.length = pb)
    (hpf2 : readMem m2.mem PF pb.length = pb)
    (c1 : ExtChk1 m1 (PF + o + 1) (PF + pb.length)) (c3 : ExtChk3 m2 (PF + o + 2) (PF + pb.length))
    (hz : u8At pb (o + 1) = 1 → sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32) :
    ExtFacts pb o ∧ (m1.mem (PF + o + 1)).toNat = u8At pb (o + 1) ∧
      rd32 m2 (PF + o + 2 + 1) = leAt pb (o + 3) 4 ∧ (m2.mem (PF + o + 2 + 5)).toNat = u8At pb (o + 7) := by
  obtain ⟨a1, a2, a3, a4⟩ := c1
  obtain ⟨b1, b2, b3⟩ := c3
  have hF := byte_at hpf1 (show PF + o + 1 = PF + (o + 1) by omega) (by omega)
  have hT := byte_at hpf1 (show PF + o + 1 + 1 = PF + (o + 2) by omega) (by omega)
  have hH := rd_at hpf2 rfl (show PF + o + 2 + 1 = PF + (o + 3) by omega) (by omega)
  have hP := byte_at hpf2 (show PF + o + 2 + 5 = PF + (o + 7) by omega) (by omega)
  rw [hF] at a2; rw [hT] at a4; rw [hH] at b1 b2; rw [hP] at b3
  exact ⟨⟨a2, a4, b1, by omega, b3, hz⟩, hF, hH, hP⟩

theorem chk_of_extFacts {m1 m2 : M} (hpf1 : readMem m1.mem PF pb.length = pb)
    (hpf2 : readMem m2.mem PF pb.length = pb) (hf : ExtFacts pb o) :
    ExtChk1 m1 (PF + o + 1) (PF + pb.length) ∧ ExtChk3 m2 (PF + o + 2) (PF + pb.length) ∧
      (m1.mem (PF + o + 1)).toNat = u8At pb (o + 1) ∧
      rd32 m2 (PF + o + 2 + 1) = leAt pb (o + 3) 4 ∧ (m2.mem (PF + o + 2 + 5)).toNat = u8At pb (o + 7) := by
  obtain ⟨fl, tag, hl1, hend, hp0, -⟩ := hf
  have hF := byte_at hpf1 (show PF + o + 1 = PF + (o + 1) by omega) (by omega)
  have hT := byte_at hpf1 (show PF + o + 1 + 1 = PF + (o + 2) by omega) (by omega)
  have hH := rd_at hpf2 rfl (show PF + o + 2 + 1 = PF + (o + 3) by omega) (by omega)
  have hP := byte_at hpf2 (show PF + o + 2 + 5 = PF + (o + 7) by omega) (by omega)
  refine ⟨⟨by omega, by rw [hF]; exact fl, by omega, by rw [hT]; exact tag⟩,
    ⟨by rw [hH]; exact hl1, by rw [hH]; omega, by rw [hP]; exact hp0⟩, hF, hH, hP⟩

/-- The zero check of a revealed child's hash slot. -/
theorem extZero_iff {m3 : M} (hpf : readMem m3.mem PF pb.length = pb) (hd : readMem m3.mem 0 168 = dataSeg)
    (hend : o + leAt pb (o + 3) 4 + 47 ≤ pb.length) :
    readMem m3.mem (leAt pb (o + 3) 4 + 5 + (PF + o + 2)) 32 = readMem m3.mem 136 32 ↔
      sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32 := by
  rw [rm_at hpf (show leAt pb (o + 3) 4 + 5 + (PF + o + 2) = PF + (o + 7 + leAt pb (o + 3) 4) by omega)
    (by omega), dZero hd]

end

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m : M}

/-- The last write (`res`) and the arena step of an extension. -/
theorem ext_fin (h : ParseInv cb pb rs R N o A K S m) (hcap : A.length < NCAP)
    (hk : u8At pb o = 3) (hf : ExtFacts pb o) {key : List Nat}
    (hkey : keyOfHP false (sl pb (o + 7) (leAt pb (o + 3) 4)) = some key)
    {S0 T : List Nat} {A1 : List Ent} (hS : S = S0 ++ T)
    (hT1 : u8At pb (o + 1) = 1 → T.length = 1) (hT0 : u8At pb (o + 1) ≠ 1 → T = [])
    {m4 : M}
    (hp : PopRel A T (childSlot (extE pb o key (rdm m.mem (AR + 24 * A.length + 8)) A K T)) A1 T.length)
    (hpm : PopMem m4 A A1 K T T.length S0)
    (e0 : rd32 m4 (AR + 24 * A.length) = PF + o + 2)
    (e4 : rd32 m4 (AR + 24 * A.length + 4) = leAt pb (o + 3) 4 + 45)
    (e8 : rd32 m4 (AR + 24 * A.length + 8) = rdm m.mem (AR + 24 * A.length + 8))
    (e12 : rd32 m4 (AR + 24 * A.length + 12) = K.length)
    (e20 : rd32 m4 (AR + 24 * A.length + 20) = 0)
    (hkc : rd32 m4 C_KC = K.length + T.length) (hhdr : rd32 m4 C_NODES = N)
    (hfr : MFrame m.mem m4.mem) (h14 : m4.regs 14 = 8) (h15 : m4.regs 15 = 1)
    (h2 : m4.regs 2 = extResv pb o key A T)
    (h10 : m4.regs 10 = PF + (o + leAt pb (o + 3) 4 + 47)) (h9 : m4.regs 9 = PF + pb.length)
    (h8 : m4.regs 8 = A.length) (h7 : m4.regs 7 = S0.length)
    (h5 : m4.regs 5 = revSum pb A + (leAt pb (o + 3) 4 + 45)) :
    twp P (Inp pub cb pb) (wField 16 2) m4 (fun m5 c =>
      BodyPostT cb pb rs R N o (o + leAt pb (o + 3) 4 + 47) A m5 (c + 1000)) := by
  have hkl := h.klen
  have hcap' := hcap
  simp only [NCAP] at hcap'
  have hres32 : extResv pb o key A T < 4294967296 := by
    unfold extResv
    split
    · split
      · rename_i hfl
        obtain ⟨c, rfl⟩ : ∃ c, T = [c] := by
          have := hT1 hfl
          match T, this with
          | [c], _ => exact ⟨c, rfl⟩
        have hc := suffix_lt (hS ▸ h.stack) 0 (by simp)
        simp only [List.getElem_cons_zero] at hc
        have := (h.amem c hc).2.2.2.2.1
        simp only [List.getD_cons_zero]
        rw [getD_eq_get hc, ← this]
        have := NpaiIR.leToNat_lt (readMem m.mem (AR + 24 * c + 16) 4)
        simpa [rd32] using this
      · simp [RNONE]
    · omega
  have hres : extResv pb o key A T < 18446744073709551616 := by omega
  refine twp_mono (extRes_twp (e := A.length) h15 h14 h8 hcap h2 hres) ?_
  rintro m5 c ⟨hm5, hr5, hc⟩
  have hpm5 : PopMem m5 A A1 K T T.length S0 :=
    hpm.wr4 hm5 (by right; simp only [AR, KL, NCAP] at *; omega) (by omega)
      (by have := hT1; have := hT0; by_cases h1 : u8At pb (o + 1) = 1 <;> simp_all <;> omega)
  have rd5 : ∀ b, b + 4 ≤ AR + 24 * A.length + 16 ∨ AR + 24 * A.length + 16 + 4 ≤ b → rd32 m5 b = rd32 m4 b := by
    intro b hb; rw [rd32_eq, rd32_eq, hm5, rdm_wr4_other _ _ _ _ hb]
  have hEm : EntMem m5 A.length (extE pb o key (rdm m.mem (AR + 24 * A.length + 8)) A K T) := by
    simp only [EntMem, extE, extEnt]
    refine ⟨by rw [rd5 _ (by omega)]; exact e0, by rw [rd5 _ (by omega)]; exact e4,
      by rw [rd5 _ (by omega)]; exact e8, by rw [rd5 _ (by omega)]; exact e12, ?_,
      by rw [rd5 _ (by omega)]; exact e20⟩
    rw [rd32_eq, hm5, rdm_wr4_same _ _ _ hres32]
  obtain ⟨A', K', S0', hpre, hlen, hoo⟩ := ext_step h hcap hk hf hkey hS hT1 hT0 hp hpm5 hEm
    (by rw [rd5 _ (by simp only [C_KC, AR]; omega)]; exact hkc)
    (by rw [rd5 _ (by simp only [C_NODES, AR]; omega)]; exact hhdr)
    (hfr.trans (by rw [hm5]; exact (MFrame.refl _).wr4 _ _ (.inl ⟨by omega, by simp only [AR, SH8, NCAP] at *; omega⟩)))
    (by rw [hr5 14 (by omega) (by omega) (by omega) (by omega), h14, h.st.k8])
    (by rw [hr5 15 (by omega) (by omega) (by omega) (by omega), h15, h.st.k1])
    (by rw [hr5 10 (by omega) (by omega) (by omega) (by omega), h10])
    (by rw [hr5 9 (by omega) (by omega) (by omega) (by omega), h9])
    (by rw [hr5 8 (by omega) (by omega) (by omega) (by omega), h8])
    (by rw [hr5 7 (by omega) (by omega) (by omega) (by omega), h7])
    (by rw [hr5 5 (by omega) (by omega) (by omega) (by omega), h5])
  refine ⟨A', K', S0', hpre, hlen, hoo, ?_⟩
  omega

end

end ReexecNpai

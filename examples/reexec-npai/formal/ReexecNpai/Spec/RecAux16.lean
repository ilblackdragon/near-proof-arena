import ReexecNpai.Spec.RecAux15

/-!
# Record parse: the extension body (`pExt`)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m m1 : M}

/-- The header chunks of an extension: from the record start to `ExtMid`, given the checks hold. -/
theorem extMid_of (hs : RecStart cb pb rs R N o A K S m m1) (hk : u8At pb o = 3)
    {m1' m2 m3 : M}
    (c1 : ExtChk1 m1 (PF + o + 1) (PF + pb.length))
    (a1 : m1'.mem = m1.mem) (a2 : m1'.regs 1 = (m1.mem (PF + o + 1)).toNat) (a3 : m1'.regs 10 = PF + o + 1 + 1)
    (a5 : m1'.regs 5 = m1.regs 5) (a7 : m1'.regs 7 = m1.regs 7) (a8 : m1'.regs 8 = m1.regs 8)
    (a9 : m1'.regs 9 = m1.regs 9) (a14 : m1'.regs 14 = 8) (a15 : m1'.regs 15 = 1)
    (b0 : m2.mem = wr4 (wr4 (wr4 m1'.mem (AR + 24 * A.length) (PF + o + 1 + 1)) (AR + 24 * A.length + 12)
      (rd32 m1' C_KC)) (AR + 24 * A.length + 20) 0)
    (b6 : m2.regs 6 = rd32 m1' C_KC) (b10 : m2.regs 10 = PF + o + 1 + 1) (b1 : m2.regs 1 = m1'.regs 1)
    (b5 : m2.regs 5 = m1'.regs 5) (b7 : m2.regs 7 = m1'.regs 7) (b8 : m2.regs 8 = A.length)
    (b9 : m2.regs 9 = m1'.regs 9) (b14 : m2.regs 14 = 8) (b15 : m2.regs 15 = 1)
    (c3 : ExtChk3 m2 (PF + o + 2) (PF + pb.length))
    (r3 : ExtRegs3 m2 m3 (PF + o + 2) A.length (revSum pb A)) :
    ∃ key, ExtMid cb pb rs R N o A K S m key m3 ∧
      (u8At pb (o + 1) = 1 → sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32 → ExtFacts pb o) := by
  obtain ⟨g5, g7, g8, g14, g15⟩ := hs.regs
  have hpf1 := hs.pf
  have hcap := hs.cap
  have hpl := hs.plen
  have hfr2 : MFrame m1.mem m2.mem := by
    rw [b0, a1]
    simp only [NCAP] at hcap
    refine (((MFrame.refl _).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_ <;> (left; simp only [AR, SH8]; omega)
  have hpf2 : readMem m2.mem PF pb.length = pb := by
    rw [hfr2.readMem (by right; right; simp only [PF, SH8]; omega)]; exact hpf1
  rw [show PF + o + 1 + 1 = PF + o + 2 by omega] at a3 b0 b10
  obtain ⟨x1, x2, x3, x4⟩ := c1
  obtain ⟨y1, y2, y3⟩ := c3
  have hF := byte_at hpf1 (show PF + o + 1 = PF + (o + 1) by omega) (by omega)
  have hT := byte_at hpf1 (show PF + o + 1 + 1 = PF + (o + 2) by omega) (by omega)
  have hH := rd_at hpf2 rfl (show PF + o + 2 + 1 = PF + (o + 3) by omega) (by omega)
  have hP := byte_at hpf2 (show PF + o + 2 + 5 = PF + (o + 7) by omega) (by omega)
  rw [hF] at x2; rw [hT] at x4; rw [hH] at y1 y2; rw [hP] at y3
  have hend : o + leAt pb (o + 3) 4 + 47 ≤ pb.length := by omega
  obtain ⟨key, hkey⟩ := (keyOfHP_sl false pb (o + 7) (leAt pb (o + 3) 4) y1 (by omega)).mpr (by simpa using y3)
  obtain ⟨qm, q0, q2, q3, q5, q10, q1, q6, q7, q8, q9, q14, q15⟩ := r3
  rw [hH] at qm q0 q3 q5 q10
  rw [hP] at q3
  have hkc : rd32 m1' C_KC = K.length := hs.kc a1
  refine ⟨key, ⟨hs.inv, hcap, hk, x2, x4, y1, hend, y3, hkey, ?_, ?_, ?_, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, q14, q15⟩,
    fun _ hz => ⟨x2, x4, y1, hend, y3, fun _ => hz⟩⟩
  · rw [qm, b0, a1, hs.mem, hkc]; rfl
  · rw [q0]
  · rw [q1, b1, a2, hF]
  · rw [q3]
    have := extKey_empty y1 (by omega) hkey
    by_cases hk0 : key = []
    · rw [if_pos (this.mp hk0), if_pos hk0]
    · rw [if_neg (fun h' => hk0 (this.mpr h')), if_neg hk0]
  · rw [q5]
  · rw [q6, b6, hkc]
  · rw [q7, b7, a7, g7]
  · rw [q8]
  · rw [q9, b9, a9, hs.rE]
  · rw [q10]

theorem RecStart.rv (hs : RecStart cb pb rs R N o A K S m m1) : revSum pb A < 4294967296 := by
  have := revSum_le hs.inv; have := hs.inv.ole; have := hs.inv.st.plen
  simp only [PMAX] at *; omega

/-- The tail of `pExt` (the child pop / `NONE`, and `res`), as `twp`. -/
theorem ext_tail_twp {key : List Nat} {m3 : M} (hm : ExtMid cb pb rs R N o A K S m key m3)
    (hz : u8At pb (o + 1) = 1 → sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32)
    (hsp : u8At pb (o + 1) = 1 → 1 ≤ S.length) :
    twp P (Inp pub cb pb) (seqs [.ite 1 (seqs (extA1 ++ extA2)) (.ite 3 (CST 2 NONE) nop), wField 16 2]) m3
      (fun m5 c => BodyPostT cb pb rs R N o (o + leAt pb (o + 3) 4 + 47) A m5 (c + 550)) := by
  simp only [seqs, twp_seq]
  have hpl := hm.inv.st.plen
  have hend := hm.hend
  simp only [PMAX] at hpl
  by_cases hfl : u8At pb (o + 1) = 1
  · refine twp_ite_ne (by rw [hm.r1, hfl]; decide) ?_
    rw [rec_twp_seqs_append _ _ (by simp [extA1]) (by simp [extA2])]
    have hz' := (extZero_iff hm.pf hm.data hend).mpr (hz hfl)
    refine twp_mono (extA1_twp (s := leAt pb (o + 3) 4 + 5 + (PF + o + 2)) (sp := S.length) hm.r15 hm.r14 hm.r0
      (by simp only [PF] at *; omega) hm.r7 hz' (hsp hfl)) ?_
    rintro m3' c1 ⟨hm3', hregs, hc1⟩
    refine twp_mono (ext_pop_twp hm hfl (hz hfl) hm3' hregs (hsp hfl)) ?_
    intro m4 c2 h4
    refine twp_mono h4 ?_
    intro m5 c3 hp
    exact hp.mono (by omega)
  · refine twp_ite_zero (by rw [hm.r1]; have := hm.fl; omega) ?_
    refine twp_mono (ext_nopop_twp hm hfl) ?_
    intro m4 c2 h4
    refine twp_mono h4 ?_
    intro m5 c3 hp
    exact hp.mono (by omega)

theorem ext_body_twp (hs : RecStart cb pb rs R N o A K S m m1) (hk : u8At pb o = 3)
    {stk' : List PTrie} {o' : Nat}
    (hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) = some (stk', pb.drop o'))
    (ho' : o' ≤ pb.length) :
    twp P (Inp pub cb pb) pExt m1 (fun m2 c => BodyPostT cb pb rs R N o o' A m2 (c + 300)) := by
  have hlt := hs.olt
  rw [decRec_pos] at hd
  unfold recPos at hd
  rw [if_pos (by omega)] at hd
  simp only [hk, show ¬ (3 = 1) from by decide, show ¬ (3 = 2) from by decide, ↓reduceIte] at hd
  cases hr : extPos pb (o + 1) ((S.map (treeAt A K (vals0 pb A))).reverse) with
  | none => rw [hr] at hd; simp at hd
  | some x =>
  obtain ⟨stk'', o''⟩ := x
  rw [hr] at hd
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨hf, ho''⟩ := facts_of_extPos hr
  have hend := hf.hend
  have he : o'' = o' := drop_inj (by omega) ho' hd.2
  subst he
  rw [ho'']
  have hsp : u8At pb (o + 1) = 1 → 1 ≤ S.length := by
    intro hfl
    obtain ⟨key, -, hpos⟩ := extPos_of_facts hf
    rw [hpos] at hr
    rcases Nat.eq_zero_or_pos S.length with h0 | h0
    · rw [List.length_eq_zero_iff] at h0
      subst h0
      simp [extRes, hfl] at hr
    · exact h0
  have hpl := hs.plen
  have hcap := hs.cap
  have hrv := hs.rv
  obtain ⟨g5, g7, g8, g14, g15⟩ := hs.regs
  rw [pExt_split, rec_twp_seqs_append _ _ (by simp [extL1]) (by simp),
    rec_twp_seqs_append _ _ (by simp [extL1]) (by simp [extL3]),
    rec_twp_seqs_append _ _ (by simp [extL1]) (by simp [extL2])]
  obtain ⟨c1, -, -, -, -⟩ := chk_of_extFacts (m1 := m1) (m2 := m1) hs.pf hs.pf hf
  refine twp_mono (ext1_twp (q := PF + o + 1) (E := PF + pb.length) hs.k1 hs.k8 hs.r10 hpl hs.rE c1) ?_
  rintro m1' ca ⟨a1, a2, a3, a5, a7, a8, a9, a14, a15, hca⟩
  refine twp_mono (ext2_twp (e := A.length) (p := PF + o + 1 + 1) a15 a14 (by rw [a8, g8]) hcap a3
    (by simp only [PF] at *; omega)) ?_
  rintro m2 cb' ⟨b0, b6, b2, b10, b1, b5, b7, b8, b9, b14, b15, hcb⟩
  have hfr2 : MFrame m1.mem m2.mem := by
    rw [b0, a1]
    simp only [NCAP] at hcap
    refine (((MFrame.refl _).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_ <;> (left; simp only [AR, SH8]; omega)
  have hpf2 : readMem m2.mem PF pb.length = pb := by
    rw [hfr2.readMem (by right; right; simp only [PF, SH8]; omega)]; exact hs.pf
  obtain ⟨-, c3, -, -, -⟩ := chk_of_extFacts (m1 := m1) (m2 := m2) hs.pf hpf2 hf
  refine twp_mono (ext3_twp (p := PF + o + 2) (E := PF + pb.length) (e := A.length) (rv := revSum pb A)
    b15 b14 (by rw [b10]) hpl (by rw [b9, a9, hs.rE]) (by omega) b8 hcap (by rw [b5, a5, g5]) hrv
    (by simp only [AR, NCAP, PF]; omega) c3) ?_
  rintro m3 cc ⟨r3, hcc⟩
  obtain ⟨key, hm, -⟩ := extMid_of hs hk c1 a1 a2 a3 a5 a7 a8 a9 a14 a15 b0 b6 b10 b1 b5 b7 b8 b9 b14 b15 c3 r3
  refine twp_mono (ext_tail_twp hm hf.zero hsp) ?_
  intro m5 cd hp
  exact hp.mono (by omega)

theorem ext_body_wp (hs : RecStart cb pb rs R N o A K S m m1) (hk : u8At pb o = 3) :
    wp P (Inp pub cb pb) pExt m1 (BodyPost cb pb rs R N o A) := by
  have hlt := hs.olt
  have hpl := hs.plen
  have hcap := hs.cap
  have hrv := hs.rv
  obtain ⟨g5, g7, g8, g14, g15⟩ := hs.regs
  rw [pExt_split, rec_wp_seqs_append _ _ (by simp [extL1]) (by simp),
    rec_wp_seqs_append _ _ (by simp [extL1]) (by simp [extL3]),
    rec_wp_seqs_append _ _ (by simp [extL1]) (by simp [extL2])]
  refine wp_mono (ext1_wp (q := PF + o + 1) (E := PF + pb.length) hs.k1 hs.k8 hs.r10 hpl hs.rE (by omega)) ?_
  rintro m1' ⟨c1, a1, a2, a3, a5, a7, a8, a9, a14, a15⟩
  refine wp_of_spec (ext2_twp (e := A.length) (p := PF + o + 1 + 1) a15 a14 (by rw [a8, g8]) hcap a3
    (by simp only [PF] at *; omega)) ?_
  rintro m2 cb' ⟨b0, b6, b2, b10, b1, b5, b7, b8, b9, b14, b15, hcb⟩
  have hq : PF + o + 2 + 5 ≤ PF + pb.length := by have := c1.2.2.1; omega
  refine wp_mono (ext3_wp (p := PF + o + 2) (E := PF + pb.length) (e := A.length) (rv := revSum pb A)
    b15 b14 (by rw [b10]) hpl (by rw [b9, a9, hs.rE]) hq b8 hcap (by rw [b5, a5, g5]) hrv
    (by simp only [AR, NCAP, PF]; omega)) ?_
  rintro m3 ⟨c3, r3⟩
  obtain ⟨key, hm, hfacts⟩ := extMid_of hs hk c1 a1 a2 a3 a5 a7 a8 a9 a14 a15 b0 b6 b10 b1 b5 b7 b8 b9 b14 b15 c3 r3
  have hend := hm.hend
  simp only [seqs, wp_seq]
  rw [wp_ite]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · have hfl : u8At pb (o + 1) ≠ 1 := by rw [hm.r1] at h0; omega
    exact wp_of_spec (ext_nopop_twp hm hfl) (fun m4 c h4 => wp_of_spec h4 (fun m5 c' hp => hp.post))
  · have hfl : u8At pb (o + 1) = 1 := by rw [hm.r1] at h1; have := hm.fl; omega
    rw [rec_wp_seqs_append _ _ (by simp [extA1]) (by simp [extA2])]
    refine wp_mono (extA1_wp (s := leAt pb (o + 3) 4 + 5 + (PF + o + 2)) (sp := S.length) hm.r15 hm.r14 hm.r0
      (by simp only [PF] at *; omega) hm.r7) ?_
    rintro m3' ⟨hzr, hsp, hm3', hregs⟩
    have hz := (extZero_iff hm.pf hm.data hend).mp hzr
    exact wp_of_spec (ext_pop_twp hm hfl hz hm3' hregs hsp)
      (fun m4 c h4 => wp_of_spec h4 (fun m5 c' hp => hp.post))

end

end ReexecNpai

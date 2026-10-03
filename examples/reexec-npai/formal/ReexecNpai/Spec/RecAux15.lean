import ReexecNpai.Spec.RecAux14

/-!
# Record parse: extension body after the header checks (the pop and `res`)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Memory after the first three extension chunks (entry `e` fields `pre`, `kid`, `val`, `preLen`). -/
def extM3 (M0 : Nat → UInt8) (e p kc hl : Nat) : Nat → UInt8 :=
  wr4 (wr4 (wr4 (wr4 M0 (AR + 24 * e) p) (AR + 24 * e + 12) kc) (AR + 24 * e + 20) 0) (AR + 24 * e + 4) (hl + 45)

theorem extM3_out (M0 : Nat → UInt8) (e p kc hl b : Nat) (hb : b + 4 ≤ AR + 24 * e ∨ AR + 24 * e + 24 ≤ b) :
    rdm (extM3 M0 e p kc hl) b = rdm M0 b := by
  simp (disch := omega) only [extM3, rdm_wr4_other]

theorem extM3_frame (M0 : Nat → UInt8) (e p kc hl : Nat) (he : e < NCAP) : MFrame M0 (extM3 M0 e p kc hl) := by
  simp only [NCAP] at he
  unfold extM3
  refine (((((MFrame.refl _).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_) <;>
    (left; simp only [AR, SH8]; omega)

/-- State after `extL1 ++ extL2 ++ extL3`. -/
structure ExtMid (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (K S : List Nat)
    (m : M) (key : List Nat) (m3 : M) : Prop where
  inv : ParseInv cb pb rs R N o A K S m
  cap : A.length < NCAP
  hk : u8At pb o = 3
  fl : u8At pb (o + 1) ≤ 1
  tag : u8At pb (o + 2) = 3
  hl1 : 1 ≤ leAt pb (o + 3) 4
  hend : o + leAt pb (o + 3) 4 + 47 ≤ pb.length
  hp0 : u8At pb (o + 7) = 0 ∨ (16 ≤ u8At pb (o + 7) ∧ u8At pb (o + 7) < 32)
  hkey : keyOfHP false (sl pb (o + 7) (leAt pb (o + 3) 4)) = some key
  mem : m3.mem = extM3 m.mem A.length (PF + o + 2) K.length (leAt pb (o + 3) 4)
  r0 : m3.regs 0 = leAt pb (o + 3) 4 + 5 + (PF + o + 2)
  r1 : m3.regs 1 = u8At pb (o + 1)
  r2 : m3.regs 2 = A.length
  r3 : m3.regs 3 = if key = [] then 1 else 0
  r5 : m3.regs 5 = revSum pb A + (leAt pb (o + 3) 4 + 45)
  r6 : m3.regs 6 = K.length
  r7 : m3.regs 7 = S.length
  r8 : m3.regs 8 = A.length
  r9 : m3.regs 9 = PF + pb.length
  r10 : m3.regs 10 = PF + o + 2 + (leAt pb (o + 3) 4 + 45)
  r14 : m3.regs 14 = 8
  r15 : m3.regs 15 = 1

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m : M}
  {key : List Nat} {m3 : M}

theorem ExtMid.facts (hm : ExtMid cb pb rs R N o A K S m key m3)
    (hz : u8At pb (o + 1) = 1 → sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32) : ExtFacts pb o :=
  ⟨hm.fl, hm.tag, hm.hl1, hm.hend, hm.hp0, hz⟩

theorem ExtMid.frame (hm : ExtMid cb pb rs R N o A K S m key m3) : MFrame m.mem m3.mem := by
  rw [hm.mem]; exact extM3_frame _ _ _ _ _ hm.cap

theorem ExtMid.out (hm : ExtMid cb pb rs R N o A K S m key m3) (b : Nat)
    (hb : b + 4 ≤ AR + 24 * A.length ∨ AR + 24 * A.length + 24 ≤ b) : rd32 m3 b = rd32 m b := by
  rw [rd32_eq, rd32_eq, hm.mem, extM3_out _ _ _ _ _ _ hb]

theorem ExtMid.pf (hm : ExtMid cb pb rs R N o A K S m key m3) : readMem m3.mem PF pb.length = pb := by
  rw [hm.frame.readMem (by right; right; simp only [PF, SH8]; omega)]; exact hm.inv.st.proof

theorem ExtMid.data (hm : ExtMid cb pb rs R N o A K S m key m3) : readMem m3.mem 0 168 = dataSeg := by
  rw [hm.frame.readMem (by left; simp only [C_KC]; omega)]; exact hm.inv.st.data

theorem ExtMid.popMem (hm : ExtMid cb pb rs R N o A K S m key m3) {S0 T : List Nat} (hS : S = S0 ++ T) :
    PopMem m3 A A K T 0 S0 := by
  have h := hm.inv
  have hcap := hm.cap
  have hkl := h.klen
  simp only [NCAP] at hcap
  refine (PopMem.init h.amem h.kmem (hS ▸ h.smem)).frame (fun b h1 h2 => hm.out b ?_) (by simp only [NCAP]; omega)
    (by simp only [NCAP]; omega)
  simp only [AR, KL] at *; omega

theorem ExtMid.e_reads (hm : ExtMid cb pb rs R N o A K S m key m3) :
    rd32 m3 (AR + 24 * A.length) = PF + o + 2 ∧
    rd32 m3 (AR + 24 * A.length + 4) = leAt pb (o + 3) 4 + 45 ∧
    rd32 m3 (AR + 24 * A.length + 8) = rdm m.mem (AR + 24 * A.length + 8) ∧
    rd32 m3 (AR + 24 * A.length + 12) = K.length ∧
    rd32 m3 (AR + 24 * A.length + 20) = 0 := by
  have hpl := hm.inv.st.plen
  have hkl := hm.inv.klen
  have hcap := hm.cap
  have := leAt4_lt pb (o + 3)
  have := hm.hend
  simp only [rd32_eq, hm.mem, extM3]
  simp only [PMAX, NCAP, PF] at hpl hcap ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [rdm_wr4_other, rdm_wr4_same]

theorem rec_hexPrefix_len {pb : Bytes} {a hl : Nat} {key : List Nat} {leaf : Bool}
    (hkey : keyOfHP leaf (sl pb a hl) = some key) (h : a + hl ≤ pb.length) :
    (hexPrefix key leaf).length = hl := by
  rw [(hexPrefix_keyOfHP hkey).1, sl_length_of h]

theorem extE_slot (hkey : keyOfHP false (sl pb (o + 7) (leAt pb (o + 3) 4)) = some key)
    (hend : o + leAt pb (o + 3) 4 + 47 ≤ pb.length) (ps : Nat) (A : List Ent) (K T : List Nat) :
    childSlot (extE pb o key ps A K T) 0 = leAt pb (o + 3) 4 + 5 + (PF + o + 2) := by
  have := rec_hexPrefix_len hkey (by omega)
  simp only [childSlot, extE, extEnt, extNF, slotOff, this]
  omega

theorem PopMem.congr {m m' : M} {A Ak : List Ent} {K T : List Nat} {k : Nat} {S0 : List Nat}
    (h : PopMem m A Ak K T k S0) (hm : m'.mem = m.mem) : PopMem m' A Ak K T k S0 :=
  ⟨fun j hj => by simp only [EntMem, rd32_eq, hm]; exact h.amem j hj,
   fun i hi => by rw [rd32_eq, hm]; exact h.kmem i hi,
   fun i hi => by rw [rd32_eq, hm]; exact h.smem i hi⟩

/-- The pop of a revealed extension child (`extA2`), then `res` and the arena step. -/
theorem ext_pop_twp (hm : ExtMid cb pb rs R N o A K S m key m3) (hfl : u8At pb (o + 1) = 1)
    (hz : sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32) {m3' : M} (hm3' : m3'.mem = m3.mem)
    (hregs : ∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → m3'.regs j = m3.regs j) (hsp : 1 ≤ S.length) :
    twp P (Inp pub cb pb) (seqs extA2) m3' (fun m4 c => twp P (Inp pub cb pb) (wField 16 2) m4
      (fun m5 c' => BodyPostT cb pb rs R N o (o + leAt pb (o + 3) 4 + 47) A m5 (c + c' + 800))) := by
  have h := hm.inv
  have hcap := hm.cap
  have hkl := h.klen
  have hpl := h.st.plen
  have hend := hm.hend
  have hf := hm.facts (fun _ => hz)
  simp only [NCAP, PMAX] at hcap hpl
  have hS : S = S.dropLast ++ [S[S.length - 1]] := by
    rw [← List.getLast_eq_getElem (by intro h0; simp [h0] at hsp)]
    exact (List.dropLast_concat_getLast _).symm
  generalize hc : S[S.length - 1] = c at hS
  generalize hS0 : S.dropLast = S0 at hS
  have hcA : c < A.length := by
    have := suffix_lt (hS ▸ h.stack) 0 (by simp); simpa using this
  have hS0l : S0.length = S.length - 1 := by rw [hS]; simp
  generalize hE : extE pb o key (rdm m.mem (AR + 24 * A.length + 8)) A K [c] = E
  have hslot : childSlot E 0 = leAt pb (o + 3) 4 + 5 + (PF + o + 2) := by
    rw [← hE]; exact extE_slot hm.hkey hend _ _ _ _
  have hcv : rd32 m3' (STK + 4 * (S.length - 1)) = c := by
    rw [rd32_eq, hm3', ← rd32_eq, hm.out _ (by simp only [AR, STK]; omega)]
    have := h.smem (S.length - 1) (by omega)
    rw [this, ← hc]
  have hcN : c < NCAP := by simp only [NCAP]; omega
  refine twp_mono (extA2_twp (emp := decide (key = [])) (s := leAt pb (o + 3) 4 + 5 + (PF + o + 2))
    (sp := S.length) (kc := K.length) (c := c)
    (by rw [hregs 15 (by omega) (by omega) (by omega)]; exact hm.r15)
    (by rw [hregs 14 (by omega) (by omega) (by omega)]; exact hm.r14)
    (by rw [hregs 0 (by omega) (by omega) (by omega)]; exact hm.r0)
    (by simp only [PF] at *; omega)
    (by rw [hregs 7 (by omega) (by omega) (by omega)]; exact hm.r7) hsp (by simp only [NCAP]; omega)
    hcv hcN
    (by rw [hregs 6 (by omega) (by omega) (by omega)]; exact hm.r6) (by simp only [NCAP]; omega)
    (by rw [hregs 3 (by omega) (by omega) (by omega), hm.r3]; by_cases hk0 : key = [] <;> simp [hk0])) ?_
  rintro m4 c4 ⟨hm4, h7, h6, h2, ⟨f0, f3, f5, f8, f9, f10, f14, f15⟩, hc4⟩
  -- the arena relation
  have hp : PopRel A [c] (childSlot E) (setPs A c (leAt pb (o + 3) 4 + 5 + (PF + o + 2))) 1 := by
    have := (PopRel.zero A [c] (childSlot E)).step (k := 0) (by simp)
      (fun q hq => by simp at hq; subst hq; simpa using hcA)
      (fun a b ha hb hab => by simp at ha hb; omega)
    simpa [hslot] using this
  -- memory
  let m4a : M := ⟨m4.regs, wr4 (wr4 m3'.mem (AR + 24 * c + 8) (leAt pb (o + 3) 4 + 5 + (PF + o + 2)))
    (KL + 4 * K.length) c⟩
  have hpm0 : PopMem m3' A A K [c] 0 S0 := (hm.popMem hS).congr hm3'
  have hpma : PopMem m4a A (setPs A c (leAt pb (o + 3) 4 + 5 + (PF + o + 2))) K [c] 1 S0 := by
    have := hpm0.step (s := leAt pb (o + 3) 4 + 5 + (PF + o + 2)) (m' := m4a) (by simp)
      (fun q hq => by simp at hq; subst hq; simpa using hcA) rfl (by simp only [NCAP]; omega)
      (by simp only [NCAP]; omega) (by simp only [PF] at *; omega) (by simp [m4a])
    simpa using this
  have hm4' : m4.mem = wr4 m4a.mem C_KC (K.length + 1) := hm4
  have hpm : PopMem m4 A (setPs A c (leAt pb (o + 3) 4 + 5 + (PF + o + 2))) K [c] [c].length S0 :=
    hpma.wr4 hm4' (by left; simp only [C_KC, AR]; omega) (by simp only [NCAP]; omega)
      (by simp only [NCAP]; omega)
  have rd4 : ∀ b, b + 4 ≤ AR + 24 * c + 8 ∨ AR + 24 * c + 8 + 4 ≤ b →
      b + 4 ≤ KL + 4 * K.length ∨ KL + 4 * K.length + 4 ≤ b → b + 4 ≤ C_KC ∨ C_KC + 4 ≤ b →
      rd32 m4 b = rd32 m3 b := by
    intro b h1 h2 h3
    rw [rd32_eq, rd32_eq, hm4, rdm_wr4_other _ _ _ _ h3, rdm_wr4_other _ _ _ _ h2, rdm_wr4_other _ _ _ _ h1, hm3']
  obtain ⟨e0, e4, e8, e12, e20⟩ := hm.e_reads
  have hfr : MFrame m.mem m4.mem := by
    rw [hm4, hm3']
    refine (((hm.frame.wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_)
    · left; simp only [AR, SH8]; omega
    · left; simp only [AR, KL, SH8]; omega
    · right; rfl
  have hr2 : m4.regs 2 = extResv pb o key A [c] := by
    rw [h2]
    cases key with
    | nil =>
      simp only [decide_true, ↓reduceIte, extResv, hfl, List.getD_cons_zero]
      rw [rd32_eq, hm3', ← rd32_eq, hm.out _ (by left; omega), rec_getD_eq_get hcA]
      exact (h.amem c hcA).2.2.2.2.1
    | cons k ks =>
      simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, extResv]
      rw [hregs 2 (by omega) (by omega) (by omega), hm.r2]
  have g : ∀ j, j ≠ 1 → j ≠ 2 → j ≠ 4 → j ≠ 6 → j ≠ 7 → j ≠ 11 → j ≠ 12 → j ≠ 13 →
      m4.regs j = m3'.regs j → m4.regs j = m3.regs j := by
    intro j _ _ _ _ _ h11 h12 h13 e; rw [e, hregs j h11 h12 h13]
  subst hE
  refine twp_mono (ext_fin (pub := pub) h hm.cap hm.hk hf hm.hkey hS (fun _ => by simp)
    (fun h1 => absurd hfl h1) hp hpm
    (by rw [rd4 _ (by omega) (by left; simp only [AR, KL]; omega) (by right; simp only [AR, C_KC]; omega)]; exact e0)
    (by rw [rd4 _ (by omega) (by left; simp only [AR, KL]; omega) (by right; simp only [AR, C_KC]; omega)]; exact e4)
    (by rw [rd4 _ (by omega) (by left; simp only [AR, KL]; omega) (by right; simp only [AR, C_KC]; omega)]; exact e8)
    (by rw [rd4 _ (by omega) (by left; simp only [AR, KL]; omega) (by right; simp only [AR, C_KC]; omega)]; exact e12)
    (by rw [rd4 _ (by omega) (by left; simp only [AR, KL]; omega) (by right; simp only [AR, C_KC]; omega)]; exact e20)
    (by rw [rd32_eq, hm4, rdm_wr4_same _ _ _ (by omega)]; simp)
    (by rw [rd4 _ (by left; simp only [AR, C_NODES]; omega) (by left; simp only [KL, C_NODES]; omega)
          (by left; simp only [C_KC, C_NODES]; omega), hm.out _ (by left; simp only [AR, C_NODES]; omega)]
        exact h.hdr)
    hfr
    (by rw [g 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f14]
        exact hm.r14)
    (by rw [g 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f15]
        exact hm.r15)
    hr2
    (by rw [g 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f10,
          hm.r10]; omega)
    (by rw [g 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f9]
        exact hm.r9)
    (by rw [g 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f8]
        exact hm.r8)
    (by rw [h7]; omega)
    (by rw [g 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f5]
        exact hm.r5)) ?_
  intro m5 c5 hp5
  exact hp5.mono (by omega)

theorem cst2_twp {m : M} (v : Nat) (hv : v < 4294967296) :
    twp P (Inp pub cb pb) (CST 2 v) m (fun m' c => m'.mem = m.mem ∧ m'.regs 2 = v ∧
      (∀ j, j ≠ 2 → m'.regs j = m.regs j) ∧ c ≤ 5) := by
  rec_auto
  all_goals first | omega | (intro j hj; simp [hj])

/-- An unrevealed extension child: `res` is `NONE` for an empty key. -/
theorem ext_nopop_twp (hm : ExtMid cb pb rs R N o A K S m key m3) (hfl : u8At pb (o + 1) ≠ 1) :
    twp P (Inp pub cb pb) (.ite 3 (CST 2 NONE) nop) m3 (fun m4 c => twp P (Inp pub cb pb) (wField 16 2) m4
      (fun m5 c' => BodyPostT cb pb rs R N o (o + leAt pb (o + 3) 4 + 47) A m5 (c + c' + 800))) := by
  have h := hm.inv
  have hf := hm.facts (fun h1 => absurd h1 hfl)
  have fin : ∀ m4 : M, m4.mem = m3.mem → m4.regs 2 = extResv pb o key A [] →
      (∀ j, j ≠ 2 → m4.regs j = m3.regs j) →
      twp P (Inp pub cb pb) (wField 16 2) m4
        (fun m5 c => BodyPostT cb pb rs R N o (o + leAt pb (o + 3) 4 + 47) A m5 (c + 1000)) := by
    intro m4 hm4 h2 hr
    have hS : S = S ++ [] := by simp
    obtain ⟨e0, e4, e8, e12, e20⟩ := hm.e_reads
    have rd : ∀ b, rd32 m4 b = rd32 m3 b := fun b => by rw [rd32_eq, rd32_eq, hm4]
    exact ext_fin h hm.cap hm.hk hf hm.hkey hS (fun h1 => absurd h1 hfl) (fun _ => rfl)
      (PopRel.zero _ _ _) ((hm.popMem hS).congr hm4)
      (by rw [rd]; exact e0) (by rw [rd]; exact e4) (by rw [rd]; exact e8) (by rw [rd]; exact e12)
      (by rw [rd]; exact e20)
      (by rw [rd, hm.out _ (by left; simp only [C_KC, AR]; omega)]; simpa using h.kc)
      (by rw [rd, hm.out _ (by left; simp only [C_NODES, AR]; omega)]; exact h.hdr)
      (by rw [hm4]; exact hm.frame)
      (by rw [hr 14 (by omega)]; exact hm.r14) (by rw [hr 15 (by omega)]; exact hm.r15) h2
      (by rw [hr 10 (by omega), hm.r10]; omega) (by rw [hr 9 (by omega)]; exact hm.r9)
      (by rw [hr 8 (by omega)]; exact hm.r8) (by rw [hr 7 (by omega)]; simpa using hm.r7)
      (by rw [hr 5 (by omega)]; exact hm.r5)
  by_cases hk0 : key = []
  · subst hk0
    refine twp_ite_ne (by rw [hm.r3]; simp) (twp_mono (cst2_twp NONE (by simp [NONE])) ?_)
    rintro m4 c ⟨hm4, h2, hr, hc⟩
    refine twp_mono (fin m4 hm4 (by rw [h2]; simp [extResv, hfl, NONE, RNONE]) hr) ?_
    intro m5 c' hp; exact hp.mono (by omega)
  · refine twp_ite_zero (by rw [hm.r3]; simp [hk0]) ?_
    rw [twp_nop]
    refine twp_mono (fin m3 rfl (by rw [hm.r2]; cases key with
      | nil => exact absurd rfl hk0
      | cons _ _ => rfl) (fun _ _ => rfl)) ?_
    intro m5 c' hp; exact hp.mono (by omega)

end

end ReexecNpai

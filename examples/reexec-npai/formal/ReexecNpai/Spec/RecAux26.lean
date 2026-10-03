import ReexecNpai.Spec.RecAux25

/-!
# Record parse: branch records, the state before the slot loop and the tail
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Memory after the branch header chunks (entry `e` fields `val`, `pre`, `kid`, `preLen`). -/
def brM4 (M0 : Nat → UInt8) (e val pre kc pl : Nat) : Nat → UInt8 :=
  wr4 (wr4 (wr4 (wr4 M0 (AR + 24 * e + 20) val) (AR + 24 * e) pre) (AR + 24 * e + 12) kc) (AR + 24 * e + 4) pl

theorem brM4_out (M0 : Nat → UInt8) (e val pre kc pl b : Nat) (hb : b + 4 ≤ AR + 24 * e ∨ AR + 24 * e + 24 ≤ b) :
    rdm (brM4 M0 e val pre kc pl) b = rdm M0 b := by
  simp (disch := omega) only [brM4, rdm_wr4_other]

theorem brM4_frame (M0 : Nat → UInt8) (e val pre kc pl : Nat) (he : e < NCAP) :
    MFrame M0 (brM4 M0 e val pre kc pl) := by
  simp only [NCAP] at he
  unfold brM4
  refine (((((MFrame.refl _).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_) <;>
    (left; simp only [AR, SH8]; omega)

/-- The value address of a branch entry. -/
def brVal (pb : Bytes) (o : Nat) : Nat := if u8At pb o = 5 then PF + o + 5 else 0

/-- State after `brL4b` (just before the slot loop). -/
structure BrMid (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (K S : List Nat)
    (m m4 : M) : Prop where
  inv : ParseInv cb pb rs R N o A K S m
  cap : A.length < NCAP
  hk : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6
  v5 : u8At pb o = 5 → o + 5 ≤ pb.length
  tag : u8At pb (brP pb o + 2) = if u8At pb o = 4 then 1 else 2
  sub : SubB 16 (brBm pb o) (brEx pb o)
  hend : brEnd pb o ≤ pb.length
  vlen : u8At pb o = 5 → sl pb (brP pb o + 3) 4 = sl pb (o + 1) 4
  vzero : u8At pb o = 5 → sl pb (brP pb o + 7) 32 = zeros 32
  mem : m4.mem = brM4 m.mem A.length (brVal pb o) (PF + brP pb o + 2) K.length
    (brHdr pb o + 32 * brNp pb o + 10)
  r1 : m4.regs 1 = brBm pb o + brEx pb o * 65536
  r2 : m4.regs 2 = PF + brR pb o + 2 + 32 * popc 16 (brBm pb o)
  r3 : m4.regs 3 = K.length
  r5 : m4.regs 5 = revSum pb A + (if u8At pb o = 5 then leAt pb (o + 1) 4 else 0) +
    (brHdr pb o + 32 * brNp pb o + 10)
  r6 : m4.regs 6 = 16
  r7 : m4.regs 7 = S.length
  r8 : m4.regs 8 = A.length
  r9 : m4.regs 9 = PF + pb.length
  r10 : m4.regs 10 = PF + brEnd pb o
  r14 : m4.regs 14 = 8
  r15 : m4.regs 15 = 1

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m m4 : M}

theorem BrMid.facts (hm : BrMid cb pb rs R N o A K S m m4) (hz : ZeroB 16 (brBm pb o) (brEx pb o) (brSlots pb o)) :
    BrFacts pb o :=
  ⟨hm.hk, hm.v5, hm.tag, hm.sub, hm.hend, hm.vlen, hm.vzero, hz⟩

theorem BrMid.frame (hm : BrMid cb pb rs R N o A K S m m4) : MFrame m.mem m4.mem := by
  rw [hm.mem]; exact brM4_frame _ _ _ _ _ _ hm.cap

theorem BrMid.out (hm : BrMid cb pb rs R N o A K S m m4) (b : Nat)
    (hb : b + 4 ≤ AR + 24 * A.length ∨ AR + 24 * A.length + 24 ≤ b) : rd32 m4 b = rd32 m b := by
  rw [rd32_eq, rd32_eq, hm.mem, brM4_out _ _ _ _ _ _ _ hb]

theorem BrMid.pf (hm : BrMid cb pb rs R N o A K S m m4) : readMem m4.mem PF pb.length = pb := by
  rw [hm.frame.readMem (by right; right; simp only [PF, SH8]; omega)]; exact hm.inv.st.proof

theorem BrMid.data (hm : BrMid cb pb rs R N o A K S m m4) : readMem m4.mem 0 168 = dataSeg := by
  rw [hm.frame.readMem (by left; simp only [C_KC]; omega)]; exact hm.inv.st.data

/-- The static facts of the slot loop. -/
theorem BrMid.static (hm : BrMid cb pb rs R N o A K S m m4) :
    BrStatic pb A K S (brBm pb o) (brEx pb o) (PF + brR pb o + 2)
      (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) := by
  have h := hm.inv
  have hpl := h.st.plen
  have hend := hm.hend
  simp only [PMAX] at hpl
  refine ⟨leAt2_lt _ _, leAt2_lt _ _, hm.sub, fun i hi he => slotPos_ksOf _ _ _ _ _ hm.sub hi he,
    by omega, by simp only [brEnd, brNp] at hend; simp only [PF] at *; omega, hm.cap, h.klen,
    fun q hq => h.stack.2.1 q hq, stack_inc h.wf h.stack⟩

/-- The slot-loop invariant at the start. -/
theorem BrMid.loop0 (hm : BrMid cb pb rs R N o A K S m m4) :
    BrLoop A K S m4 (brBm pb o) (brEx pb o) (PF + brR pb o + 2)
      (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) 16 m4 := by
  have h := hm.inv
  have hcap := hm.cap
  have hkl := h.klen
  simp only [NCAP] at hcap
  have hpm : PopMem m4 A A K S 0 [] := by
    refine (PopMem.init h.amem h.kmem (by simpa using h.smem)).frame (fun b h1 h2 => hm.out b ?_)
      (by simp only [NCAP]; omega) (by simp only [NCAP]; omega)
    simp only [AR, KL] at *; omega
  refine ⟨hm.r6, by omega, hm.r1, hm.r2, by rw [hm.r3]; simp, by rw [hm.r7]; simp, by simp,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨A, by simpa using hpm, by simpa using PopRel.zero A S _⟩,
    fun b _ => rfl, MFrame.refl _, fun j h1 h2 => absurd h2 (by omega)⟩

theorem popc_sub : ∀ (n bm ex : Nat), SubB n bm ex → popc n ex ≤ popc n bm
  | 0, _, _, _ => Nat.le_refl _
  | n + 1, bm, ex, h => by
    obtain ⟨s0, s1⟩ := (SubB_succ _ _ _).mp h
    rw [popc_succ, popc_succ]
    have := popc_sub n _ _ s1
    have : ex % 2 < 2 := Nat.mod_lt _ (by omega)
    have : bm % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases he : ex % 2 = 1
    · have := s0 he; omega
    · omega

theorem brEnd_ge (pb : Bytes) (o : Nat) : o + 14 + 32 * brNp pb o ≤ brEnd pb o := by
  have : o + 1 ≤ brP pb o := by unfold brP; split <;> omega
  have : 1 ≤ brHdr pb o := by unfold brHdr; split <;> omega
  simp only [brEnd, brR]; omega

theorem brE_entRev (pb : Bytes) (o ps : Nat) (A : List Ent) (K T : List Nat) :
    entRev pb (brE pb o ps A K T) =
      (brHdr pb o + 32 * brNp pb o + 10) + (if u8At pb o = 5 then leAt pb (o + 1) 4 else 0) := by
  simp only [entRev, brE, brEnt]
  by_cases h5 : u8At pb o = 5
  · have hv : hasVal (brNF pb o) = true := by
      simp only [brNF]; rw [if_neg (by omega), if_pos h5]; rfl
    simp only [hv, ↓reduceIte, h5, vlenAt, show PF + o + 5 - 4 = PF + (o + 1) by omega, pseg_PF, leAt]
  · have hv : hasVal (brNF pb o) = false := by
      simp only [brNF]; by_cases h4 : u8At pb o = 4
      · rw [if_pos h4]; rfl
      · rw [if_neg h4, if_neg h5]; rfl
    simp only [hv, h5, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]

theorem BrMid.e_reads (hm : BrMid cb pb rs R N o A K S m m4) :
    rd32 m4 (AR + 24 * A.length) = PF + brP pb o + 2 ∧
    rd32 m4 (AR + 24 * A.length + 4) = brHdr pb o + 32 * brNp pb o + 10 ∧
    rd32 m4 (AR + 24 * A.length + 8) = rdm m.mem (AR + 24 * A.length + 8) ∧
    rd32 m4 (AR + 24 * A.length + 12) = K.length ∧
    rd32 m4 (AR + 24 * A.length + 20) = brVal pb o := by
  have hpl := hm.inv.st.plen
  have hkl := hm.inv.klen
  have hcap := hm.cap
  have hend := hm.hend
  have := brEnd_ge pb o
  have hP : brP pb o + 2 + brHdr pb o + 32 * brNp pb o + 10 ≤ brEnd pb o := by simp only [brEnd, brR]; omega
  have hv : brVal pb o ≤ PF + o + 5 := by unfold brVal; split <;> omega
  simp only [rd32_eq, hm.mem, brM4]
  simp only [PMAX, NCAP, PF] at hpl hcap hv ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [rdm_wr4_other, rdm_wr4_same]

/-- After the slot loop: `brL5` and the arena step. -/
theorem br_fin (hm : BrMid cb pb rs R N o A K S m m4) (hz : ZeroB 16 (brBm pb o) (brEx pb o) (brSlots pb o))
    {m5 : M} (hl : BrLoop A K S m4 (brBm pb o) (brEx pb o) (PF + brR pb o + 2)
      (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) 0 m5) :
    twp P (Inp pub cb pb) (seqs brL5) m5 (fun m6 c =>
      BodyPostT cb pb rs R N o (brEnd pb o) A m6 (c + 1000 + 80 * popc 16 (brEx pb o))) := by
  have h := hm.inv
  have hf := hm.facts hz
  have hcap := hm.cap
  have hkl := h.klen
  simp only [NCAP] at hcap
  obtain ⟨Ak, hpm, hpr⟩ := hl.pop
  have hkle := hl.kle
  rw [show popc 0 (brEx pb o) = 0 from rfl, Nat.sub_zero] at hpm hpr hkle
  generalize hn : popc 16 (brEx pb o) = n at hpm hpr hkle
  have hS : S = S.take (S.length - n) ++ S.drop (S.length - n) := (List.take_append_drop _ _).symm
  generalize hS0 : S.take (S.length - n) = S0 at hS
  generalize hT : S.drop (S.length - n) = T at hS
  have hTl : T.length = n := by rw [← hT]; simp; try omega
  have hS0l : S0.length = S.length - n := by rw [← hS0]; simp; try omega
  rw [hS, ← hTl] at hpm hpr
  have hpm' := hpm.split
  have hp := hpr.split
  generalize hps : rdm m.mem (AR + 24 * A.length + 8) = ps
  have hfeq : (fun q => brSlotF (S0 ++ T) (brEx pb o) (PF + brR pb o + 2)
      (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) (S0.length + q)) = childSlot (brE pb o ps A K T) := by
    funext q
    rw [brSlotF_split _ _ _ _ _ (by rw [hTl, hn]), childSlot_brE]
  rw [hfeq] at hp
  have r3 := hl.r3
  rw [show popc 0 (brEx pb o) = 0 from rfl, Nat.sub_zero, hn] at r3
  have r7 := hl.r7
  rw [show popc 0 (brEx pb o) = 0 from rfl, Nat.sub_zero, hn] at r7
  obtain ⟨f1, f5, f8, f9, f10, f14, f15⟩ := hl.fr
  have hnS : n ≤ S.length := hkle
  have hSl : S.length = S0.length + T.length := by rw [hS]; simp
  refine twp_mono (brL5_twp (e := A.length) (kc := K.length + n) (by rw [f15, hm.r15]) (by rw [f14, hm.r14]) r3
    (by omega) (by rw [f8, hm.r8]) hm.cap) ?_
  rintro m6 c ⟨hm6, hr6, hc⟩
  let m5a : M := ⟨m5.regs, wr4 m5.mem C_KC (K.length + n)⟩
  have hC : C_KC + 4 ≤ AR ∨ (AR + 24 * A.length ≤ C_KC ∧ C_KC + 4 ≤ KL) := Or.inl (by decide)
  have hE : AR + 24 * A.length + 16 + 4 ≤ AR ∨
      (AR + 24 * A.length ≤ AR + 24 * A.length + 16 ∧ AR + 24 * A.length + 16 + 4 ≤ KL) :=
    Or.inr ⟨by omega, by simp only [AR, KL]; omega⟩
  have hAN : A.length ≤ NCAP := by simp only [NCAP]; omega
  have hKN : K.length + T.length ≤ NCAP := by simp only [NCAP]; omega
  have hpm6 : PopMem m6 A Ak K T T.length S0 :=
    (hpm'.wr4 (m' := m5a) rfl hC hAN hKN).wr4 hm6 hE hAN hKN
  have rd6 : ∀ b, (b + 4 ≤ C_KC ∨ C_KC + 4 ≤ b) →
      (b + 4 ≤ AR + 24 * A.length + 16 ∨ AR + 24 * A.length + 16 + 4 ≤ b) → rd32 m6 b = rd32 m5 b := by
    intro b h1 h2; rw [rd32_eq, rd32_eq, hm6, rdm_wr4_other _ _ _ _ h2, rdm_wr4_other _ _ _ _ h1]
  have rd5 : ∀ x, x ≤ 20 → rd32 m5 (AR + 24 * A.length + x) = rd32 m4 (AR + 24 * A.length + x) := by
    intro x hx; exact hl.out _ (by right; simp only [AR, KL]; omega)
  obtain ⟨e0, e4, e8, e12, e20⟩ := hm.e_reads
  have hrd : ∀ x, x ≤ 20 → (x + 4 ≤ 16 ∨ 20 ≤ x) → rd32 m6 (AR + 24 * A.length + x) = rd32 m4 (AR + 24 * A.length + x) := by
    intro x hx h16
    rw [rd6 _ (by right; simp only [C_KC, AR]; omega) (by omega), rd5 x hx]
  have hEm : EntMem m6 A.length (brE pb o ps A K T) := by
    simp only [EntMem, brE, brEnt]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hrd 0 (by omega) (by omega); simp only [Nat.add_zero] at this; rw [this, e0]
    · rw [hrd 4 (by omega) (by omega), e4]
    · rw [hrd 8 (by omega) (by omega), e8, hps]
    · rw [hrd 12 (by omega) (by omega), e12]
    · rw [rd32_eq, hm6, rdm_wr4_same _ _ _ (by simp only [NCAP] at *; omega)]
    · rw [hrd 20 (by omega) (by omega), e20]; rfl
  have g : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 11 → j ≠ 12 → j ≠ 13 → m6.regs j = m5.regs j := hr6
  have hnp := popc_sub 16 _ _ hm.sub
  have hge := brEnd_ge pb o
  obtain ⟨A', K', S0', hpre, hlen, hoo⟩ := br_step h hm.cap hm.hk hf hS (by rw [hTl, hn]) hp hpm6 hEm
    (by rw [rd32_eq, hm6, rdm_wr4_other _ _ _ _ (by left; simp only [C_KC, AR]; omega),
          rdm_wr4_same _ _ _ (by simp only [NCAP] at *; omega), hTl])
    (by rw [rd6 _ (by left; simp only [C_KC, C_NODES]; omega) (by left; simp only [C_NODES, AR]; omega),
          hl.out _ (by left; simp only [C_NODES, AR]; omega), hm.out _ (by left; simp only [C_NODES, AR]; omega)]
        exact h.hdr)
    (hm.frame.trans (hl.mf.trans (by
      rw [hm6]
      refine ((MFrame.refl _).wr4 _ _ (.inr rfl)).wr4 _ _ (.inl ⟨by omega, by simp only [AR, SH8, NCAP] at *; omega⟩))))
    (by rw [g 14 (by omega) (by omega) (by omega) (by omega) (by omega), f14, hm.r14, h.st.k8])
    (by rw [g 15 (by omega) (by omega) (by omega) (by omega) (by omega), f15, hm.r15, h.st.k1])
    (by rw [g 10 (by omega) (by omega) (by omega) (by omega) (by omega), f10, hm.r10])
    (by rw [g 9 (by omega) (by omega) (by omega) (by omega) (by omega), f9, hm.r9])
    (by rw [g 8 (by omega) (by omega) (by omega) (by omega) (by omega), f8, hm.r8])
    (by rw [g 7 (by omega) (by omega) (by omega) (by omega) (by omega), r7]; omega)
    (by rw [g 5 (by omega) (by omega) (by omega) (by omega) (by omega), f5, hm.r5, brE_entRev]; omega)
  refine ⟨A', K', S0', hpre, hlen, hoo, ?_⟩
  simp only [brNp] at hge
  omega

end

end ReexecNpai

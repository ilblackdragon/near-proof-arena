import ReexecNpai.Spec.RecAux22

/-!
# Record parse: branch records, the slot-loop invariant
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem popc_top : ∀ (i x : Nat), popc (i + 1) x = popc i x + bitOf x i
  | 0, x => by simp [popc, bitOf]
  | i + 1, x => by
    rw [popc_succ, popc_top i (x / 2), popc_succ, bitOf_succ]; omega

theorem popc_mono (x : Nat) : ∀ {i j : Nat}, i ≤ j → popc i x ≤ popc j x := by
  intro i j h
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · rw [popc_top]; have := ih (by omega); omega
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Slot address of the stack entry `j` popped by the slot loop. -/
def brSlotF (S : List Nat) (ex SL : Nat) (ks : List (Option (Option Bytes))) (j : Nat) : Nat :=
  SL + 32 * slotPos ks (j + popc 16 ex - S.length)

/-- The slot-loop invariant with `i` bits left to process (`r6 = i`). -/
structure BrLoop (A : List Ent) (K S : List Nat) (m0 : M) (bm ex SL : Nat)
    (ks : List (Option (Option Bytes))) (i : Nat) (m : M) : Prop where
  r6 : m.regs 6 = i
  hi : i ≤ 16
  r1 : m.regs 1 = bm + ex * 65536
  r2 : m.regs 2 = SL + 32 * popc i bm
  r3 : m.regs 3 = K.length + (popc 16 ex - popc i ex)
  r7 : m.regs 7 = S.length - (popc 16 ex - popc i ex)
  kle : popc 16 ex - popc i ex ≤ S.length
  fr : BrFrame m0 m
  pop : ∃ Ak, PopMem m A Ak K S (popc 16 ex - popc i ex) [] ∧
    PopRel A S (brSlotF S ex SL ks) Ak (popc 16 ex - popc i ex)
  out : ∀ b, (b + 4 ≤ AR ∨ (AR + 24 * A.length ≤ b ∧ b + 4 ≤ KL)) → rd32 m b = rd32 m0 b
  mf : MFrame m0.mem m.mem
  chk : ∀ j, i ≤ j → j < 16 → bitOf bm j = 1 → bitOf ex j = 1 →
    readMem m0.mem (SL + 32 * popc j bm) 32 = readMem m0.mem 136 32

/-- Static facts the slot loop relies on. -/
structure BrStatic (pb : Bytes) (A : List Ent) (K S : List Nat) (bm ex SL : Nat)
    (ks : List (Option (Option Bytes))) : Prop where
  bm16 : bm < 65536
  ex16 : ex < 65536
  sub : SubB 16 bm ex
  ks : ∀ i, i < 16 → bitOf ex i = 1 → slotPos ks (popc i ex) = popc i bm
  SLlo : PF ≤ SL
  SLhi : SL + 32 * popc 16 bm ≤ 13844304
  cap : A.length < NCAP
  klen : K.length + S.length = A.length
  slt : ∀ q (hq : q < S.length), S[q] < A.length
  inc : ∀ a b (ha : a < S.length) (hb : b < S.length), a < b → S[a] < S[b]

section
variable {pb : Bytes} {A : List Ent} {K S : List Nat} {m0 : M} {bm ex SL : Nat}
  {ks : List (Option (Option Bytes))}

theorem BrFrame.trans {m1 m2 m3 : M} (h1 : BrFrame m1 m2) (h2 : BrFrame m2 m3) : BrFrame m1 m3 := by
  obtain ⟨a1, a5, a8, a9, a10, a14, a15⟩ := h1
  obtain ⟨b1, b5, b8, b9, b10, b14, b15⟩ := h2
  exact ⟨b1.trans a1, b5.trans a5, b8.trans a8, b9.trans a9, b10.trans a10, b14.trans a14, b15.trans a15⟩

/-- An absent slot. -/
theorem BrLoop.none {i : Nat} {m m' : M} (st : BrStatic pb A K S bm ex SL ks)
    (h : BrLoop A K S m0 bm ex SL ks (i + 1) m) (hb : bitOf bm i = 0)
    (hm : m'.mem = m.mem) (h6 : m'.regs 6 = i) (hr : ∀ j, j ≠ 6 → j ≠ 11 → m'.regs j = m.regs j) :
    BrLoop A K S m0 bm ex SL ks i m' := by
  have he : bitOf ex i = 0 := by
    have := st.sub i (by have := h.hi; omega); have := bitOf_lt ex i; omega
  have pb' := popc_top i bm
  have pe := popc_top i ex
  rw [hb] at pb'; rw [he] at pe
  have hk : popc 16 ex - popc i ex = popc 16 ex - popc (i + 1) ex := by rw [pe, Nat.add_zero]
  obtain ⟨Ak, hpm, hpr⟩ := h.pop
  have rd : ∀ b, rd32 m' b = rd32 m b := fun b => by rw [rd32_eq, rd32_eq, hm]
  refine ⟨h6, by have := h.hi; omega, by rw [hr 1 (by omega) (by omega)]; exact h.r1,
    by rw [hr 2 (by omega) (by omega), h.r2, pb', Nat.add_zero],
    by rw [hr 3 (by omega) (by omega), h.r3, pe, Nat.add_zero],
    by rw [hr 7 (by omega) (by omega), h.r7, pe, Nat.add_zero],
    by rw [hk]; exact h.kle, ?_, ⟨Ak, ?_, by rw [hk]; exact hpr⟩,
    fun b hb' => by rw [rd]; exact h.out b hb', by rw [hm]; exact h.mf, fun j h1 h2 h3 h4 => ?_⟩
  · obtain ⟨a1, a5, a8, a9, a10, a14, a15⟩ := h.fr
    exact ⟨by rw [hr 1 (by omega) (by omega)]; exact a1, by rw [hr 5 (by omega) (by omega)]; exact a5,
      by rw [hr 8 (by omega) (by omega)]; exact a8, by rw [hr 9 (by omega) (by omega)]; exact a9,
      by rw [hr 10 (by omega) (by omega)]; exact a10, by rw [hr 14 (by omega) (by omega)]; exact a14,
      by rw [hr 15 (by omega) (by omega)]; exact a15⟩
  · rw [hk]; exact hpm.congr hm
  · rcases Nat.eq_or_lt_of_le h1 with h1 | h1
    · subst h1; rw [hb] at h3; omega
    · exact h.chk j (by omega) h2 h3 h4

/-- A present, unrevealed slot. -/
theorem BrLoop.hash {i : Nat} {m m' : M}
    (h : BrLoop A K S m0 bm ex SL ks (i + 1) m) (hb : bitOf bm i = 1) (he : bitOf ex i = 0)
    (hm : m'.mem = m.mem) (h6 : m'.regs 6 = i) (h2 : m'.regs 2 = m.regs 2 - 32)
    (hr : ∀ j, j ≠ 2 → j ≠ 6 → j ≠ 11 → m'.regs j = m.regs j) :
    BrLoop A K S m0 bm ex SL ks i m' := by
  have pb' := popc_top i bm
  have pe := popc_top i ex
  rw [hb] at pb'; rw [he] at pe
  have hk : popc 16 ex - popc i ex = popc 16 ex - popc (i + 1) ex := by rw [pe, Nat.add_zero]
  obtain ⟨Ak, hpm, hpr⟩ := h.pop
  have rd : ∀ b, rd32 m' b = rd32 m b := fun b => by rw [rd32_eq, rd32_eq, hm]
  refine ⟨h6, by have := h.hi; omega, by rw [hr 1 (by omega) (by omega) (by omega)]; exact h.r1,
    by rw [h2, h.r2, pb']; omega,
    by rw [hr 3 (by omega) (by omega) (by omega), h.r3, pe, Nat.add_zero],
    by rw [hr 7 (by omega) (by omega) (by omega), h.r7, pe, Nat.add_zero],
    by rw [hk]; exact h.kle, ?_, ⟨Ak, ?_, by rw [hk]; exact hpr⟩,
    fun b hb' => by rw [rd]; exact h.out b hb', by rw [hm]; exact h.mf, fun j h1 h2 h3 h4 => ?_⟩
  · obtain ⟨a1, a5, a8, a9, a10, a14, a15⟩ := h.fr
    exact ⟨by rw [hr 1 (by omega) (by omega) (by omega)]; exact a1, by rw [hr 5 (by omega) (by omega) (by omega)]; exact a5,
      by rw [hr 8 (by omega) (by omega) (by omega)]; exact a8, by rw [hr 9 (by omega) (by omega) (by omega)]; exact a9,
      by rw [hr 10 (by omega) (by omega) (by omega)]; exact a10,
      by rw [hr 14 (by omega) (by omega) (by omega)]; exact a14,
      by rw [hr 15 (by omega) (by omega) (by omega)]; exact a15⟩
  · rw [hk]; exact hpm.congr hm
  · rcases Nat.eq_or_lt_of_le h1 with h1 | h1
    · subst h1; rw [he] at h4; omega
    · exact h.chk j (by omega) h2 h3 h4

/-- A revealed child: pop, `pslot`, child list. -/
theorem BrLoop.popStep {i : Nat} {m m' : M} (st : BrStatic pb A K S bm ex SL ks)
    (h : BrLoop A K S m0 bm ex SL ks (i + 1) m) (hi : i < 16) (hb : bitOf bm i = 1) (he : bitOf ex i = 1)
    (hle : popc 16 ex - popc i ex ≤ S.length)
    (hz : readMem m.mem (m.regs 2 - 32) 32 = readMem m.mem 136 32)
    (hm : m'.mem = wr4 (wr4 m.mem (AR + 24 * rd32 m (STK + 4 * (m.regs 7 - 1)) + 8) (m.regs 2 - 32))
      (KL + 4 * m.regs 3) (rd32 m (STK + 4 * (m.regs 7 - 1))))
    (h6 : m'.regs 6 = i) (h2 : m'.regs 2 = m.regs 2 - 32) (h7 : m'.regs 7 = m.regs 7 - 1)
    (h3 : m'.regs 3 = m.regs 3 + 1) (hfr : BrFrame m m') :
    BrLoop A K S m0 bm ex SL ks i m' := by
  have pb' := popc_top i bm
  have pe := popc_top i ex
  rw [hb] at pb'; rw [he] at pe
  have hmono := popc_mono ex (show i + 1 ≤ 16 by omega)
  have hcap := st.cap
  have hkl := st.klen
  simp only [NCAP] at hcap
  obtain ⟨Ak, hpm, hpr⟩ := h.pop
  have r7 := h.r7
  have r3 := h.r3
  have r2 := h.r2
  have hkle := h.kle
  generalize hk : popc 16 ex - popc (i + 1) ex = k at hpm hpr r7 r3 hkle
  have hk' : popc 16 ex - popc i ex = k + 1 := by omega
  have hksl : k + 1 ≤ S.length := by omega
  have hidx : S.length - 1 - k < S.length := by omega
  have hc : rd32 m (STK + 4 * (m.regs 7 - 1)) = S[S.length - 1 - k] := by
    rw [r7, show S.length - k - 1 = S.length - 1 - k by omega,
      hpm.smem _ (by simp; omega), List.nil_append, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hidx]; rfl
  have hcA := st.slt _ hidx
  have hslot : m.regs 2 - 32 = brSlotF S ex SL ks (S.length - 1 - k) := by
    rw [r2, pb']
    simp only [brSlotF]
    rw [show S.length - 1 - k + popc 16 ex - S.length = popc i ex by omega, st.ks i hi he]
    omega
  rw [hc, r3, hslot] at hm
  have hsv : brSlotF S ex SL ks (S.length - 1 - k) < 4294967296 := by
    rw [← hslot, r2]; have := st.SLhi; have := popc_mono bm (show i + 1 ≤ 16 by omega); omega
  have hpm' := hpm.step (m' := m') (s := brSlotF S ex SL ks (S.length - 1 - k)) hksl st.slt
    hpr.len (by simp only [NCAP]; omega) (by simp only [NCAP]; omega) hsv hm
  have hpr' := hpr.step hksl st.slt st.inc
  have hout : ∀ b, (b + 4 ≤ AR ∨ (AR + 24 * A.length ≤ b ∧ b + 4 ≤ KL)) → rd32 m' b = rd32 m b := by
    intro b hb'
    rw [rd32_eq, rd32_eq, hm, rdm_wr4_other _ _ _ _ (by simp only [AR, KL] at *; omega),
      rdm_wr4_other _ _ _ _ (by simp only [AR, KL] at *; omega)]
  have hmf : MFrame m.mem m'.mem := by
    rw [hm]
    refine ((MFrame.refl _).wr4 _ _ ?_).wr4 _ _ ?_ <;> (left; simp only [AR, KL, SH8]; omega)
  refine ⟨h6, by omega, by rw [hfr.1]; exact h.r1, by rw [h2, r2, pb']; omega,
    by rw [h3, r3]; omega, by rw [h7, r7]; omega, by omega, h.fr.trans hfr,
    ⟨_, by rw [hk']; exact hpm', by rw [hk']; exact hpr'⟩,
    fun b hb' => by rw [hout b hb']; exact h.out b hb', h.mf.trans hmf, fun j h1 h2 h3 h4 => ?_⟩
  rcases Nat.eq_or_lt_of_le h1 with h1 | h1
  · subst h1
    have hlo := st.SLlo
    have hhi := st.SLhi
    have := popc_mono bm (show i + 1 ≤ 16 by omega)
    rw [r2, pb', show SL + 32 * (popc i bm + 1) - 32 = SL + 32 * popc i bm by omega] at hz
    rw [← h.mf.readMem (by right; right; simp only [PF, SH8] at *; omega),
      ← h.mf.readMem (show 136 + 32 ≤ C_KC ∨ _ from by left; simp only [C_KC]; omega)]
    exact hz
  · exact h.chk j (by omega) h2 h3 h4

end

end ReexecNpai

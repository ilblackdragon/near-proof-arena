import ReexecNpai.Spec.RecAux23

/-!
# Record parse: branch records, the slot loop
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes} {A : List Ent} {K S : List Nat} {m0 : M} {bm ex SL : Nat}
  {ks : List (Option (Option Bytes))}

/-- Loop potential. -/
def brPot (ex : Nat) (m : M) : Nat := 25 * m.regs 6 + 80 * popc (m.regs 6) ex

theorem BrLoop.k (h : BrLoop A K S m0 bm ex SL ks i m) (h14 : m0.regs 14 = 8) (h15 : m0.regs 15 = 1) :
    m.regs 14 = 8 ∧ m.regs 15 = 1 := by
  obtain ⟨-, -, -, -, -, a14, a15⟩ := h.fr
  exact ⟨by rw [a14, h14], by rw [a15, h15]⟩

/-- Facts for a pop at bit `i`. -/
theorem BrLoop.popFacts {i : Nat} {m : M} (st : BrStatic pb A K S bm ex SL ks)
    (h : BrLoop A K S m0 bm ex SL ks (i + 1) m) (hb : bitOf bm i = 1) (he : bitOf ex i = 1) :
    32 ≤ m.regs 2 ∧ m.regs 2 ≤ 13844304 ∧ m.regs 7 ≤ NCAP ∧ m.regs 3 < NCAP ∧
      (1 ≤ m.regs 7 → rd32 m (STK + 4 * (m.regs 7 - 1)) < NCAP) := by
  have pb' := popc_top i bm
  have pe := popc_top i ex
  rw [hb] at pb'; rw [he] at pe
  have hmb := popc_mono bm (show i + 1 ≤ 16 by have := h.hi; omega)
  have hme := popc_mono ex (show i + 1 ≤ 16 by have := h.hi; omega)
  have hcap := st.cap
  have hkl := st.klen
  have hlo := st.SLlo
  have hhi := st.SLhi
  have hkle := h.kle
  simp only [NCAP, PF] at hcap hlo
  obtain ⟨Ak, hpm, -⟩ := h.pop
  refine ⟨by rw [h.r2]; omega, by rw [h.r2]; omega, by rw [h.r7]; simp only [NCAP]; omega,
    by rw [h.r3]; simp only [NCAP]; omega, fun hsp => ?_⟩
  have r7 := h.r7
  have hidx : m.regs 7 - 1 < S.length := by omega
  rw [hpm.smem _ (by simp; omega), List.nil_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hidx]
  have := st.slt _ hidx
  simp only [Option.getD_some, NCAP]; omega

/-- One iteration (total correctness). -/
theorem br_iter_twp {i : Nat} {m : M} (st : BrStatic pb A K S bm ex SL ks)
    (h14 : m0.regs 14 = 8) (h15 : m0.regs 15 = 1)
    (hz : ∀ j, j < 16 → bitOf bm j = 1 → bitOf ex j = 1 →
      readMem m0.mem (SL + 32 * popc j bm) 32 = readMem m0.mem 136 32)
    (hn : popc 16 ex ≤ S.length) (h : BrLoop A K S m0 bm ex SL ks (i + 1) m) :
    twp P (Inp pub cb pb) brBody m (fun m' c => BrLoop A K S m0 bm ex SL ks i m' ∧
      c + 2 + brPot ex m' ≤ brPot ex m) := by
  obtain ⟨k8, k1⟩ := h.k h14 h15
  have hi : i < 16 := by have := h.hi; omega
  have pb' := popc_top i bm
  have pe := popc_top i ex
  have hbl := bitOf_lt bm i
  have hel := bitOf_lt ex i
  have pot : brPot ex m = 25 * (i + 1) + 80 * popc (i + 1) ex := by simp only [brPot, h.r6]
  rcases Nat.lt_or_ge (bitOf bm i) 1 with hb | hb
  · have hb : bitOf bm i = 0 := by omega
    have he : bitOf ex i = 0 := by have := st.sub i hi; omega
    refine twp_mono (brBody_none k1 k8 h.r6 hi h.r1 st.bm16 st.ex16 hb) ?_
    rintro m' c ⟨hm, h6, hr, hc⟩
    refine ⟨h.none st hb hm h6 hr, ?_⟩
    rw [show brPot ex m' = 25 * i + 80 * popc i ex by simp only [brPot, h6], pot, pe, he]; omega
  · have hb : bitOf bm i = 1 := by omega
    rcases Nat.lt_or_ge (bitOf ex i) 1 with he | he
    · have he : bitOf ex i = 0 := by omega
      have hmb := popc_mono bm (show i + 1 ≤ 16 by omega)
      have hhi := st.SLhi
      have hlo := st.SLlo
      simp only [PF] at hlo
      refine twp_mono (brBody_hash k1 k8 h.r6 hi h.r1 st.bm16 st.ex16 hb he rfl
        (by rw [h.r2, pb', hb]; omega) (by rw [h.r2]; omega)) ?_
      rintro m' c ⟨hm, h6, h2, hr, hc⟩
      refine ⟨h.hash hb he hm h6 h2 hr, ?_⟩
      rw [show brPot ex m' = 25 * i + 80 * popc i ex by simp only [brPot, h6], pot, pe, he]; omega
    · have he : bitOf ex i = 1 := by omega
      obtain ⟨p1, p2, p7, p3, pc⟩ := h.popFacts st hb he
      have pe' := pe; rw [he] at pe'
      have hme := popc_mono ex (show i + 1 ≤ 16 by omega)
      have hsp : 1 ≤ m.regs 7 := by have := h.r7; have := h.kle; omega
      have hle : popc 16 ex - popc i ex ≤ S.length := by omega
      have hzm : readMem m.mem (m.regs 2 - 32) 32 = readMem m.mem 136 32 := by
        have hhi := st.SLhi
        have hlo := st.SLlo
        have hmb := popc_mono bm (show i + 1 ≤ 16 by omega)
        have pb'' := pb'; rw [hb] at pb''
        rw [h.r2, pb'', show SL + 32 * (popc i bm + 1) - 32 = SL + 32 * popc i bm by omega,
          h.mf.readMem (by right; right; simp only [PF, SH8] at *; omega),
          h.mf.readMem (show 136 + 32 ≤ C_KC ∨ _ from by left; simp only [C_KC]; omega)]
        exact hz i hi hb he
      refine twp_mono (brBody_pop k1 k8 h.r6 hi h.r1 st.bm16 st.ex16 hb he rfl p1 p2 rfl hsp p7 rfl p3 rfl
        (pc hsp) hzm) ?_
      rintro m' c ⟨hm, h6, h2, h7, h3, hfr, hc⟩
      refine ⟨h.popStep st hi hb he hle hzm hm h6 h2 h7 h3 hfr, ?_⟩
      rw [show brPot ex m' = 25 * i + 80 * popc i ex by simp only [brPot, h6], pot, pe']; omega

/-- One iteration (partial correctness). -/
theorem br_iter_wp {i : Nat} {m : M} (st : BrStatic pb A K S bm ex SL ks)
    (h14 : m0.regs 14 = 8) (h15 : m0.regs 15 = 1) (h : BrLoop A K S m0 bm ex SL ks (i + 1) m) :
    wp P (Inp pub cb pb) brBody m (fun m' => BrLoop A K S m0 bm ex SL ks i m') := by
  obtain ⟨k8, k1⟩ := h.k h14 h15
  have hi : i < 16 := by have := h.hi; omega
  have pb' := popc_top i bm
  have pe := popc_top i ex
  have hbl := bitOf_lt bm i
  have hel := bitOf_lt ex i
  rcases Nat.lt_or_ge (bitOf bm i) 1 with hb | hb
  · have hb : bitOf bm i = 0 := by omega
    exact wp_of_spec (brBody_none k1 k8 h.r6 hi h.r1 st.bm16 st.ex16 hb)
      (fun m' c ⟨hm, h6, hr, _⟩ => h.none st hb hm h6 hr)
  · have hb : bitOf bm i = 1 := by omega
    have hmb := popc_mono bm (show i + 1 ≤ 16 by omega)
    have hhi := st.SLhi
    have hlo := st.SLlo
    simp only [PF] at hlo
    rcases Nat.lt_or_ge (bitOf ex i) 1 with he | he
    · have he : bitOf ex i = 0 := by omega
      exact wp_of_spec (brBody_hash k1 k8 h.r6 hi h.r1 st.bm16 st.ex16 hb he rfl
        (by rw [h.r2, pb', hb]; omega) (by rw [h.r2]; omega))
        (fun m' c ⟨hm, h6, h2, hr, _⟩ => h.hash hb he hm h6 h2 hr)
    · have he : bitOf ex i = 1 := by omega
      obtain ⟨p1, p2, p7, p3, pc⟩ := h.popFacts st hb he
      have pe' := pe; rw [he] at pe'
      have hme := popc_mono ex (show i + 1 ≤ 16 by omega)
      refine wp_mono (brBody_pop_wp k1 k8 h.r6 hi h.r1 st.bm16 st.ex16 hb he rfl p1 p2 rfl p7 rfl p3 rfl pc) ?_
      rintro m' ⟨hzm, hsp, hm, h6, h2, h7, h3, hfr⟩
      have hle : popc 16 ex - popc i ex ≤ S.length := by have := h.r7; have := h.kle; omega
      exact h.popStep st hi hb he hle hzm hm h6 h2 h7 h3 hfr

theorem br_loop_twp {m : M} (st : BrStatic pb A K S bm ex SL ks)
    (h14 : m0.regs 14 = 8) (h15 : m0.regs 15 = 1)
    (hz : ∀ j, j < 16 → bitOf bm j = 1 → bitOf ex j = 1 →
      readMem m0.mem (SL + 32 * popc j bm) 32 = readMem m0.mem 136 32)
    (hn : popc 16 ex ≤ S.length) (h : BrLoop A K S m0 bm ex SL ks 16 m) :
    twp P (Inp pub cb pb) (.loop 6 brBody) m (fun m' c => BrLoop A K S m0 bm ex SL ks 0 m' ∧
      c ≤ 25 * 16 + 80 * popc 16 ex + 1) := by
  refine twp_loop (fun m => BrLoop A K S m0 bm ex SL ks (m.regs 6) m) (brPot ex) (by rw [h.r6]; exact h)
    (fun m hI h6 => ?_) (fun m' c hI h6 hc => ?_)
  · obtain ⟨i, hi⟩ : ∃ i, m.regs 6 = i + 1 := ⟨m.regs 6 - 1, by omega⟩
    rw [hi] at hI
    refine twp_mono (br_iter_twp st h14 h15 hz hn hI) ?_
    rintro m' c ⟨h', hc⟩
    exact ⟨by rw [h'.r6]; exact h', hc⟩
  · rw [h6] at hI
    refine ⟨hI, ?_⟩
    simp only [brPot, h.r6] at hc
    omega

theorem br_loop_wp {m : M} (st : BrStatic pb A K S bm ex SL ks)
    (h14 : m0.regs 14 = 8) (h15 : m0.regs 15 = 1) (h : BrLoop A K S m0 bm ex SL ks 16 m) :
    wp P (Inp pub cb pb) (.loop 6 brBody) m (fun m' => BrLoop A K S m0 bm ex SL ks 0 m') := by
  refine wp_loop (fun m => BrLoop A K S m0 bm ex SL ks (m.regs 6) m) (by rw [h.r6]; exact h)
    (fun m hI h6 => ?_) (fun m' hI h6 => by rw [h6] at hI; exact hI)
  obtain ⟨i, hi⟩ : ∃ i, m.regs 6 = i + 1 := ⟨m.regs 6 - 1, by omega⟩
  rw [hi] at hI
  refine wp_mono (br_iter_wp st h14 h15 hI) ?_
  intro m' h'
  rw [h'.r6]; exact h'

end

end ReexecNpai

import ReexecNpai.Spec.RecAux3

/-!
# Record parse: the state before the push, `pPush`, and the kind dispatch
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- State after a record body, before `pPush`: like `ParseInv` with the new
entry (the last one) not yet on the stack `S0` and `r8` not yet incremented. -/
structure PreInv (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (K : List Nat)
    (S0 : List Nat) (m : M) : Prop where
  st : RcptsSt cb pb rs R m
  rP : m.regs 10 = PF + o
  rE : m.regs 9 = PF + pb.length
  re : m.regs 8 + 1 = A.length
  rsp : m.regs 7 = S0.length
  rrv : m.regs 5 = revSum pb A
  kc : rd32 m C_KC = K.length
  hdr : rd32 m C_NODES = N
  oR : R + 4 ≤ o
  ole : o ≤ pb.length
  cap : A.length ≤ NCAP
  dec : decRecs A.length [] (pb.drop (R + 4)) =
    some (((S0 ++ [A.length - 1]).map (treeAt A K (vals0 pb A))).reverse, pb.drop o)
  wf : ∀ j, j < A.length → NodeWF pb A K j
  first : 0 < A.length → (A.getD 0 default).rst = PF + R + 4
  contig : ∀ j, j + 1 < A.length →
    (A.getD j default).pre + (A.getD j default).preLen = (A.getD (j + 1) default).rst
  last : (0 < A.length → (A.getD (A.length - 1) default).pre + (A.getD (A.length - 1) default).preLen = PF + o) ∧
    (A.length = 0 → o = R + 4)
  stack : StackOK A (S0 ++ [A.length - 1])
  amem : ∀ j (h : j < A.length), EntMem m j A[j]
  kmem : ∀ i (h : i < K.length), rd32 m (KL + 4 * i) = K[i]
  krange : ∀ j (h : j < A.length), A[j].kid + nKids A[j].nf ≤ K.length
  smem : ∀ i (h : i < S0.length), rd32 m (STK + 4 * i) = S0[i]
  klen : K.length + S0.length + 1 = A.length

theorem pPush_exe {pub cb pb : Bytes} {m : M} {sp e : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h7 : m.regs 7 = sp) (h8 : m.regs 8 = e) (hsp : sp < NCAP) (he : e < NCAP) :
    twp P (Inp pub cb pb) (.seq pPush (LTU 4 10 9)) m (fun m' c => m'.mem = wr4 m.mem (STK + 4 * sp) e ∧
      m'.regs 7 = sp + 1 ∧ m'.regs 8 = e + 1 ∧ m'.regs 4 = (if m.regs 10 < m.regs 9 then 1 else 0) ∧
      (∀ j, j ≠ 4 → j ≠ 7 → j ≠ 8 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) ∧ c = 17) := by
  simp only [NCAP] at hsp he
  simp only [pPush]
  rec_auto [hk1, hk8, h7, h8]
  refine ⟨by rw [wr4, show 7753384 + 4 * sp = sp * 4 + 7753384 by omega], ?_⟩
  intro j h1 h2 h3 h4 h5
  simp [h1, h2, h3, h4, h5]

theorem pPush_wp {pub cb pb : Bytes} {m : M} {sp e : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h7 : m.regs 7 = sp) (h8 : m.regs 8 = e) (hsp : sp < NCAP) (he : e < NCAP) {Q : M → Prop}
    (hq : ∀ m', m'.mem = wr4 m.mem (STK + 4 * sp) e → m'.regs 7 = sp + 1 → m'.regs 8 = e + 1 →
      m'.regs 4 = (if m.regs 10 < m.regs 9 then 1 else 0) →
      (∀ j, j ≠ 4 → j ≠ 7 → j ≠ 8 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) → Q m') :
    wp P (Inp pub cb pb) (.seq pPush (LTU 4 10 9)) m Q := by
  exact wp_of_spec (pPush_exe hk1 hk8 h7 h8 hsp he) (fun m' _ ⟨a, b, c, d, e, _⟩ => hq m' a b c d e)

/-- `pPush` turns the pre-push state into the loop invariant. -/
theorem preInv_push {cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S0 : List Nat}
    {m m' : M} (h : PreInv cb pb rs R N o A K S0 m) (hm : m'.mem = wr4 m.mem (STK + 4 * S0.length) (A.length - 1))
    (h7 : m'.regs 7 = S0.length + 1) (h8 : m'.regs 8 = A.length)
    (hr : ∀ j, j ≠ 4 → j ≠ 7 → j ≠ 8 → j ≠ 12 → j ≠ 13 → m'.regs j = m.regs j) :
    ParseInv cb pb rs R N o A K (S0 ++ [A.length - 1]) m' := by
  have hcap := h.cap
  have hkl := h.klen
  simp only [NCAP] at hcap
  have hS : STK + 4 * S0.length + 4 ≤ SH8 := by simp only [STK, SH8]; omega
  have hf : MFrame m.mem m'.mem := by
    rw [hm]; exact (MFrame.refl _).wr4 _ _ (.inl ⟨by simp only [STK, AR]; omega, hS⟩)
  have hrd : ∀ b, (b + 4 ≤ STK + 4 * S0.length ∨ STK + 4 * S0.length + 4 ≤ b) → rd32 m' b = rd32 m b := by
    intro b hb; rw [rd32_eq, rd32_eq, hm, rdm_wr4_other _ _ _ _ hb]
  refine ⟨rcpts_frame h.st (hr 14 (by omega) (by omega) (by omega) (by omega) (by omega))
      (hr 15 (by omega) (by omega) (by omega) (by omega) (by omega)) hf,
    by rw [hr 10 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rP,
    by rw [hr 9 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rE,
    h8, by rw [h7]; simp,
    by rw [hr 5 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rrv,
    by rw [hrd _ (by simp only [C_KC, STK]; omega)]; exact h.kc,
    by rw [hrd _ (by simp only [C_NODES, STK]; omega)]; exact h.hdr,
    h.oR, h.ole, h.cap, h.dec, h.wf, h.first, h.contig, h.last, h.stack, ?_, ?_, h.krange, ?_, by simp; omega⟩
  · intro j hj
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.amem j hj
    have hA : AR + 24 * j + 24 ≤ STK := by simp only [AR, STK, NCAP] at *; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [hrd _ (by omega)]; assumption)
  · intro i hi
    have hk : K.length ≤ 272728 := by omega
    rw [hrd _ (by simp only [KL, STK]; omega)]; exact h.kmem i hi
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i S0.length with hi' | hi'
    · rw [hrd _ (by omega), List.getElem_append_left hi']; exact h.smem i hi'
    · have : i = S0.length := by omega
      subst this
      rw [List.getElem_append_right (Nat.le_refl _), rd32_eq, hm, rdm_wr4_same _ _ _ (by omega)]
      simp

end ReexecNpai

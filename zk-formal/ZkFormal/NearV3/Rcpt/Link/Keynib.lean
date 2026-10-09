import ZkFormal.NearV3.Rcpt.Extract.RcptView

/-!
# ZkFormal.NearV3.Rcpt.Link.Keynib — `KeynibOk` for the receipt side's `KEYNIB` sends

Lane v3-trie's `KeynibOk` needs every provider message `(w, t, sym, last)` to have
`sym < 16` or `sym = END` (and `sym < P`).  The account walk's symbols are nibbles of
`[0] ‖ receiver`, the access-key walk's of `[2] ‖ signer ‖ [2] ‖ kt ‖ pk`, both followed by
`END`; with byte-valued strings every symbol qualifies (`rcpt_keynib_syms`).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem nib_syms (l : List Nat) (hl : ∀ y ∈ l, y < 256) :
    ∀ y ∈ l.flatMap (fun ch => [ch / 16, ch % 16]) ++ [SYM_END], y < 16 ∨ y = SYM_END := by
  intro y hy
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hy
  rcases hy with ⟨ch, hch, rfl | rfl⟩ | rfl
  · have := hl ch hch; left; omega
  · left; omega
  · right; rfl

theorem keyMsgs_syms (w : Nat) (syms : List Nat) (h : ∀ y ∈ syms, y < 16 ∨ y = SYM_END) :
    ∀ m ∈ RcptE.keyMsgs w syms, m.getD 2 0 < P ∧ (m.getD 2 0 < 16 ∨ m.getD 2 0 = SYM_END) := by
  intro m hm
  simp only [RcptE.keyMsgs, List.mem_map, List.mem_range] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  have hy := h (syms.getD t 0) (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, List.getElem_mem])
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨?_, hy⟩
  have hP : (16 : Nat) < P := by unfold P; omega
  rcases hy with hy | hy
  · omega
  · rw [hy]; unfold SYM_END; omega

/-- **Symbols of a receipt's `KEYNIB` sends.** -/
theorem rcpt_keynib_syms (x : RcptE) (r : Nat) (hv : ∀ y ∈ x.v, y < 256)
    (hak : x.ee = true → (∀ y ∈ x.s, y < 256) ∧ (∀ y ∈ x.pk, y < 256) ∧ x.kt < 256) :
    ∀ m ∈ RcptE.keyMsgs r x.keySyms ++ (if x.ee then RcptE.keyMsgs (W_AK + r) x.akSyms else []),
      m.getD 2 0 < P ∧ (m.getD 2 0 < 16 ∨ m.getD 2 0 = SYM_END) := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · refine keyMsgs_syms r _ (fun y hy => ?_) m hm
    have e : x.keySyms = ([0] ++ x.v).flatMap (fun ch => [ch / 16, ch % 16]) ++ [SYM_END] := by
      simp [RcptV.keySyms]
    rw [e] at hy
    exact nib_syms _ (by intro y hy; simp at hy; rcases hy with rfl | hy; omega; exact hv y hy) y hy
  · by_cases he : x.ee = true
    · rw [if_pos he] at hm
      obtain ⟨hs, hpk, hkt⟩ := hak he
      refine keyMsgs_syms _ _ (fun y hy => nib_syms _ ?_ y hy) m hm
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      rcases hy with (((rfl | hy) | rfl) | rfl) | hy
      · omega
      · exact hs y hy
      · omega
      · exact hkt
      · exact hpk y hy
    · simp [he] at hm

end ZkFormal.NearV3

import ReexecNpai.Spec.RecAux9

/-!
# Record parse: popping revealed children (shared by extensions and branches)

A record with revealed children pops them off the stack, top first: the child
`T[q]` gets `pslot := f q` and is appended to the child list `KL`. `PopRel`
tracks the arena after `k` pops, `PopMem` the memory.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- Set the `pslot` of entry `c`. -/
def setPs (A : List Ent) (c s : Nat) : List Ent := A.set c { A.getD c default with pslot := s }

theorem setPs_length (A : List Ent) (c s : Nat) : (setPs A c s).length = A.length := by
  simp [setPs]

theorem setPs_getD (A : List Ent) (c s j : Nat) (hc : c < A.length) :
    (setPs A c s).getD j default = if j = c then { A.getD c default with pslot := s } else A.getD j default := by
  simp only [setPs, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : c = j
  · subst h; simp [hc]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Arena after popping the top `k` children of `T` (`T[n-1]`, …, `T[n-k]`). -/
structure PopRel (A : List Ent) (T : List Nat) (f : Nat → Nat) (Ak : List Ent) (k : Nat) : Prop where
  len : Ak.length = A.length
  same : ∀ j (h : j < A.length), SameBut (Ak.getD j default) A[j]
  other : ∀ j (h : j < A.length), (∀ q (hq : q < T.length), T.length - k ≤ q → T[q] ≠ j) →
    (Ak.getD j default).pslot = A[j].pslot
  slot : ∀ q (hq : q < T.length), T.length - k ≤ q → (Ak.getD T[q] default).pslot = f q

theorem PopRel.zero (A : List Ent) (T : List Nat) (f : Nat → Nat) : PopRel A T f A 0 := by
  refine ⟨rfl, fun j hj => ?_, fun j hj _ => ?_, fun q hq h => absurd h (by omega)⟩
  · rw [getD_eq_get hj]; rfl
  · rw [getD_eq_get hj]

theorem PopRel.step {A : List Ent} {T : List Nat} {f : Nat → Nat} {Ak : List Ent} {k : Nat}
    (h : PopRel A T f Ak k) (hk : k < T.length) (hTA : ∀ q (hq : q < T.length), T[q] < A.length)
    (hinc : ∀ a b (ha : a < T.length) (hb : b < T.length), a < b → T[a] < T[b]) :
    PopRel A T f (setPs Ak T[T.length - 1 - k] (f (T.length - 1 - k))) (k + 1) := by
  have hc := hTA (T.length - 1 - k) (by omega)
  have hcA : T[T.length - 1 - k] < Ak.length := by rw [h.len]; exact hc
  refine ⟨by rw [setPs_length, h.len], fun j hj => ?_, fun j hj hn => ?_, fun q hq hq' => ?_⟩
  · rw [setPs_getD _ _ _ _ hcA]
    split
    · rename_i hjc; subst hjc
      have := h.same _ hj
      simp only [SameBut] at this ⊢
      rw [← this]
    · exact h.same j hj
  · rw [setPs_getD _ _ _ _ hcA, if_neg (fun e => hn _ (by omega) (by omega) e.symm)]
    exact h.other j hj (fun q hq hq' => hn q hq (by omega))
  · rw [setPs_getD _ _ _ _ hcA]
    by_cases hq0 : q = T.length - 1 - k
    · subst hq0; simp
    · have hne : T[q] ≠ T[T.length - 1 - k] := by
        rcases Nat.lt_or_gt_of_ne hq0 with h1 | h1
        · exact Nat.ne_of_lt (hinc _ _ hq (by omega) h1)
        · exact Nat.ne_of_gt (hinc _ _ (by omega) hq h1)
      rw [if_neg hne]
      exact h.slot q hq (by omega)

/-- Memory after popping the top `k` children of `T` off `S0 ++ T`. -/
structure PopMem (m : M) (A Ak : List Ent) (K T : List Nat) (k : Nat) (S0 : List Nat) : Prop where
  amem : ∀ j (h : j < A.length), EntMem m j (Ak.getD j default)
  kmem : ∀ i, i < K.length + k → rd32 m (KL + 4 * i) = (K ++ (T.drop (T.length - k)).reverse).getD i 0
  smem : ∀ i, i < S0.length + (T.length - k) → rd32 m (STK + 4 * i) = (S0 ++ T).getD i 0

theorem PopMem.frame {m m' : M} {A Ak : List Ent} {K T : List Nat} {k : Nat} {S0 : List Nat}
    (h : PopMem m A Ak K T k S0)
    (hr : ∀ b, ((AR ≤ b ∧ b + 4 ≤ AR + 24 * A.length) ∨ b ≥ KL) → (b < KL + 4 * (K.length + k) ∨ b ≥ STK) →
      rd32 m' b = rd32 m b) (hA : A.length ≤ NCAP) (hK : K.length + k ≤ NCAP) :
    PopMem m' A Ak K T k S0 := by
  simp only [NCAP] at hA hK
  refine ⟨fun j hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.amem j hj
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [hr _ (by left; omega) (by left; simp only [AR, KL] at *; omega)]; assumption)
  · rw [hr _ (by right; simp only [KL]; omega) (by left; omega)]; exact h.kmem i hi
  · rw [hr _ (by right; simp only [KL, STK]; omega) (by right; simp only [STK]; omega)]; exact h.smem i hi

theorem PopMem.init {m : M} {A : List Ent} {K T S0 : List Nat}
    (hamem : ∀ j (h : j < A.length), EntMem m j A[j])
    (hkmem : ∀ i (h : i < K.length), rd32 m (KL + 4 * i) = K[i])
    (hsmem : ∀ i (h : i < (S0 ++ T).length), rd32 m (STK + 4 * i) = (S0 ++ T)[i]) :
    PopMem m A A K T 0 S0 := by
  refine ⟨fun j hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [getD_eq_get hj]; exact hamem j hj
  · simp only [Nat.sub_zero, List.drop_length, List.reverse_nil, List.append_nil, Nat.add_zero] at hi ⊢
    rw [hkmem i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  · simp only [Nat.sub_zero] at hi
    have hi' : i < (S0 ++ T).length := by simp; omega
    rw [hsmem i hi', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl

theorem rd32_wr4_wr4_other {M0 : Nat → UInt8} {m : M} {a1 v1 a2 v2 b : Nat}
    (hm : m.mem = wr4 (wr4 M0 a1 v1) a2 v2) (h1 : b + 4 ≤ a1 ∨ a1 + 4 ≤ b) (h2 : b + 4 ≤ a2 ∨ a2 + 4 ≤ b) :
    rd32 m b = rdm M0 b := by
  rw [rd32_eq, hm, rdm_wr4_other _ _ _ _ h2, rdm_wr4_other _ _ _ _ h1]

/-- One pop: `pslot[c] := s`, `KL[K.length + k] := c`. -/
theorem PopMem.step {m m' : M} {A Ak : List Ent} {K T : List Nat} {k : Nat} {S0 : List Nat} {s : Nat}
    (h : PopMem m A Ak K T k S0) (hk : k < T.length) (hTA : ∀ q (hq : q < T.length), T[q] < A.length)
    (hAk : Ak.length = A.length) (hA : A.length ≤ NCAP) (hK : K.length + k < NCAP)
    (hs : s < 4294967296)
    (hm : m'.mem = wr4 (wr4 m.mem (AR + 24 * T[T.length - 1 - k] + 8) s) (KL + 4 * (K.length + k))
      T[T.length - 1 - k]) :
    PopMem m' A (setPs Ak T[T.length - 1 - k] s) K T (k + 1) S0 := by
  have hc := hTA (T.length - 1 - k) (by omega)
  generalize hcd : T[T.length - 1 - k] = c at hc hm
  have hcA : c < Ak.length := by rw [hAk]; exact hc
  simp only [NCAP] at hA hK
  have hcv : c < 4294967296 := by omega
  refine ⟨fun j hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [setPs_getD _ _ _ _ hcA]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.amem j hj
    have hKL : AR + 24 * j + 24 ≤ KL + 4 * (K.length + k) := by simp only [AR, KL]; omega
    split
    · rename_i hjc; subst hjc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rd32_wr4_wr4_other hm (by omega) (by omega), ← rd32_eq]; exact a1
      · rw [rd32_wr4_wr4_other hm (by omega) (by omega), ← rd32_eq]; exact a2
      · rw [rd32_eq, hm, rdm_wr4_other _ _ _ _ (by omega), rdm_wr4_same _ _ _ hs]
      · rw [rd32_wr4_wr4_other hm (by omega) (by omega), ← rd32_eq]; exact a4
      · rw [rd32_wr4_wr4_other hm (by omega) (by omega), ← rd32_eq]; exact a5
      · rw [rd32_wr4_wr4_other hm (by omega) (by omega), ← rd32_eq]; exact a6
    · rename_i hjc
      have hd : 24 * j + 24 ≤ 24 * c ∨ 24 * c + 24 ≤ 24 * j := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (rw [rd32_wr4_wr4_other hm (by omega) (by omega), ← rd32_eq]; assumption)
  · have hdrop : T.drop (T.length - (k + 1)) = c :: T.drop (T.length - k) := by
      rw [show T.length - (k + 1) = T.length - 1 - k by omega, List.drop_eq_getElem_cons (by omega), hcd,
        show T.length - 1 - k + 1 = T.length - k by omega]
    rw [hdrop, List.reverse_cons, ← List.append_assoc]
    have hlen : (K ++ (T.drop (T.length - k)).reverse).length = K.length + k := by
      simp; omega
    rcases Nat.lt_or_ge i (K.length + k) with hi' | hi'
    · have d1 : KL + 4 * i + 4 ≤ AR + 24 * c + 8 ∨ AR + 24 * c + 8 + 4 ≤ KL + 4 * i := by
        simp only [AR, KL]; omega
      have d2 : KL + 4 * i + 4 ≤ KL + 4 * (K.length + k) ∨ KL + 4 * (K.length + k) + 4 ≤ KL + 4 * i := by omega
      rw [rd32_wr4_wr4_other hm d1 d2, ← rd32_eq, h.kmem i hi', List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (l₂ := [c]) (by rw [hlen]; exact hi')]
    · have hi2 : i = K.length + k := by omega
      subst hi2
      rw [rd32_eq, hm, rdm_wr4_same _ _ _ hcv, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hlen]
      simp
  · have hST : STK ≥ KL + 4 * (K.length + k) + 4 := by simp only [STK, KL]; omega
    rw [rd32_wr4_wr4_other hm (by simp only [AR, STK]; omega) (by omega), ← rd32_eq]
    exact h.smem i (by omega)

theorem PopRel.full {A : List Ent} {T : List Nat} {f : Nat → Nat} {An : List Ent}
    (h : PopRel A T f An T.length) :
    (∀ j (h : j < A.length), j ∉ T → (An.getD j default).pslot = A[j].pslot) ∧
    (∀ q (hq : q < T.length), (An.getD T[q] default).pslot = f q) := by
  refine ⟨fun j hj hn => h.other j hj (fun q hq _ e => hn (e ▸ List.getElem_mem hq)),
    fun q hq => h.slot q hq (by omega)⟩

theorem PopMem.full {m : M} {A An : List Ent} {K T : List Nat} {S0 : List Nat}
    (h : PopMem m A An K T T.length S0) :
    (∀ i, i < K.length + T.length → rd32 m (KL + 4 * i) = (K ++ T.reverse).getD i 0) ∧
    (∀ i (hi : i < S0.length), rd32 m (STK + 4 * i) = S0[i]) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h.kmem i hi; simpa using this
  · rw [h.smem i (by omega), List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
      List.getElem?_eq_getElem hi]; rfl

theorem stack_succ {pb : Bytes} {A : List Ent} {K S : List Nat} (hwf : ∀ j, j < A.length → NodeWF pb A K j)
    (hs : StackOK A S) (i : Nat) (h : i + 1 < S.length) : S[i] < S[i + 1] := by
  have hlo := hs.2.2.2.1 i h
  have hlt := hs.2.1 (i + 1) h
  obtain ⟨e, he, -, -, -, -, -, -, -, hle, -⟩ := hwf _ hlt
  rw [getD_eq_of he] at hlo
  omega

theorem stack_inc {pb : Bytes} {A : List Ent} {K S : List Nat} (hwf : ∀ j, j < A.length → NodeWF pb A K j)
    (hs : StackOK A S) : ∀ a b (ha : a < S.length) (hb : b < S.length), a < b → S[a] < S[b] := by
  intro a b ha hb hab
  induction b with
  | zero => omega
  | succ b ih =>
    have := stack_succ hwf hs b hb
    rcases Nat.lt_or_ge a b with h1 | h1
    · exact Nat.lt_trans (ih (by omega) h1) this
    · have : a = b := by omega
      subst this; exact this

theorem suffix_inc {S0 T : List Nat} (h : ∀ a b (ha : a < (S0 ++ T).length) (hb : b < (S0 ++ T).length), a < b →
    (S0 ++ T)[a] < (S0 ++ T)[b]) : ∀ a b (ha : a < T.length) (hb : b < T.length), a < b → T[a] < T[b] := by
  intro a b ha hb hab
  have := h (S0.length + a) (S0.length + b) (by simp; omega) (by simp; omega) (by omega)
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)] at this
  simpa using this

theorem suffix_lt {A : List Ent} {S0 T : List Nat} (hs : StackOK A (S0 ++ T)) :
    ∀ q (hq : q < T.length), T[q] < A.length := by
  intro q hq
  have := hs.2.1 (S0.length + q) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa using this

theorem stepHyp_of_pop {pb : Bytes} {A : List Ent} {K S0 T : List Nat} {A1 : List Ent} {E : Ent}
    (hwf : ∀ j, j < A.length → NodeWF pb A K j) (hkr : ∀ j (h : j < A.length), A[j].kid + nKids A[j].nf ≤ K.length)
    (hst : StackOK A (S0 ++ T)) (hp : PopRel A T (childSlot E) A1 T.length)
    (kid : E.kid = K.length) (nk : nKids E.nf = T.length)
    (lo : E.lo = if h : 0 < T.length then loOf A T[0] else A.length)
    (res : E.res = (match E.nf with
             | .ext [] none _ => (A.getD (T.getD 0 0) default).res
             | .ext [] (some _) _ => RNONE
             | _ => A.length))
    (loc : LocalWF pb E) : StepHyp pb A K S0 T A1 E :=
  { wf := hwf, krange := hkr, stack := hst, len1 := hp.len, same := hp.same,
    other := hp.full.1, slot := hp.full.2, kid := kid, nk := nk, lo := lo, res := res, loc := loc }

theorem PopMem.wr4 {m m' : M} {A Ak : List Ent} {K T : List Nat} {k : Nat} {S0 : List Nat} {a v : Nat}
    (h : PopMem m A Ak K T k S0) (hm : m'.mem = ReexecNpai.wr4 m.mem a v)
    (ha : a + 4 ≤ AR ∨ (AR + 24 * A.length ≤ a ∧ a + 4 ≤ KL)) (hA : A.length ≤ NCAP) (hK : K.length + k ≤ NCAP) :
    PopMem m' A Ak K T k S0 := by
  refine h.frame (fun b h1 h2 => ?_) hA hK
  rw [rd32_eq, rd32_eq, hm, rdm_wr4_other]
  simp only [AR, KL, STK, NCAP] at *
  omega

end ReexecNpai

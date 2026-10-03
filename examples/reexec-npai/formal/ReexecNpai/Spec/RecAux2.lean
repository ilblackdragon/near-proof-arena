import ReexecNpai.Spec.RecAux1

/-!
# Record parse: arena step (pure)

Appending one entry to a well-formed partial arena: subtree nesting, stack
entries are not children of earlier entries, and the generic step lemma
`arena_step` (well-formedness, stack shape and `treeAt` of the extended arena).
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-- `lo` of entry `x`. -/
def loOf (A : List Ent) (x : Nat) : Nat := (A.getD x default).lo

theorem getD_eq_of {A : List Ent} {c : Nat} {ec d : Ent} (h : A[c]? = some ec) : A.getD c d = ec := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

theorem lt_of_getElem? {A : List Ent} {c : Nat} {ec : Ent} (h : A[c]? = some ec) : c < A.length := by
  rcases Nat.lt_or_ge c A.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

section
variable {pb : Bytes} {A : List Ent} {K : List Nat}

theorem wf_of (hwf : ∀ j, j < A.length → NodeWF pb A K j) {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    e.lo ≤ j ∧ (nKids e.nf = 0 → e.lo = j) ∧
    (∀ q, q < nKids e.nf →
      ∃ ec, A[childIdx K e.kid (nKids e.nf) q]? = some ec ∧ childIdx K e.kid (nKids e.nf) q < j ∧
        ec.pslot = childSlot e q ∧
        ec.lo = (if q = 0 then e.lo else childIdx K e.kid (nKids e.nf) (q - 1) + 1) ∧
        (q + 1 = nKids e.nf → childIdx K e.kid (nKids e.nf) q + 1 = j)) := by
  obtain ⟨e', he', -, -, -, -, -, -, -, h1, h2, h3, -⟩ := hwf j (lt_of_getElem? hj)
  rw [hj] at he'; cases he'
  exact ⟨h1, h2, h3⟩

theorem child_lo (hwf : ∀ j, j < A.length → NodeWF pb A K j) {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    ∀ q, q < nKids e.nf → e.lo ≤ loOf A (childIdx K e.kid (nKids e.nf) q) ∧
      loOf A (childIdx K e.kid (nKids e.nf) q) ≤ childIdx K e.kid (nKids e.nf) q := by
  intro q
  induction q with
  | zero =>
    intro hq
    obtain ⟨-, -, hc⟩ := wf_of hwf hj
    obtain ⟨ec, h1, -, -, h3, -⟩ := hc 0 hq
    simp only [↓reduceIte] at h3
    have := (wf_of hwf h1).1
    simp only [loOf, getD_eq_of h1]
    omega
  | succ q ih =>
    intro hq
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨-, -, hc⟩ := wf_of hwf hj
    obtain ⟨ec, h1, -, -, h3, -⟩ := hc (q + 1) hq
    have := (wf_of hwf h1).1
    simp only [loOf, getD_eq_of h1] at this ⊢
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h3
    exact ⟨by omega, this⟩

/-- Subtrees nest: every entry in the subtree interval of `j` has its own
interval inside it. -/
theorem nest (hwf : ∀ j, j < A.length → NodeWF pb A K j) :
    ∀ j, j < A.length → ∀ x, loOf A j ≤ x → x ≤ j → loOf A j ≤ loOf A x := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro hj x h1 h2
  rcases Nat.lt_or_ge x j with hx | hx
  case inr => rw [show x = j by omega]; exact Nat.le_refl _
  obtain ⟨e, he⟩ : ∃ e, A[j]? = some e := ⟨A[j], List.getElem?_eq_getElem hj⟩
  have hlo : loOf A j = e.lo := by rw [loOf, getD_eq_of he]
  rw [hlo] at h1 ⊢
  obtain ⟨-, h0, hc⟩ := wf_of hwf he
  have hR : 0 < nKids e.nf := by
    rcases Nat.eq_zero_or_pos (nKids e.nf) with h | h
    · have := h0 h; omega
    · exact h
  have hcl := child_lo hwf he
  -- find the child interval containing x
  have find : ∀ q, q < nKids e.nf → x ≤ childIdx K e.kid (nKids e.nf) q →
      ∃ q', q' < nKids e.nf ∧ loOf A (childIdx K e.kid (nKids e.nf) q') ≤ x ∧
        x ≤ childIdx K e.kid (nKids e.nf) q' := by
    intro q
    induction q with
    | zero =>
      intro hq hxq
      refine ⟨0, hq, ?_, hxq⟩
      obtain ⟨ec, e1, -, -, e3, -⟩ := hc 0 hq
      simp only [loOf, getD_eq_of e1, e3, ↓reduceIte]; exact h1
    | succ q ihq =>
      intro hq hxq
      by_cases hle : x ≤ childIdx K e.kid (nKids e.nf) q
      · obtain ⟨q', a, b, c⟩ := ihq (by omega) hle
        exact ⟨q', a, b, c⟩
      · refine ⟨q + 1, hq, ?_, hxq⟩
        obtain ⟨ec, e1, -, -, e3, -⟩ := hc (q + 1) hq
        simp only [loOf, getD_eq_of e1, e3, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        omega
  obtain ⟨ec, e1, -, -, -, e5⟩ := hc (nKids e.nf - 1) (by omega)
  have hlast := e5 (by omega)
  obtain ⟨q', hq', hx1, hx2⟩ := find (nKids e.nf - 1) (by omega) (by omega)
  obtain ⟨ec', f1, f2, -⟩ := hc q' hq'
  have := ih _ f2 (lt_of_getElem? f1) x hx1 hx2
  have := (hcl q' hq').1
  omega

/-- The stack is strictly increasing. -/
theorem stack_mono (hwf : ∀ j, j < A.length → NodeWF pb A K j) {S : List Nat} (hs : StackOK A S) :
    ∀ i k (hik : i < k) (hk : k < S.length), S[i]'(by omega) < S[k] := by
  obtain ⟨-, hlt, -, hcons, -⟩ := hs
  have step : ∀ i (h : i + 1 < S.length), S[i] < S[i + 1] := by
    intro i h
    have h1 := hcons i h
    have h2 := hlt (i + 1) h
    obtain ⟨e, he⟩ : ∃ e, A[S[i + 1]]? = some e := ⟨_, List.getElem?_eq_getElem h2⟩
    have := (wf_of hwf he).1
    rw [getD_eq_of he] at h1
    omega
  intro i k hik hk
  induction k with
  | zero => omega
  | succ k ih =>
    have := step k hk
    rcases Nat.lt_or_ge i k with h | h
    · have := ih h (by omega); omega
    · have hik' : i = k := by omega
      subst hik'; exact this

/-- Every entry lies in the interval of some stack entry. -/
theorem stack_cover {S : List Nat} (hs : StackOK A S) :
    ∀ k (hk : k < S.length) x, x ≤ S[k] → ∃ i, ∃ hi : i < S.length, i ≤ k ∧ loOf A S[i] ≤ x ∧ x ≤ S[i] := by
  obtain ⟨-, -, h0, hcons, -⟩ := hs
  intro k
  induction k with
  | zero =>
    intro hk x hx
    exact ⟨0, hk, Nat.le_refl _, by simp only [loOf]; rw [h0 hk]; omega, hx⟩
  | succ k ih =>
    intro hk x hx
    by_cases hle : x ≤ S[k]
    · obtain ⟨i, hi, a, b, c⟩ := ih (by omega) x hle
      exact ⟨i, hi, by omega, b, c⟩
    · exact ⟨k + 1, hk, Nat.le_refl _, by simp only [loOf, hcons k hk]; omega, hx⟩

/-- A stack entry is not a child of any entry. -/
theorem stack_not_child (hwf : ∀ j, j < A.length → NodeWF pb A K j) {S : List Nat} (hs : StackOK A S)
    {j : Nat} {e : Ent} (hj : A[j]? = some e) {q : Nat} (hq : q < nKids e.nf) :
    childIdx K e.kid (nKids e.nf) q ∉ S := by
  intro hmem
  obtain ⟨k, hk, hck⟩ := List.getElem_of_mem hmem
  have hjl := lt_of_getElem? hj
  have hne : S ≠ [] := by
    intro h; subst h; simp at hk
  have hSpos : 0 < S.length := by
    cases S with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hlast := hs.2.2.2.2 hSpos
  obtain ⟨i, hi, -, hi1, hi2⟩ := stack_cover hs (S.length - 1) (by omega) j (by omega)
  obtain ⟨-, -, hc⟩ := wf_of hwf hj
  obtain ⟨ec, -, hcj, -⟩ := hc q hq
  obtain ⟨hcl1, hcl2⟩ := child_lo hwf hj q hq
  have hSi := hs.2.1 i hi
  have hn := nest hwf S[i] hSi j hi1 hi2
  have hloj : loOf A j = e.lo := by rw [loOf, getD_eq_of hj]
  -- k < i
  have hki : k < i := by
    rcases Nat.lt_or_ge k i with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'; omega
      · have := stack_mono hwf hs i k h' hk; omega
  have hi0 : i ≠ 0 := by omega
  have hcons := hs.2.2.2.1 (i - 1) (by omega)
  have hcons' : loOf A S[i] = S[i - 1] + 1 := by
    simp only [loOf]; rw [← hcons]; simp only [show i - 1 + 1 = i by omega]
  have hmono : S[k] ≤ S[i - 1] := by
    rcases Nat.eq_or_lt_of_le (show k ≤ i - 1 by omega) with h | h
    · subst h; exact Nat.le_refl _
    · exact Nat.le_of_lt (stack_mono hwf hs k (i - 1) h (by omega))
  omega

end

/-- Two entries agree except possibly on `pslot`. -/
def SameBut (e' e : Ent) : Prop := { e' with pslot := e.pslot } = e

theorem SameBut.fields {e' e : Ent} (h : SameBut e' e) :
    e'.pre = e.pre ∧ e'.preLen = e.preLen ∧ e'.kid = e.kid ∧ e'.res = e.res ∧ e'.val = e.val ∧
    e'.nf = e.nf ∧ e'.lo = e.lo ∧ e'.rst = e.rst := by
  cases e'; cases e; simp only [SameBut, Ent.mk.injEq] at h
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h4, h5, h6, h7, h8, h9⟩

theorem vlenAt_same {pb : Bytes} {e' e : Ent} (h : SameBut e' e) : vlenAt pb e' = vlenAt pb e := by
  simp [vlenAt, h.fields.2.2.2.2.1]

theorem childSlot_same {e' e : Ent} (h : SameBut e' e) (q : Nat) : childSlot e' q = childSlot e q := by
  obtain ⟨h1, -, -, -, -, h6, -⟩ := h.fields
  simp [childSlot, h1, h6]

theorem childIdx_ext {K K' : List Nat} (hK : ∀ i, i < K.length → K'.getD i 0 = K.getD i 0)
    {kid R q : Nat} (hr : kid + R ≤ K.length) (hq : q < R) : childIdx K' kid R q = childIdx K kid R q := by
  simp only [childIdx]; exact hK _ (by omega)

/-- `NodeWF` survives changing other entries' `pslot`s (except of its children) and
extending the child list. -/
theorem nodeWF_transfer {pb : Bytes} {A A' : List Ent} {K K' : List Nat} {j : Nat}
    (h : NodeWF pb A K j) {e e' : Ent} (he : A[j]? = some e) (he' : A'[j]? = some e') (hf : SameBut e' e)
    (hkr : e.kid + nKids e.nf ≤ K.length) (hK : ∀ i, i < K.length → K'.getD i 0 = K.getD i 0)
    (hA : ∀ c ec, A[c]? = some ec → c < j → ∃ ec', A'[c]? = some ec' ∧ SameBut ec' ec)
    (hps : ∀ q, q < nKids e.nf → ∀ ec ec', A[childIdx K e.kid (nKids e.nf) q]? = some ec →
      A'[childIdx K e.kid (nKids e.nf) q]? = some ec' → ec'.pslot = ec.pslot) :
    NodeWF pb A' K' j := by
  obtain ⟨e0, he0, nfok, h1, h2, h3, hpre, hval, hhdr, hlo, hlo0, hch, hres⟩ := h
  rw [he] at he0; cases he0
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hf.fields
  have hv := vlenAt_same (pb := pb) hf
  refine ⟨e', he', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f6]; exact nfok
  · rw [f8]; exact h1
  · rw [f8, f1]; exact h2
  · rw [f1, f2]; exact h3
  · rw [f1, f2, f6, hv]; exact hpre
  · rw [f6, f5, f8, hv, f1]; exact hval
  · rw [f6, f1]; exact hhdr
  · rw [f7]; exact hlo
  · rw [f6, f7]; exact hlo0
  · intro q hq
    rw [f6] at hq
    obtain ⟨ec, c1, c2, c3, c4, c5⟩ := hch q hq
    have hcq : childIdx K' e'.kid (nKids e'.nf) q = childIdx K e.kid (nKids e.nf) q := by
      rw [f3, f6]; exact childIdx_ext hK hkr hq
    obtain ⟨ec', d1, d2⟩ := hA _ ec c1 c2
    refine ⟨ec', by rw [hcq]; exact d1, by rw [hcq]; exact c2, ?_, ?_, ?_⟩
    · rw [hps q hq ec ec' c1 d1, c3, childSlot_same hf]
    · rw [d2.fields.2.2.2.2.2.2.1, c4, f7]
      split
      · rfl
      · rw [f3, f6, childIdx_ext hK hkr (by omega)]
    · rw [hcq, f6]; exact c5
  · rw [f4, f6]
    revert hres
    cases hn : e.nf with
    | leaf _ _ _ => exact id
    | branch _ _ _ => exact id
    | ext k hh mm =>
      cases k with
      | cons _ _ => exact id
      | nil =>
        cases hh with
        | some _ => exact id
        | none =>
          intro hres
          rw [hres]
          have hq : 0 < nKids e.nf := by simp [hn, nKids]
          obtain ⟨ec, c1, c2, -⟩ := hch 0 hq
          have hk0 : childIdx K e.kid (nKids e.nf) 0 = K.getD e.kid 0 := by simp [childIdx, hn, nKids]
          rw [hk0] at c1 c2
          obtain ⟨ec', d1, d2⟩ := hA _ ec c1 c2
          have hkk : K'.getD e'.kid 0 = K.getD e.kid 0 := by
            rw [f3]; exact hK _ (by simp [hn, nKids] at hkr; omega)
          rw [hkk, getD_eq_of d1, getD_eq_of c1, d2.fields.2.2.2.1]

theorem treeAt_transfer {A A' : List Ent} {K K' : List Nat} {vals vals' : Nat → Bytes}
    (hA : ∀ c (hc : c < A.length), ∃ ec', A'[c]? = some ec' ∧ SameBut ec' A[c])
    (hkr : ∀ c (hc : c < A.length), A[c].kid + nKids A[c].nf ≤ K.length)
    (hK : ∀ i, i < K.length → K'.getD i 0 = K.getD i 0)
    (hv : ∀ c, c < A.length → vals' c = vals c) :
    ∀ j, j < A.length → treeAt A' K' vals' j = treeAt A K vals j := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro hj
  have he : A[j]? = some A[j] := List.getElem?_eq_getElem hj
  obtain ⟨e', he', hf⟩ := hA j hj
  obtain ⟨-, -, f3, -, -, f6, -⟩ := hf.fields
  have hk := hkr j hj
  cases hn : A[j].nf with
  | leaf k ref mm =>
    rw [treeAt_leaf he hn, treeAt_leaf he' (by rw [f6, hn]), hv j hj]
  | ext k h mm =>
    cases h with
    | some hh => rw [treeAt_exth he hn, treeAt_exth he' (by rw [f6, hn])]
    | none =>
      rw [treeAt_ext he hn, treeAt_ext he' (by rw [f6, hn])]
      rw [hn] at hk
      simp only [nKids, Option.isNone_none, ↓reduceIte] at hk
      rw [f3, hK _ (by omega)]
      split
      · rename_i hlt; rw [ih _ hlt (by omega)]
      · rfl
  | branch v ks mm =>
    rw [treeAt_branch he hn, treeAt_branch he' (by rw [f6, hn]), hv j hj]
    congr 1
    apply kidsOf_congr
    intro q _ hq
    rw [hn] at hk
    simp only [nKids] at hk
    rw [f3, childIdx_ext hK hk (by omega)]
    split
    · rename_i hlt; rw [ih _ hlt (by omega)]
    · rfl

/-! ## The generic step -/

/-- Local well-formedness of an entry (the parts of `NodeWF` about the entry itself). -/
def LocalWF (pb : Bytes) (E : Ent) : Prop :=
  NFOk E.nf ∧ PF ≤ E.rst ∧ E.rst < E.pre ∧ E.pre + E.preLen ≤ PF + pb.length ∧
    (∃ z zs, z.length = 32 ∧ zs.length = nKids E.nf ∧ (∀ x ∈ zs, x.length = 32) ∧
      pseg pb E.pre E.preLen = preImg E.nf (vlenAt pb E) z zs) ∧
    (if hasVal E.nf then E.val = E.rst + 5 ∧ vlenAt pb E < 4294967296 ∧
        E.pre = E.val + vlenAt pb E + (match E.nf with | .branch _ _ _ => 2 | _ => 0)
     else E.val = 0) ∧
    (match E.nf with
     | .ext _ h _ => pseg pb (E.pre - 1) 1 = [if h.isNone then 1 else 0]
     | .branch _ ks _ => pseg pb (E.pre - 2) 2 = u16 (bitsRev ks 0)
     | _ => True)

/-- The tree of a node with fields `nf`, value `v` and revealed children `ch`. -/
def nodeOf (nf : NF) (v : Bytes) (ch : Nat → PTrie) : PTrie :=
  match nf with
  | .leaf k ref mm => .leaf k (slotOfRef ref v) mm
  | .ext k (some hh) mm => .ext k (.hash hh) mm
  | .ext k none mm => .ext k (ch 0) mm
  | .branch vv ks mm => .branch (vv.map fun r => slotOfRef r v) (kidsOf ch ks 0) mm

/-- Hypotheses of one arena step: `A1` is `A` with the popped children `T` (the
top of the stack `S0 ++ T`) pointing into the new entry `E`. -/
structure StepHyp (pb : Bytes) (A : List Ent) (K S0 T : List Nat) (A1 : List Ent) (E : Ent) : Prop where
  wf : ∀ j, j < A.length → NodeWF pb A K j
  krange : ∀ j (h : j < A.length), A[j].kid + nKids A[j].nf ≤ K.length
  stack : StackOK A (S0 ++ T)
  len1 : A1.length = A.length
  same : ∀ j (h : j < A.length), SameBut (A1.getD j default) A[j]
  other : ∀ j (h : j < A.length), j ∉ T → (A1.getD j default).pslot = A[j].pslot
  slot : ∀ q (hq : q < T.length), (A1.getD T[q] default).pslot = childSlot E q
  kid : E.kid = K.length
  nk : nKids E.nf = T.length
  lo : E.lo = if h : 0 < T.length then loOf A T[0] else A.length
  res : E.res = (match E.nf with
             | .ext [] none _ => (A.getD (T.getD 0 0) default).res
             | .ext [] (some _) _ => RNONE
             | _ => A.length)
  loc : LocalWF pb E

section
variable {pb : Bytes} {A : List Ent} {K S0 T : List Nat} {A1 : List Ent} {E : Ent}

theorem StepHyp.T_lt (h : StepHyp pb A K S0 T A1 E) (q : Nat) (hq : q < T.length) : T[q] < A.length := by
  have := h.stack.2.1 (S0.length + q) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa using this

theorem StepHyp.get_old (h : StepHyp pb A K S0 T A1 E) {j : Nat} (hj : j < A.length) :
    (A1 ++ [E])[j]? = some (A1.getD j default) := by
  rw [List.getElem?_append_left (by rw [h.len1]; exact hj), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [h.len1]; exact hj)]
  rfl

theorem StepHyp.get_new (h : StepHyp pb A K S0 T A1 E) : (A1 ++ [E])[A.length]? = some E := by
  rw [List.getElem?_append_right (by rw [h.len1]; omega), h.len1]; simp

theorem StepHyp.getD_old (h : StepHyp pb A K S0 T A1 E) {j : Nat} (hj : j < A.length) (d : Ent) :
    (A1 ++ [E]).getD j d = A1.getD j default := by
  rw [List.getD_eq_getElem?_getD, h.get_old hj]; rfl

theorem StepHyp.getD_new (h : StepHyp pb A K S0 T A1 E) (d : Ent) : (A1 ++ [E]).getD A.length d = E := by
  rw [List.getD_eq_getElem?_getD, h.get_new]; rfl

theorem K_ext (K L : List Nat) : ∀ i, i < K.length → (K ++ L).getD i 0 = K.getD i 0 := by
  intro i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem childIdx_new (K T : List Nat) (q : Nat) (hq : q < T.length) :
    childIdx (K ++ T.reverse) K.length T.length q = T.getD q 0 := by
  simp only [childIdx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), show K.length + (T.length - 1 - q) - K.length = T.length - 1 - q by omega,
    List.getElem?_reverse (by omega), show T.length - 1 - (T.length - 1 - q) = q by omega]

theorem StepHyp.not_T (h : StepHyp pb A K S0 T A1 E) {j : Nat} {e : Ent} (hj : A[j]? = some e) {q : Nat}
    (hq : q < nKids e.nf) : childIdx K e.kid (nKids e.nf) q ∉ T := by
  intro hm
  exact stack_not_child h.wf h.stack hj hq (List.mem_append_right _ hm)

theorem StepHyp.wf_old (h : StepHyp pb A K S0 T A1 E) {j : Nat} (hj : j < A.length) :
    NodeWF pb (A1 ++ [E]) (K ++ T.reverse) j := by
  have he : A[j]? = some A[j] := List.getElem?_eq_getElem hj
  refine nodeWF_transfer (h.wf j hj) he (h.get_old hj) (h.same j hj) (h.krange j hj) (K_ext K _) ?_ ?_
  · intro c ec hc hcj
    have hcl := lt_of_getElem? hc
    refine ⟨_, h.get_old hcl, ?_⟩
    rw [List.getElem?_eq_getElem hcl] at hc; cases hc
    exact h.same c hcl
  · intro q hq ec ec' h1 h2
    have hcl := lt_of_getElem? h1
    rw [h.get_old hcl] at h2; cases h2
    rw [List.getElem?_eq_getElem hcl] at h1; cases h1
    exact h.other _ hcl (h.not_T he hq)

theorem StepHyp.lo_T (h : StepHyp pb A K S0 T A1 E) (q : Nat) (hq : q < T.length) :
    (A1.getD T[q] default).lo = if q = 0 then E.lo else T.getD (q - 1) 0 + 1 := by
  have hT := h.T_lt q hq
  rw [(h.same _ hT).fields.2.2.2.2.2.2.1]
  split
  · rename_i hq0; subst hq0
    rw [h.lo, dif_pos hq]; simp [loOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hT]
  · have hc := h.stack.2.2.2.1 (S0.length + (q - 1)) (by simp; omega)
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)] at hc
    simp only [show S0.length + (q - 1) + 1 - S0.length = q by omega,
      show S0.length + (q - 1) - S0.length = q - 1 by omega] at hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : q - 1 < T.length)]
    simp only [Option.getD_some]
    rw [← hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hT]
    rfl

theorem StepHyp.T_last (h : StepHyp pb A K S0 T A1 E) (q : Nat) (hq : q + 1 = T.length) :
    T.getD q 0 + 1 = A.length := by
  have hl := h.stack.2.2.2.2 (by simp; omega)
  rw [List.getElem_append_right (by simp; omega)] at hl
  simp only [List.length_append, show S0.length + T.length - 1 - S0.length = q by omega] at hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact hl

theorem StepHyp.wf_new (h : StepHyp pb A K S0 T A1 E) :
    NodeWF pb (A1 ++ [E]) (K ++ T.reverse) A.length := by
  obtain ⟨nfok, h1, h2, h3, hpre, hval, hhdr⟩ := h.loc
  refine ⟨E, h.get_new, nfok, h1, h2, h3, hpre, hval, hhdr, ?_, ?_, ?_, ?_⟩
  · rw [h.lo]; split
    · rename_i hT
      have := h.T_lt 0 hT
      have := (wf_of h.wf (List.getElem?_eq_getElem this)).1
      simp only [loOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h.T_lt 0 hT)]
      simp at this ⊢; omega
    · exact Nat.le_refl _
  · intro h0; rw [h.lo, dif_neg (by rw [← h.nk]; omega)]
  · intro q hq
    rw [h.nk] at hq ⊢
    have hc : childIdx (K ++ T.reverse) E.kid T.length q = T[q] := by
      rw [h.kid, childIdx_new K T q hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
    have hT := h.T_lt q hq
    refine ⟨A1.getD T[q] default, by rw [hc]; exact h.get_old hT, by rw [hc]; exact hT,
      h.slot q hq, ?_, ?_⟩
    · rw [h.lo_T q hq]
      split
      · rfl
      · rw [h.kid, childIdx_new K T (q - 1) (by omega)]
    · intro hq1; rw [hc]
      have := h.T_last q hq1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq] at this
      exact this
  · rw [h.res]
    cases hn : E.nf with
    | leaf _ _ _ => rfl
    | branch _ _ _ => rfl
    | ext k hh mm =>
      cases k with
      | cons _ _ => rfl
      | nil =>
        cases hh with
        | some _ => rfl
        | none =>
          have hT1 : T.length = 1 := by rw [← h.nk, hn]; rfl
          have h0 : 0 < T.length := by omega
          simp only
          rw [h.kid, K_ext' K T.reverse, List.getD_eq_getElem?_getD (l := T.reverse),
            List.getElem?_reverse (by omega)]
          simp only [hT1, Nat.sub_self]
          rw [List.getElem?_eq_getElem h0, Option.getD_some, h.getD_old (h.T_lt 0 h0),
            (h.same _ (h.T_lt 0 h0)).fields.2.2.2.1]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem (h.T_lt 0 h0)]
where
  K_ext' (K L : List Nat) : (K ++ L).getD K.length 0 = L.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getD_eq_getElem?_getD]

theorem StepHyp.wf' (h : StepHyp pb A K S0 T A1 E) :
    ∀ j, j < (A1 ++ [E]).length → NodeWF pb (A1 ++ [E]) (K ++ T.reverse) j := by
  intro j hj
  simp only [List.length_append, h.len1, List.length_singleton] at hj
  rcases Nat.lt_or_ge j A.length with hj' | hj'
  · exact h.wf_old hj'
  · rw [show j = A.length by omega]; exact h.wf_new

theorem StepHyp.length (h : StepHyp pb A K S0 T A1 E) : (A1 ++ [E]).length = A.length + 1 := by
  simp [h.len1]

theorem StepHyp.krange' (h : StepHyp pb A K S0 T A1 E) :
    ∀ j (hj : j < (A1 ++ [E]).length), (A1 ++ [E])[j].kid + nKids (A1 ++ [E])[j].nf ≤ (K ++ T.reverse).length := by
  intro j hj
  have hj2 : j < A.length + 1 := by rw [← h.length]; exact hj
  have hg : (A1 ++ [E])[j] = (A1 ++ [E]).getD j default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [hg]
  simp only [List.length_append, List.length_reverse]
  rcases Nat.lt_or_ge j A.length with hj' | hj'
  · rw [h.getD_old hj']
    obtain ⟨-, -, f3, -, -, f6, -⟩ := (h.same j hj').fields
    rw [f3, f6]; have := h.krange j hj'; omega
  · rw [show j = A.length by omega, h.getD_new, h.kid, h.nk]; omega

theorem StepHyp.stack' (h : StepHyp pb A K S0 T A1 E) : StackOK (A1 ++ [E]) (S0 ++ [A.length]) := by
  obtain ⟨_, hlt, h0, hcons, hlast⟩ := h.stack
  have hS0 : ∀ i (hi : i < S0.length), S0[i] < A.length := by
    intro i hi
    have := hlt i (by simp; omega)
    rwa [List.getElem_append_left hi] at this
  have hlo : ∀ c, c < A.length → ((A1 ++ [E]).getD c default).lo = (A.getD c default).lo := by
    intro c hc
    rw [h.getD_old hc, (h.same c hc).fields.2.2.2.2.2.2.1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hc]; rfl
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rw [h.length]
    rcases Nat.lt_or_ge i S0.length with h1 | h1
    · rw [List.getElem_append_left h1]; have := hS0 i h1; omega
    · rw [List.getElem_append_right h1]; simp
  · intro hp
    by_cases hS : 0 < S0.length
    · rw [List.getElem_append_left hS, hlo _ (hS0 0 hS)]
      have := h0 (by simp; omega)
      rwa [List.getElem_append_left hS] at this
    · have hS0e : S0 = [] := by cases S0 with | nil => rfl | cons _ _ => simp at hS
      subst hS0e
      simp only [List.nil_append, List.getElem_singleton]
      rw [h.getD_new, h.lo]
      split
      · rename_i hT
        have := h0 (by simp; omega)
        simp only [List.nil_append] at this
        simp only [loOf]; exact this
      · rename_i hT
        have hTe : T = [] := by cases T with | nil => rfl | cons _ _ => simp at hT
        subst hTe
        have := h.stack.1 rfl
        simp [this]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge (i + 1) S0.length with h1 | h1
    · rw [List.getElem_append_left h1, List.getElem_append_left (by omega), hlo _ (hS0 _ h1)]
      have := hcons i (by simp; omega)
      rwa [List.getElem_append_left h1, List.getElem_append_left (by omega)] at this
    · have hi1 : i + 1 = S0.length := by omega
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
      simp only [show i + 1 - S0.length = 0 by omega, List.getElem_singleton]
      rw [h.getD_new, h.lo]
      split
      · rename_i hT
        have := hcons i (by simp; omega)
        rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)] at this
        simp only [show i + 1 - S0.length = 0 by omega] at this
        simp only [loOf]; exact this
      · rename_i hT
        have hTe : T = [] := by cases T with | nil => rfl | cons _ _ => simp at hT
        subst hTe
        have := hlast (by simp; omega)
        simp only [List.append_nil] at this
        rw [← this]; congr 1; congr 1; omega
  · intro _
    simp [h.length]

theorem StepHyp.vals (h : StepHyp pb A K S0 T A1 E) :
    ∀ c, c < A.length → vals0 pb (A1 ++ [E]) c = vals0 pb A c := by
  intro c hc
  simp only [vals0]
  rw [h.getD_old hc, vlenAt_same (h.same c hc), (h.same c hc).fields.2.2.2.2.1, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hc]; rfl

theorem StepHyp.tree_old (h : StepHyp pb A K S0 T A1 E) :
    ∀ j, j < A.length → treeAt (A1 ++ [E]) (K ++ T.reverse) (vals0 pb (A1 ++ [E])) j = treeAt A K (vals0 pb A) j :=
  treeAt_transfer (fun c hc => ⟨_, h.get_old hc, h.same c hc⟩) h.krange (K_ext K _) h.vals

theorem StepHyp.tree_new (h : StepHyp pb A K S0 T A1 E) :
    treeAt (A1 ++ [E]) (K ++ T.reverse) (vals0 pb (A1 ++ [E])) A.length =
      nodeOf E.nf (pseg pb E.val (vlenAt pb E)) (fun q => treeAt A K (vals0 pb A) (T.getD q 0)) := by
  have hv : vals0 pb (A1 ++ [E]) A.length = pseg pb E.val (vlenAt pb E) := by
    simp only [vals0, h.getD_new]
  cases hn : E.nf with
  | leaf k ref mm => rw [treeAt_leaf h.get_new hn, hv]; rfl
  | ext k hh mm =>
    cases hh with
    | some hh => rw [treeAt_exth h.get_new hn]; rfl
    | none =>
      rw [treeAt_ext h.get_new hn]
      have hT1 : T.length = 1 := by rw [← h.nk, hn]; rfl
      have h0 : 0 < T.length := by omega
      have hk : (K ++ T.reverse).getD E.kid 0 = T.getD 0 0 := by
        have := childIdx_new K T 0 h0
        simp only [childIdx, hT1, Nat.sub_self, Nat.add_zero] at this
        rw [h.kid]; exact this
      have hTl : T.getD 0 0 < A.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0]; exact h.T_lt 0 h0
      rw [hk, if_pos hTl, h.tree_old _ hTl]; rfl
  | branch v ks mm =>
    rw [treeAt_branch h.get_new hn, hv]
    simp only [nodeOf]
    rw [kidsOf_congr (fun q => if childIdx (K ++ T.reverse) E.kid (nRev ks) q < A.length then
        treeAt (A1 ++ [E]) (K ++ T.reverse) (vals0 pb (A1 ++ [E])) (childIdx (K ++ T.reverse) E.kid (nRev ks) q)
        else .hash []) (fun q => treeAt A K (vals0 pb A) (T.getD q 0)) ks 0]
    intro q _ hq
    have hnk : nRev ks = T.length := by rw [← h.nk, hn]; rfl
    rw [hnk] at hq ⊢
    rw [Nat.zero_add] at hq
    rw [h.kid, childIdx_new K T q hq]
    have hTl : T.getD q 0 < A.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; exact h.T_lt q hq
    rw [if_pos hTl, h.tree_old _ hTl]

theorem StepHyp.revSum_eq (h : StepHyp pb A K S0 T A1 E) :
    revSum pb (A1 ++ [E]) = revSum pb A + entRev pb E := by
  have hm : A1.map (entRev pb) = A.map (entRev pb) := by
    apply List.ext_getElem (by simp [h.len1])
    intro i h1 h2
    simp only [List.getElem_map]
    simp only [List.length_map] at h2
    have hs := h.same i h2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [h.len1]; exact h2)] at hs
    simp only [Option.getD_some] at hs
    obtain ⟨-, f2, -, -, f5, f6, -⟩ := hs.fields
    simp only [entRev, f2, f6, vlenAt, f5]
  simp [revSum, List.map_append, List.foldl_append, hm]

end

end ReexecNpai

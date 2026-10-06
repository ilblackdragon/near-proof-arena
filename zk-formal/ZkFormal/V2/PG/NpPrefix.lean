import ZkFormal.V2.PG.NpFits
import ZkFormal.Udr.Np.Late

/-!
# ZkFormal.V2.PG.NpPrefix (P2 copy of `Prover.NpPrefix` at `dp = pg g`) — message `j` reads only the first `j` challenges (`MsgPrefixStmt`)

The aux/quotient/OOD messages read `cs[0..3]`; the DEEP batch reads `cs[0 .. 4+L)`;
the FRI word of layer `i` reads `β_{i'}` (`i' < i`) and `γ_{i'}` (`i' ≤ i`), all of which
precede the fold challenge of layer `i` in the schedule (`kinds_take`).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

/-! ## List plumbing -/

theorem zip_take_right {α β : Type} : ∀ (l : List α) (m : List β) (q : Nat),
    l.zip (m.take q) = (l.zip m).take q
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, 0 => by simp
  | a :: l, b :: m, q + 1 => by simp [zip_take_right l m q]

theorem zip_take_length {α β : Type} : ∀ (l : List α) (m : List β) (q : Nat), l.length ≤ q →
    l.zip (m.take q) = l.zip m
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | _ :: _, _ :: _, 0, h => by simp at h
  | a :: l, b :: m, q + 1, h => by simp [zip_take_length l m q (by simpa using h)]

theorem getD_of_prefix {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : Nat} (hi : i < l₁.length)
    (d : α) : l₁.getD i d = l₂.getD i d := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem lookup_none_of_not_mem {β : Type} (k : Nat) : ∀ (l : List (Nat × β)),
    k ∉ l.map Prod.fst → l.lookup k = none
  | [], _ => rfl
  | p :: l, h => by
    have hk : (k == p.1) = false := by
      simp only [beq_eq_false_iff_ne]; intro he; exact h (by simp [he])
    simp only [List.lookup, hk]
    exact lookup_none_of_not_mem k l (fun h' => h (List.mem_cons_of_mem _ h'))

theorem lookup_of_prefix {β : Type} : ∀ {l₁ l₂ : List (Nat × β)}, l₁ <+: l₂ → ∀ k : Nat,
    (k ∈ l₁.map Prod.fst ∨ k ∉ l₂.map Prod.fst) → l₁.lookup k = l₂.lookup k
  | [], l₂, _, k, h => by
    rcases h with h | h
    · simp at h
    · exact (lookup_none_of_not_mem k l₂ h).symm
  | p :: l₁, l₂, hp, k, h => by
    obtain ⟨t, rfl⟩ := hp
    simp only [List.cons_append, List.lookup]
    split
    · rfl
    · have hp' : l₁ <+: l₁ ++ t := ⟨t, rfl⟩
      apply lookup_of_prefix hp' k
      rcases h with h | h
      · rename_i hne
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h; simp at hne
        · exact Or.inl h
      · refine Or.inr fun h' => h ?_
        rw [List.cons_append, List.map_cons]
        exact List.mem_cons_of_mem _ h'

theorem length_filter_zip {α β : Type} (p : α → Bool) : ∀ (l : List α) (m : List β),
    l.length ≤ m.length → ((l.zip m).filter fun x => p x.1).length = (l.filter p).length
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: l, b :: m, h => by
    simp only [List.zip_cons_cons, List.filter_cons]
    have := length_filter_zip p l m (by simpa using h)
    split <;> simp [this]

theorem getD_take {α : Type} (cs : List α) {i n : Nat} (h : i < n) (d : α) :
    (cs.take n).getD i d = cs.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

/-! ## The DEEP batch depends on `cs[0 .. 4+L)` only -/

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem Bw_congr {cs cs' : List Fp8} (h : cs.take (4 + nB A tr) = cs'.take (4 + nB A tr)) :
    Bw A cb tr cs = Bw A cb tr cs' := by
  have hg : ∀ i, i < 4 → cs.getD i 0 = cs'.getD i 0 := fun i hi => by
    rw [← getD_take cs (n := 4 + nB A tr) (by omega), h, getD_take cs' (by omega)]
  have e0 : cAfp cs = cAfp cs' := hg 0 (by omega)
  have e1 : cGam cs = cGam cs' := hg 1 (by omega)
  have e2 : cAc cs = cAc cs' := hg 2 (by omega)
  have e3 : cZ cs = cZ cs' := hg 3 (by omega)
  unfold Bw ctx0 standin opAt auxOc quotOc finalsC oodC
  rw [e0, e1, e2, e3, h]

/-- The FRI words depend only on the DEEP batch and the FRI challenges they precede. -/
theorem word_congr {cs cs' : List Fp8} (hB : Bw A cb tr cs = Bw A cb tr cs') :
    ∀ i, (∀ i', i' < i → (betaL A tr cs).getD i' 0 = (betaL A tr cs').getD i' 0) →
      (∀ i', i' ≤ i → (gammaL A tr cs).lookup i' = (gammaL A tr cs').lookup i') →
      word A cb tr cs i = word A cb tr cs' i
  | 0, _, _ => by funext p; simp only [word, hB]
  | i + 1, hb, hg => by
    funext q
    have ih := word_congr hB i (fun i' hi' => hb i' (by omega)) (fun i' hi' => hg i' (by omega))
    simp only [word, ih, hb i (by omega), hg (i + 1) (Nat.le_refl _), hB]

end

/-! ## Kinds before a fold challenge -/

section
variable (A : Air) (tr : Trace Fp)

/-- The kinds of layer `i`. -/
def layerKinds (i : Nat) : List (Bool × Nat) :=
  (if rollInAt A dp (hdr A tr) i then [(true, i)] else []) ++ [(false, i)]

theorem kinds_decomp {i : Nat} (hi : i < ell A tr) :
    ∃ R, kinds A tr = (List.range i).flatMap (layerKinds A tr) ++
      ((if rollInAt A dp (hdr A tr) i then [(true, i)] else []) ++ [(false, i)]) ++ R := by
  have hl : finalLayer A dp (hdr A tr) = i + (1 + (ell A tr - i - 1)) := by unfold ell at hi ⊢; omega
  unfold kinds friChalKinds
  simp only []
  rw [hl, List.range_add, List.range_add, List.flatMap_append, List.map_append,
    List.flatMap_append]
  refine ⟨List.flatMap (fun i => (if rollInAt A dp (hdr A tr) i = true then [(true, i)] else []) ++
      [(false, i)]) (List.map (fun x => i + x) (List.map (fun x => 1 + x) (List.range (ell A tr - i - 1)))) ++
    (if rollInAt A dp (hdr A tr) (i + (1 + (ell A tr - i - 1))) = true then
      [(true, i + (1 + (ell A tr - i - 1)))] else []), ?_⟩
  simp [List.append_assoc]
  rfl

theorem kinds_sorted' : (kinds A tr).Pairwise (fun a b => keyOf a < keyOf b) :=
  kinds_sorted A dp (hdr A tr)

theorem length_layers (i : Nat) :
    (((List.range i).flatMap (layerKinds A tr)).filter (! ·.1)).length = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.flatMap_append, List.filter_append, List.length_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, layerKinds]
    split <;> simp

theorem mem_layers {i' i : Nat} (h : i' < i) (b : Bool) (hb : b = true → rollInAt A dp (hdr A tr) i' = true) :
    (b, i') ∈ (List.range i).flatMap (layerKinds A tr) := by
  rw [List.mem_flatMap]
  refine ⟨i', List.mem_range.mpr h, ?_⟩
  cases b
  · simp [layerKinds]
  · simp [layerKinds, hb rfl]

/-- The kinds strictly before the fold challenge of layer `i`. -/
theorem kinds_take {q i : Nat} (hq : (kinds A tr)[q]? = some (false, i)) :
    i < ell A tr ∧ (kinds A tr).take q = (List.range i).flatMap (layerKinds A tr) ++
      (if rollInAt A dp (hdr A tr) i then [(true, i)] else []) := by
  have hmem : (false, i) ∈ kinds A tr := List.mem_of_getElem? hq
  have hi : i < ell A tr := by
    have := (mem_kinds A dp (hdr A tr) _ hmem).1 rfl; exact this
  refine ⟨hi, ?_⟩
  obtain ⟨R, hR⟩ := kinds_decomp A tr hi
  let P := (List.range i).flatMap (layerKinds A tr) ++
    (if rollInAt A dp (hdr A tr) i then [(true, i)] else [])
  have hk : kinds A tr = P ++ (false, i) :: R := by rw [hR]; simp [P]
  have hq' : (kinds A tr)[P.length]? = some (false, i) := by rw [hk]; simp
  -- uniqueness of positions in a strictly sorted list
  have hs := kinds_sorted' A tr
  have hqP : q = P.length := by
    have h1 := List.getElem_of_getElem? hq
    have h2 := List.getElem_of_getElem? hq'
    obtain ⟨hlq, e1⟩ := h1
    obtain ⟨hlp, e2⟩ := h2
    rw [List.pairwise_iff_getElem] at hs
    rcases Nat.lt_trichotomy q P.length with h | h | h
    · have := hs q P.length hlq hlp h; rw [e1, e2] at this; exact absurd this (Nat.lt_irrefl _)
    · exact h
    · have := hs P.length q hlp hlq h; rw [e1, e2] at this; exact absurd this (Nat.lt_irrefl _)
  rw [hqP, hk, List.take_left]

end

theorem take_zip_both {α β : Type} : ∀ (l : List α) (m : List β) (q : Nat),
    (l.zip m).take q = (l.take q).zip (m.take q)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, 0 => by simp
  | a :: l, b :: m, q + 1 => by simp [take_zip_both l m q]

theorem mem_zip_of_mem {α β : Type} {k : α} : ∀ {l : List α} {m : List β}, k ∈ l →
    l.length ≤ m.length → ∃ v, (k, v) ∈ l.zip m
  | [], _, h, _ => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: m, h, hl => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨b, by simp⟩
    · obtain ⟨v, hv⟩ := mem_zip_of_mem (m := m) h (by simpa using hl)
      exact ⟨v, by simp [hv]⟩

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem roll_of_mem_kinds {i : Nat} (h : (true, i) ∈ kinds A tr) : rollInAt A dp (hdr A tr) i = true := by
  unfold kinds friChalKinds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at h
  rcases h with ⟨j, _, hj⟩ | hj
  · rcases hj with hj | hj
    · split at hj
      · simp at hj; subst hj; assumption
      · simp at hj
    · simp at hj
  · split at hj
    · simp at hj; subst hj; assumption
    · simp at hj

theorem friCs_take (cs : List Fp8) (q : Nat) :
    friCs A tr (cs.take (4 + nB A tr + q)) = (friCs A tr cs).take q := by
  unfold friCs
  rw [List.drop_take, show 4 + nB A tr + q - (4 + nB A tr) = q by omega, zip_take_right]

theorem betaL_prefix (cs : List Fp8) (q : Nat) :
    betaL A tr (cs.take (4 + nB A tr + q)) <+: betaL A tr cs := by
  unfold betaL; rw [friCs_take]
  exact ((List.take_prefix q _).filter _).map _

theorem gammaL_prefix (cs : List Fp8) (q : Nat) :
    gammaL A tr (cs.take (4 + nB A tr + q)) <+: gammaL A tr cs := by
  unfold gammaL; rw [friCs_take]
  exact ((List.take_prefix q _).filter _).map _

theorem take_take_nB (cs : List Fp8) (q : Nat) :
    (cs.take (4 + nB A tr + q)).take (4 + nB A tr) = cs.take (4 + nB A tr) := by
  rw [List.take_take]; congr 1; omega

/-- The FRI words computed at the fold challenge of layer `i` are the final ones. -/
theorem word_take {cs : List Fp8} {q i : Nat} (hq : (kinds A tr)[q]? = some (false, i))
    (hlen : 4 + nB A tr + q ≤ cs.length) :
    word A cb tr (cs.take (4 + nB A tr + q)) i = word A cb tr cs i := by
  obtain ⟨hi, htk⟩ := kinds_take A tr hq
  have hqk : q < (kinds A tr).length := (List.getElem?_eq_some_iff.mp hq).1
  have hB := Bw_congr A cb tr (take_take_nB A tr cs q)
  have hzl : ((kinds A tr).take q).length ≤ ((cs.drop (4 + nB A tr)).take q).length := by
    simp; omega
  apply word_congr A cb tr hB
  · intro i' hi'
    apply getD_of_prefix (betaL_prefix A tr cs q)
    unfold betaL; rw [friCs_take, List.length_map]
    unfold friCs; rw [take_zip_both, length_filter_zip (fun k => !k.1) _ _ hzl, htk,
      List.filter_append, List.length_append, length_layers]
    omega
  · intro i' hi'
    apply lookup_of_prefix (gammaL_prefix A tr cs q)
    by_cases hr : rollInAt A dp (hdr A tr) i' = true
    · left
      have hmem : (true, i') ∈ (kinds A tr).take q := by
        rw [htk]
        rcases Nat.lt_or_eq_of_le hi' with h | h
        · exact List.mem_append_left _ (mem_layers A tr h true (fun _ => hr))
        · subst h; exact List.mem_append_right _ (by simp [hr])
      obtain ⟨v, hv⟩ := mem_zip_of_mem hmem hzl
      unfold gammaL; rw [friCs_take]; unfold friCs; rw [take_zip_both]
      simp only [List.map_map, List.mem_map, List.mem_filter, Function.comp]
      exact ⟨((true, i'), v), ⟨hv, rfl⟩, rfl⟩
    · right
      intro hm
      unfold gammaL friCs at hm
      simp only [List.map_map, List.mem_map, List.mem_filter, Function.comp] at hm
      obtain ⟨⟨⟨b, k⟩, v⟩, ⟨hz, hb⟩, he⟩ := hm
      simp only at hb he
      subst hb; subst he
      exact hr (roll_of_mem_kinds A tr (List.of_mem_zip hz).1)

theorem getD_take' (cs : List Fp8) {i j : Nat} (h : i < j) : (cs.take j).getD i 0 = cs.getD i 0 :=
  getD_take cs h 0

end

theorem prefix_fri (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8) (q : Nat)
    (hjc : 4 + nB A tr + q ≤ cs.length) :
    (match (kinds A tr)[q]? with
      | some k => kindMsg A cb tr (cs.take (4 + nB A tr + q)) k
      | none => [PartV.elems (finalPoly A cb tr (cs.take (4 + nB A tr + q)))]) =
    (match (kinds A tr)[q]? with
      | some k => kindMsg A cb tr cs k
      | none => [PartV.elems (finalPoly A cb tr cs)]) := by
  cases hk : (kinds A tr)[q]? with
  | some k =>
    obtain ⟨b, i⟩ := k
    cases b
    · unfold kindMsg
      simp only [Bool.false_eq_true, ite_false]
      cases (commits A tr).lookup i with
      | none => rfl
      | some a => simp only [friMat, word_take A cb tr hk hjc]
    · simp only [kindMsg, ite_true]
  | none =>
    have hq : (kinds A tr).length ≤ q := by
      rcases Nat.lt_or_ge q (kinds A tr).length with h | h
      · rw [List.getElem?_eq_getElem h] at hk; cases hk
      · exact h
    have hF : friCs A tr (cs.take (4 + nB A tr + q)) = friCs A tr cs := by
      unfold friCs
      rw [List.drop_take, show 4 + nB A tr + q - (4 + nB A tr) = q by omega, zip_take_length _ _ _ hq]
    have hB' := Bw_congr A cb tr (take_take_nB A tr cs q)
    have hw : word A cb tr (cs.take (4 + nB A tr + q)) = word A cb tr cs := by
      funext i
      exact word_congr A cb tr hB' i (fun i' _ => by unfold betaL; rw [hF])
        (fun i' _ => by unfold gammaL; rw [hF])
    simp only [finalPoly, hw]

theorem prefix_small (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8) (j : Nat) (hj : j ≤ 4) :
    npMsg A cb tr (cs.take j) j = npMsg A cb tr cs j := by
  have e0 : ∀ i, i < j → (cs.take j).getD i 0 = cs.getD i 0 := fun i h => getD_take' cs h
  match j, hj with
  | 0, _ => simp only [npMsg, ↓reduceIte]
  | 1, _ => simp only [npMsg, show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
  | 2, _ =>
    have a0 : cAfp (cs.take 2) = cAfp cs := e0 0 (by omega)
    have a1 : cGam (cs.take 2) = cGam cs := e0 1 (by omega)
    simp only [npMsg, auxOc, finalsC, a0, a1, ↓reduceIte, show (2 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 1 by decide]
  | 3, _ =>
    have a0 : cAfp (cs.take 3) = cAfp cs := e0 0 (by omega)
    have a1 : cGam (cs.take 3) = cGam cs := e0 1 (by omega)
    have a2 : cAc (cs.take 3) = cAc cs := e0 2 (by omega)
    simp only [npMsg, quotOc, a0, a1, a2, ↓reduceIte, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide]
  | 4, _ =>
    have a0 : cAfp (cs.take 4) = cAfp cs := e0 0 (by omega)
    have a1 : cGam (cs.take 4) = cGam cs := e0 1 (by omega)
    have a2 : cAc (cs.take 4) = cAc cs := e0 2 (by omega)
    have a3 : cZ (cs.take 4) = cZ cs := e0 3 (by omega)
    simp only [npMsg, oodC, a0, a1, a2, a3, ↓reduceIte, show (4 : Nat) ≠ 0 by decide,
      show (4 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 3 by decide]

theorem msgPrefix : MsgPrefixStmt := by
  intro A cb tr _ cs j hj hjc
  by_cases hs : j ≤ 4
  · exact prefix_small A cb tr cs j hs
  have hb := nB_pos A tr
  unfold npMsg
  simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega,
    show j ≠ 4 by omega, ite_false]
  by_cases hB : j < 4 + nB A tr
  · simp only [hB, ite_true]
  simp only [hB, ite_false]
  obtain ⟨q, rfl⟩ : ∃ q, j = 4 + nB A tr + q := ⟨j - (4 + nB A tr), by omega⟩
  rw [show 4 + nB A tr + q - (4 + nB A tr) = q by omega]
  exact prefix_fri A cb tr cs q hjc

end ZkFormal.Prover.Np.G

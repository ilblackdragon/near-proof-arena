import ZkFormal.NearV3.Render.Node.TEdge2

/-!
# ZkFormal.NearV3.Render.Node.TEdge3 — EDGE: branch records (`DOWN` edges in slot order, then `VAL`)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- Child windows: messages depending on the child and its slot. -/
theorem wins_flat2 {β : Type} (kids : List NKid) (G : F → List β) (K : NKid × Nat → List β)
    (hK : ∀ k w l j, G (.ch (kidWin k w l (some j))) = K (k, j)) (K0 : ∀ j, K (.none, j) = []) :
    (branchWins kids).flatMap G = (kids.zip (List.range kids.length)).flatMap K := by
  unfold branchWins
  generalize hP : (kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none) = P
  have h1 : ((P.zip (List.range P.length)).map (fun x => F.ch (kidWin x.1.1 x.2 (x.2 + 1 = P.length)
      (some x.1.2)))).flatMap G = P.flatMap K := by
    rw [List.flatMap_map]
    have : ∀ (Q : List (NKid × Nat)) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => G (F.ch (kidWin x.1.1 x.2 (x.2 + 1 = P.length) (some x.1.2)))) =
          Q.flatMap K := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L =>
          simp only [List.zip_cons_cons, List.flatMap_cons]
          rw [ih L (by simpa using hL), hK]
    exact this P _ (by simp)
  have h3 : P.flatMap K = (kids.zip (List.range kids.length)).flatMap K := by
    rw [← hP]
    generalize kids.zip (List.range kids.length) = Q
    induction Q with
    | nil => rfl
    | cons q Q ih =>
      obtain ⟨k, j⟩ := q
      by_cases hq : k = .none
      · subst hq
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false, List.flatMap_cons, ih, K0, List.nil_append]
      · simp only [List.filter_cons, hq, ne_eq, not_false_eq_true, decide_true, if_true, List.flatMap_cons, ih]
  rw [h1, h3]

/-- Revealed-child `DOWN` pair of slot `j`. -/
def downF (n : Nat) (kids : List NKid) : NKid × Nat → List (List Nat × Nat)
  | (.node _ _ r _ _, j) => [([n, 0, j, r, 0, EK_DOWN], revBelow kids j)]
  | _ => []

def downO (n : Nat) : NKid × Nat → Option (List Nat)
  | (.node _ _ cr _ _, j) => some [n, 0, j, cr, 0, EK_DOWN]
  | _ => none

def downsE (n : Nat) (kids : List NKid) : List (List Nat) :=
  (kids.zip (List.range kids.length)).filterMap (downO n)

theorem zip_snoc (kids : List NKid) (k : NKid) :
    (kids ++ [k]).zip (List.range (kids ++ [k]).length) = kids.zip (List.range kids.length) ++ [(k, kids.length)] := by
  rw [List.length_append, List.length_singleton, List.range_succ, List.zip_append (by simp)]
  rfl

theorem revBelow_snoc (kids : List NKid) (k : NKid) {j : Nat} (hj : j ≤ kids.length) :
    revBelow (kids ++ [k]) j = revBelow kids j := by
  simp only [revBelow, List.take_append_of_le_length hj]

theorem revBelow_all (kids : List NKid) (k : NKid) :
    revBelow (kids ++ [k]) (kids ++ [k]).length = revBelow kids kids.length +
      (match k with | .node .. => 1 | _ => 0) := by
  simp only [revBelow]
  rw [List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _), List.filter_append,
    List.length_append]
  cases k <;> simp

theorem snoc_ind {α : Type} {P : List α → Prop} (l : List α) (nil : P [])
    (append_singleton : ∀ l x, P l → P (l ++ [x])) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x t ih => rw [List.reverse_cons]; exact append_singleton _ _ ih

theorem downs_len (n : Nat) (kids : List NKid) : (downsE n kids).length = revBelow kids kids.length := by
  induction kids using snoc_ind with
  | nil => rfl
  | append_singleton kids k ih =>
    rw [downsE, zip_snoc, List.filterMap_append, List.length_append, ← downsE, ih, revBelow_all]
    cases k <;> simp [downO]

theorem nRev_branch (sv : Option NSlot3) (kids : List NKid) (m : List Nat) :
    nRev (.branch sv kids m) = revBelow kids kids.length := by
  simp only [nRev, NodeV3.revealed]
  induction kids using snoc_ind with
  | nil => rfl
  | append_singleton kids k ih =>
    rw [List.filterMap_append, List.length_append, ih, revBelow_all]
    cases k <;> simp

theorem enumL_snoc (a : List (List Nat)) (e : List Nat) : enumL (a ++ [e]) = enumL a ++ [(e, a.length)] := by
  rw [enumL_append, enumL_single]; rfl

theorem downs_enum (n : Nat) (kids : List NKid) :
    (kids.zip (List.range kids.length)).flatMap (downF n kids) = enumL (downsE n kids) := by
  induction kids using snoc_ind with
  | nil => rfl
  | append_singleton kids k ih =>
    rw [zip_snoc, List.flatMap_append, downsE, zip_snoc, List.filterMap_append, ← downsE]
    have h1 : (kids.zip (List.range kids.length)).flatMap (downF n (kids ++ [k])) =
        (kids.zip (List.range kids.length)).flatMap (downF n kids) := by
      apply ZkFormal.Near.Render.flatMap_congr'
      intro x hx
      have hj := List.mem_range.1 (List.of_mem_zip hx).2
      obtain ⟨k', j⟩ := x
      cases k' <;> simp [downF, revBelow_snoc kids k (show j ≤ kids.length by simp at hj; omega)]
    rw [h1, ih]
    have h2 : revBelow (kids ++ [k]) kids.length = (downsE n kids).length := by
      rw [revBelow_snoc kids k (Nat.le_refl _), downs_len]
    cases k with
    | node c l r pre po =>
      simp only [downF, h2, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filterMap_cons, downO,
        List.filterMap_nil]
      exact (enumL_snoc _ _).symm
    | hash h => simp [downF, downO, List.filterMap_cons]
    | none => simp [downF, downO, List.filterMap_cons]

def valE (n : Nat) : Option NSlot3 → List (List Nat)
  | some (.val _ i _ _ _ _) => [[n, 0, SYM_END, i, 0, EK_VAL]]
  | _ => []

theorem edges_branch (n : Nat) (s : NodeS3) (sv : Option NSlot3) (kids : List NKid) (m : List Nat)
    (hs : s.v = .branch sv kids m) :
    edgesOf3 n s = downsE n kids ++ valE n sv := by
  obtain ⟨v, _⟩ := s
  simp only at hs
  subst hs
  rfl

/-- **Branch records: the EDGE pairs are the enumerated edges, up to order.** -/
theorem rec_pairs_branch (vs : List NodeS3) (n : Nat) (sv : Option NSlot3) (kids : List NKid)
    (m : List Nat) (hs : (rec vs n).v = .branch sv kids m) :
    (recPairs vs n).Perm (enumL (edgesOf3 n (rec vs n))) := by
  have hle : isLE (rec vs n).v = false := by rw [hs]; rfl
  have hW : (branchWins kids).flatMap (fun f => (List.range (f.len (hplenOf (rec vs n).v))).flatMap
      fun i => gE vs n (f, i)) = (kids.zip (List.range kids.length)).flatMap (downF n kids) := by
    apply wins_flat2
    · intro k w l j
      rw [range0' _ _ (by cases k <;> simp [F.len, kidWin]) (fun i hi => by rw [gE_ch]; simp [hi])]
      rw [gE_ch]
      cases k <;> simp [kidWin, downF, hle, hs, kidsOf, isLE]
    · intro j; rfl
  have hE := edges_branch n (rec vs n) sv kids m hs
  rw [hE, enumL_append, ← downs_enum, ← hW]
  have hN : nRev (rec vs n).v = (downsE n kids).length := by rw [hs, nRev_branch, downs_len]
  simp only [recPairs]
  cases sv with
  | none =>
    rw [show fieldsOf (rec vs n).v = [.tag, .bm] ++ branchWins kids ++ [.mem] by rw [hs]; rfl]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [rangeNil _ (F.len _ .tag) (fun i => gE_other vs n .tag i (by simp) (by simp) (by simp) (by simp) (by simp)),
      rangeNil _ (F.len _ .bm) (fun i => gE_other vs n .bm i (by simp) (by simp) (by simp) (by simp) (by simp)),
      rangeNil _ (F.len _ .mem) (fun i => by rw [gE_mem]; simp [hs, isLeaf])]
    simp [enumL, valE]
  | some s =>
    rw [show fieldsOf (rec vs n).v = [.tag, .vlen, .vh (valWin s), .bm] ++ branchWins kids ++ [.mem] by rw [hs]; rfl]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [rangeNil _ (F.len _ .tag) (fun i => gE_other vs n .tag i (by simp) (by simp) (by simp) (by simp) (by simp)),
      rangeNil _ (F.len _ .vlen) (fun i => gE_other vs n .vlen i (by simp) (by simp) (by simp) (by simp) (by simp)),
      rangeNil _ (F.len _ .bm) (fun i => gE_other vs n .bm i (by simp) (by simp) (by simp) (by simp) (by simp)),
      rangeNil _ (F.len _ .mem) (fun i => by rw [gE_mem]; simp [hs, isLeaf]),
      range0' _ (F.len _ (.vh (valWin s))) (by simp [F.len]) (fun i hi => by rw [gE_vh]; simp [hi])]
    simp only [List.nil_append, List.append_nil]
    refine (List.perm_append_comm).trans ?_
    congr 1
    rw [gE_vh, hN]
    cases s with
    | ref l h => simp [enumL, tvOf, hs, NodeV3.value, valE]
    | val l i vl pre po wr => simp [enumL, tvOf, hs, NodeV3.value, typeOf, isLeaf, vidOf, valE]

end NodeGen3

end ZkFormal.NearV3.Render

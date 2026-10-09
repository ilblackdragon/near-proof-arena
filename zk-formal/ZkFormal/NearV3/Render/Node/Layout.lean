import ZkFormal.NearV3.Render.Node.Gen

/-!
# ZkFormal.NearV3.Render.Node.Layout — the bytes of a record, field by field

`fbytes v post f`: the bytes of field `f`; the serialization is their concatenation
(`ser_fields`), each has the field's length (`fbytes_len`), so the serialization is
read off the layout (`ser_getD`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

def tagOf : NodeV3 → Nat
  | .leaf .. => 0
  | .ext .. => 3
  | .branch none .. => 1
  | .branch (some _) .. => 2

/-- The bytes of field `f` of record `v`. -/
def fbytes (v : NodeV3) (post : Bool) : F → List Nat
  | .tag => [tagOf v]
  | .hpl => u32Bytes (hpN (keyOf v) (isLeaf v)).length
  | .hpf => (hpN (keyOf v) (isLeaf v)).take 1
  | .key => (hpN (keyOf v) (isLeaf v)).drop 1
  | .vlen => ((slotOf v).map NSlot3.lenB).getD []
  | .vh w => if post then w.post else w.pre
  | .bm => [bmvOf v % 256, bmvOf v / 256]
  | .ch w => if post then w.post else w.pre
  | .mem => memOf v

theorem kidWin_bytes (k : NKid) (w : Nat) (l : Bool) (sl : Option Nat) (post : Bool) :
    (if post then (kidWin k w l sl).post else (kidWin k w l sl).pre) = k.bytes post := by
  cases k <;> cases post <;> rfl

theorem branchWins_bytes (kids : List NKid) (post : Bool) (v : NodeV3) :
    (branchWins kids).flatMap (fbytes v post) = kids.flatMap (NKid.bytes post) := by
  unfold branchWins
  generalize hP : (kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none) = P
  have h1 : ((P.zip (List.range P.length)).map (fun x => F.ch (kidWin x.1.1 x.2 (x.2 + 1 = P.length)
      (some x.1.2)))).flatMap (fbytes v post) = P.flatMap fun x => x.1.bytes post := by
    rw [List.flatMap_map]
    have : ∀ (Q : List (NKid × Nat)) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => fbytes v post (F.ch (kidWin x.1.1 x.2 (x.2 + 1 = P.length) (some x.1.2)))) =
          Q.flatMap fun x => x.1.bytes post := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L =>
          simp only [List.zip_cons_cons, List.flatMap_cons]
          rw [ih L (by simpa using hL)]
          simp only [fbytes, kidWin_bytes]
    exact this P _ (by simp)
  have h2 : (kids.zip (List.range kids.length)).flatMap (fun x => x.1.bytes post) = kids.flatMap (NKid.bytes post) := by
    have : ∀ (Q : List NKid) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => x.1.bytes post) = Q.flatMap (NKid.bytes post) := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L => simp only [List.zip_cons_cons, List.flatMap_cons]; rw [ih L (by simpa using hL)]
    exact this kids _ (by simp)
  have h3 : P.flatMap (fun x => x.1.bytes post) =
      (kids.zip (List.range kids.length)).flatMap (fun x => x.1.bytes post) := by
    rw [← hP]
    generalize kids.zip (List.range kids.length) = Q
    induction Q with
    | nil => rfl
    | cons q Q ih =>
      by_cases hq : q.1 = .none
      · simp only [List.filter_cons, hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false, List.flatMap_cons, ih]
        simp [NKid.bytes]
      · simp only [List.filter_cons, hq, ne_eq, not_false_eq_true, decide_true, if_true, List.flatMap_cons, ih]
  rw [h1, h3, h2]

theorem take_tail (l X : List Nat) : l.take 1 ++ (l.drop 1 ++ X) = l ++ X := by
  cases l <;> simp

theorem slot_bytes (s : NSlot3) (post : Bool) :
    s.bytes post = s.lenB ++ (if post then (valWin s).post else (valWin s).pre) := by
  cases s <;> cases post <;> rfl

/-- **The serialization is the concatenation of the field bytes.** -/
theorem ser_fields (v : NodeV3) (post : Bool) : v.ser post = (fieldsOf v).flatMap (fbytes v post) := by
  cases v with
  | leaf k s m =>
    simp only [NodeV3.ser, fieldsOf, List.flatMap_cons, List.flatMap_nil, fbytes, slot_bytes, keyOf, isLeaf,
      slotOf, memOf, tagOf, Option.map_some, Option.getD_some, List.append_nil, List.append_assoc]
    rw [take_tail]
  | ext k kid m =>
    simp only [NodeV3.ser, fieldsOf, List.flatMap_cons, List.flatMap_nil, fbytes, keyOf, isLeaf, memOf, tagOf,
      List.append_nil, List.append_assoc, kidWin_bytes]
    rw [take_tail]
  | branch sv kids m =>
    cases sv with
    | none =>
      simp only [NodeV3.ser, fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        fbytes, memOf, tagOf, bmvOf, isLE, kidsOf, List.append_nil, List.append_assoc, branchWins_bytes]
      simp
    | some s =>
      simp only [NodeV3.ser, fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        fbytes, memOf, tagOf, bmvOf, isLE, kidsOf, slotOf, slot_bytes, Option.map_some, Option.getD_some,
        List.append_nil, List.append_assoc, branchWins_bytes]
      simp

/-! ## Field lengths -/

theorem hpN_len (k : List Nat) (b : Bool) : (hpN k b).length = 1 + k.length / 2 :=
  NodeLay.hpN_len k b

theorem mem_branchWins {kids : List NKid} {f : F} (h : f ∈ branchWins kids) :
    ∃ k w l j, k ∈ kids ∧ k ≠ .none ∧ f = .ch (kidWin k w l (some j)) := by
  unfold branchWins at h
  rw [List.mem_map] at h
  obtain ⟨⟨⟨k, j⟩, w⟩, hm, rfl⟩ := h
  have hm1 := (List.of_mem_zip hm).1
  rw [List.mem_filter] at hm1
  exact ⟨k, w, _, j, (List.of_mem_zip hm1.1).1, by simpa using hm1.2, rfl⟩

theorem kid_len {k : NKid} (hk : k.wf) (hne : k ≠ .none) (w : Nat) (l : Bool) (sl : Option Nat) (v : NodeV3)
    (post : Bool) : (fbytes v post (.ch (kidWin k w l sl))).length = 32 := by
  cases k with
  | none => exact absurd rfl hne
  | hash h => cases post <;> simpa [fbytes, kidWin, NKid.wf] using hk
  | node c l' r pre po => cases post <;> simp [fbytes, kidWin, NKid.wf] at hk ⊢ <;> simp [hk]

theorem val_len {s : NSlot3} (hs : s.wf) (v : NodeV3) (post : Bool) :
    (fbytes v post (.vh (valWin s))).length = 32 := by
  cases s with
  | ref l h => cases post <;> simpa [fbytes, valWin, NSlot3.wf] using hs.2
  | val l i vl pre po w =>
    obtain ⟨_, h1, h2, _⟩ := hs
    cases post <;> simp [fbytes, valWin, h1, h2]

theorem fbytes_len {v : NodeV3} (hw : v.wf) (post : Bool) :
    ∀ f ∈ fieldsOf v, (fbytes v post f).length = f.len (hplenOf v) := by
  intro f hf
  cases v with
  | leaf k s m =>
    obtain ⟨-, hs, hm⟩ := hw
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    have hl : s.lenB.length = 4 := by cases s <;> exact hs.1
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · simp [fbytes, F.len, u32r]
    · simp [fbytes, F.len, hpN_len, keyOf, isLeaf]
    · simp [fbytes, F.len, hpN_len, keyOf, isLeaf, hplenOf, isLE]
    · simp [fbytes, F.len, slotOf, hl]
    · exact val_len hs _ post
    · simp [fbytes, F.len, memOf, hm]
  | ext k kid m =>
    obtain ⟨-, hne, hk, hm⟩ := hw
    simp only [fieldsOf, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · simp [fbytes, F.len, u32r]
    · simp [fbytes, F.len, hpN_len, keyOf, isLeaf]
    · simp [fbytes, F.len, hpN_len, keyOf, isLeaf, hplenOf, isLE]
    · exact kid_len hk hne _ _ _ _ post
    · simp [fbytes, F.len, memOf, hm]
  | branch sv kids m =>
    obtain ⟨-, hs, hk, hm⟩ := hw
    have hb : ∀ f ∈ branchWins kids, (fbytes (.branch sv kids m) post f).length = f.len 0 := by
      intro f hf
      obtain ⟨k, w, l, j, hkm, hne, rfl⟩ := mem_branchWins hf
      exact kid_len (hk k hkm) hne w l (some j) _ post
    have h0 : hplenOf (.branch sv kids m) = 0 := rfl
    rw [h0]
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | hf | rfl
      · rfl
      · rfl
      · exact hb f (by simpa using hf)
      · simp [fbytes, F.len, memOf, hm]
    | some s =>
      have hs' := hs s rfl
      have hl : s.lenB.length = 4 := by cases s <;> exact hs'.1
      simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf | rfl
      · rfl
      · simp [fbytes, F.len, slotOf, hl]
      · exact val_len hs' _ post
      · rfl
      · exact hb f (by simpa using hf)
      · simp [fbytes, F.len, memOf, hm]

/-- **The serialization read off the layout.** -/
theorem ser_layout {v : NodeV3} (hw : v.wf) (post : Bool) :
    v.ser post = (layout (fieldsOf v) (hplenOf v)).map fun fi => (fbytes v post fi.1).getD fi.2 0 := by
  rw [ser_fields]
  exact NodeLay.flatMap_layout _ _ _ (fbytes_len hw post)

theorem ser_len {v : NodeV3} (hw : v.wf) (post : Bool) :
    (v.ser post).length = (layout (fieldsOf v) (hplenOf v)).length := by
  rw [ser_layout hw post, List.length_map]

theorem ser_getD {v : NodeV3} (hw : v.wf) (post : Bool) {p : Nat}
    (hp : p < (layout (fieldsOf v) (hplenOf v)).length) :
    (v.ser post).getD p 0 = (fbytes v post ((layout (fieldsOf v) (hplenOf v)).getD p default).1).getD
      ((layout (fieldsOf v) (hplenOf v)).getD p default).2 0 := by
  rw [ser_layout hw post]
  simp [List.getD_eq_getElem?_getD, hp]

end NodeGen3

end ZkFormal.NearV3.Render

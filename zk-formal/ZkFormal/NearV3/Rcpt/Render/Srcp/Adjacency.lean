import ZkFormal.NearV3.Rcpt.Render.Srcp.Layout
import ZkFormal.Near.Render.Proof.MrkRecs

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near.Render

private theorem range_adj {α : Type} (f : Nat → α) (rel : α → α → Prop)
    (n : Nat) (h : ∀ i, i + 1 < n → rel (f i) (f (i + 1))) :
    Adj2 rel ((List.range n).map f) := by
  apply Adj2.of_get
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  exact h i hi

private theorem range_adj' (rel : Nat → Nat → Prop) (n : Nat)
    (h : ∀ i, i + 1 < n → rel i (i + 1)) : Adj2 rel (List.range n) := by
  simpa using range_adj id rel n h

/-- Within a path segment every next descriptor is the next byte. -/
theorem path_adj (B : SrcpB) (i : Nat) :
    Adj2 (fun a b => nextKind B a = some b) ((List.range 64).map (Kind.path i)) := by
  apply range_adj
  intro o ho
  simp [nextKind, ho]

/-- The path-segment boundary increments the path index and resets its byte. -/
theorem paths_adj (B : SrcpB) :
    Adj2 (fun a b => nextKind B a = some b)
      ((List.range B.path.length).flatMap fun i => (List.range 64).map (Kind.path i)) := by
  apply Adj2.flatMap
  · intro i _
    exact path_adj B i
  · apply range_adj'
    intro i hi a b ha hb
    have ha' : a = .path i 63 := by simpa [List.range_succ] using ha.symm
    have hb' : b = .path (i + 1) 0 := by simpa [List.range_succ_eq_map] using hb.symm
    subst a
    subst b
    simp [nextKind, hi]
  · intro i _
    simp

theorem kinds_adj (B : SrcpB) :
    Adj2 (fun a b => nextKind B a = some b) (kinds B) := by
  unfold kinds
  apply Adj2.append
  · apply Adj2.append
    · trivial
    · apply range_adj
      intro p hp
      simp [nextKind, hp]
    · intro a b ha hb
      have ha' : a = .root := by simpa using ha.symm
      have hb' : b = .leaf 0 := by simpa [List.range_succ_eq_map] using hb.symm
      subst a; subst b
      rfl
  · exact paths_adj B
  · intro a b ha hb
    have ha' : a = .leaf 31 := by
      simpa [List.getLast?_append, List.range_succ] using ha.symm
    by_cases hp : B.path.length = 0
    · simp [hp] at hb
    · obtain ⟨n, hn⟩ : ∃ n, B.path.length = n + 1 := ⟨B.path.length - 1, by omega⟩
      have hb' : b = .path 0 0 := by
        simpa [hn, List.range_succ_eq_map] using hb.symm
      subst a; subst b
      simp [nextKind, show 0 < B.path.length by omega]

/-- Adjacent rows either stay in one list or cross to the next root. -/
def RAdj (bs : List SrcpB) (a b : Nat × Kind) : Prop :=
  (nextKind (bs.getD a.1 default) a.2 = some b.2 ∧ b.1 = a.1) ∨
  (nextKind (bs.getD a.1 default) a.2 = none ∧ b = (a.1 + 1, .root))

private theorem adj_mono {α : Type} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) : ∀ {xs : List α}, Adj2 r xs → Adj2 s xs
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: xs, ⟨h1, h2⟩ => ⟨h a b h1, adj_mono h h2⟩

theorem recs_adj (bs : List SrcpB) : Adj2 (RAdj bs) (recs bs) := by
  unfold recs
  apply Adj2.flatMap
  · intro i _
    apply Adj2.map
    exact adj_mono (fun a b h => Or.inl ⟨h, rfl⟩) (kinds_adj (bs.getD i default))
  · apply range_adj'
    intro i hi a b ha hb
    rw [List.getLast?_map, kinds_last] at ha
    rw [List.head?_map, kinds_first] at hb
    cases ha; cases hb
    exact Or.inr ⟨next_last _, rfl⟩
  · intro i _
    simp [kinds]

theorem adjAt {bs : List SrcpB} {r : Nat} (hr : r + 1 < R bs) :
    RAdj bs ((recs bs).getD r default) ((recs bs).getD (r + 1) default) := by
  have hh := (recs_adj bs).get r hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < (recs bs).length by unfold R at hr; omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact hh

end ZkFormal.NearV3.Render.SrcpGen

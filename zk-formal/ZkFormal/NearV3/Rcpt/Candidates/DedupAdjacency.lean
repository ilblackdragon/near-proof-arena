import ZkFormal.NearV3.Rcpt.Candidates.DedupLayoutSize
import ZkFormal.NearV3.Rcpt.Render.Srcp.Adjacency

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near.Render Render.SrcpGen

/-- Duplicate headers have no internal successor; computed segments retain the
original exact byte and path-item succession. -/
def nextKind (B : SrcpB) (k : Kind) : Option Kind :=
  if B.dup then none else Render.SrcpGen.nextKind B k

theorem kinds_first (B : SrcpB) : (kinds B).head? = some .root := by
  cases hd : B.dup <;> simp [kinds, hd, Render.SrcpGen.kinds_first]

theorem next_last (B : SrcpB) : nextKind B (lastKind B) = none := by
  cases hd : B.dup <;> simp [nextKind, lastKind, hd, Render.SrcpGen.next_last]

theorem kinds_adj (B : SrcpB) :
    Adj2 (fun a b => nextKind B a = some b) (kinds B) := by
  cases hd : B.dup
  · simpa only [kinds, nextKind, hd, Bool.false_eq_true, ite_false] using
      Render.SrcpGen.kinds_adj B
  · simp [kinds, hd, Adj2]

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
    cases hd : (bs.getD i default).dup
    all_goals simp only [List.getD_eq_getElem?_getD] at hd
    all_goals simp [kinds, hd, Render.SrcpGen.kinds]

theorem adjAt {bs : List SrcpB} {r : Nat} (hr : r + 1 < R bs) :
    RAdj bs ((recs bs).getD r default) ((recs bs).getD (r + 1) default) := by
  have hh := (recs_adj bs).get r hr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < (recs bs).length by unfold R at hr; omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

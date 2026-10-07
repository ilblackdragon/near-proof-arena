import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficComplete

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near Render.SrcpGen

def lastKind (B : SrcpB) : Kind := if B.dup then .root else Render.SrcpGen.lastKind B

theorem R_pos {bs : List SrcpB} (hn : bs ≠ []) : 0 < R bs := by
  have hl : 0 < bs.length := by cases bs <;> simp_all
  rw [R_accounting]
  omega

theorem kinds_last (B : SrcpB) : (kinds B).getLast? = some (lastKind B) := by
  cases hd : B.dup <;> simp [kinds, lastKind, hd, Render.SrcpGen.kinds_last]

theorem recs_last {bs : List SrcpB} (hn : bs ≠ []) :
    (recs bs).getLast? = some (bs.length - 1, lastKind (bs.getD (bs.length - 1) default)) := by
  have hp : 0 < bs.length := by cases bs <;> simp_all
  obtain ⟨n, he⟩ : ∃ n, bs.length = n + 1 := ⟨bs.length - 1, by omega⟩
  unfold recs
  rw [he, List.range_succ, List.flatMap_append, List.getLast?_append]
  simp [List.getLast?_map, kinds_last]

theorem lastAt {bs : List SrcpB} (hn : bs ≠ []) :
    (recs bs).getD (R bs - 1) default =
      (bs.length - 1, lastKind (bs.getD (bs.length - 1) default)) := by
  have hh := recs_last hn
  rw [List.getLast?_eq_getElem?] at hh
  rw [List.getD_eq_getElem?_getD]
  unfold R
  rw [hh]
  rfl

theorem last_size (B : SrcpB) (before : Nat) :
    (frame B before (lastKind B)).sz = before + sizeStep B := by
  cases hd : B.dup
  · by_cases hp : B.path.length = 0
    · simp [lastKind, hd, Render.SrcpGen.lastKind, hp, frame, leafFrame, sizeStep]
    · have he : B.path.length - 1 + 1 = B.path.length := by omega
      simp [lastKind, hd, Render.SrcpGen.lastKind, hp, frame, pathFrame, sizeStep, he, Nat.add_assoc]
  · simp [lastKind, hd, frame, rootFrame, sizeStep]

private theorem take_next {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using congrArg (List.cons a) (ih i (by simpa using hi))

theorem size_take_next (bs : List SrcpB) (i : Nat) (hi : i < bs.length) :
    size (bs.take (i + 1)) = size (bs.take i) + sizeStep (bs.getD i default) := by
  rw [take_next bs i hi]
  simp only [size, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem last_size_cell {bs : List SrcpB} (hn : bs ≠ []) (repeated : Nat → Bool) :
    cell bs repeated (R bs - 1) SrcpV3.sz = size bs := by
  have hr : R bs - 1 < R bs := by have := R_pos hn; omega
  have hp : 0 < bs.length := by cases bs <;> simp_all
  have hi : bs.length - 1 < bs.length := by omega
  have he : bs.length - 1 + 1 = bs.length := by omega
  simp only [cell, hr, ↓reduceIte, lastAt hn, rowFrame, SrcpV3.sz]
  change (frame _ _ (lastKind _)).sz = _
  rw [last_size, ← size_take_next bs _ hi, he]
  simp

theorem cell_gz (bs : List SrcpB) (repeated : Nat → Bool) (r : Nat) :
    cell bs repeated r SrcpV3.gz = if r < R bs then (decide (r + 1 = R bs)).toNat else 0 := by
  simp [cell, rowFrame, SrcpV3.gz, SrcpV3.sz, Frame.cell]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

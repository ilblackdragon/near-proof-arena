import ZkFormal.NearV3.Rcpt.Candidates.DedupLayoutFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupNextMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near Render.SrcpGen

/-- Integer interpretation used to prove field constraints by the standard cast lemma. -/
def cellsI (bs : List SrcpB) (repeated : Nat → Bool) (r : Nat) : Nat → Int :=
  fun x => (cell bs repeated r x : Int)

theorem active_cellsI (bs : List SrcpB) (repeated : Nat → Bool) (r : Nat) (hr : r < R bs) :
    cellsI bs repeated r =
      let a := (recs bs).getD r default
      fun x => (localCells (bs.getD a.1 default) (size (bs.take a.1)) a.2
        (decide (r + 1 = R bs)) (repeated a.1) x : Int) := by
  unfold cellsI
  rw [active_cells bs repeated r hr]

theorem padding_cellsI (bs : List SrcpB) (repeated : Nat → Bool) (r : Nat) (hr : R bs ≤ r) :
    cellsI bs repeated r = fun x => if x = SrcpV3.sz then (size bs : Int) else 0 := by
  funext x
  by_cases hx : x = SrcpV3.sz <;> simp [cellsI, cell, Nat.not_lt.mpr hr, hx]

theorem getD_mem {bs : List SrcpB} {i : Nat} (hi : i < bs.length) : bs.getD i default ∈ bs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem TableFacts.block_at {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    (i : Nat) (hi : i < bs.length) : BlockFacts (bs.getD i default) :=
  h.block _ (getD_mem hi)

theorem first_sg {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep) :
    cellsI bs rep 0 SrcpV3.sg = 0 := by
  rw [active_cellsI bs rep 0 (by have := R_ge_33 h; omega), firstAt h]
  simp [localCells, frame, rootFrame, Frame.cell, SrcpV3.sg]
  split <;> rfl

theorem final_charge {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep) :
    size (bs.take (bs.length - 1)) + sizeStep (bs.getD (bs.length - 1) default) = size bs := by
  have hp : 0 < bs.length := by have hn := h.nonempty; cases bs <;> simp_all
  have he : bs.length - 1 + 1 = bs.length := by omega
  have hh := size_take_next bs (bs.length - 1) (by omega)
  simpa only [he, List.take_length] using hh.symm

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

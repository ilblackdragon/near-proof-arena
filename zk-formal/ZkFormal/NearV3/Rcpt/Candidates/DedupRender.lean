import ZkFormal.NearV3.Rcpt.Render.Srcp.Facts
import ZkFormal.NearV3.Rcpt.Candidates.SourceBudget

/-! Isolated executable candidate renderer. It deliberately has no active AIR/table
admission theorem: duplicate-header transitions and partition continuations must still
be constrained and proved. Existing source tables and public widths are unchanged. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra
open Render.SrcpGen

abbrev width : Nat := 57

def kinds (B : SrcpB) : List Kind :=
  if B.dup then [.root] else Render.SrcpGen.kinds B

def payloadRows (B : SrcpB) : Nat := if B.dup then 0 else 32 + 64 * B.path.length

def sizeStep (B : SrcpB) : Nat := B.L + if B.dup then 0 else 33 * B.path.length

def size (bs : List SrcpB) : Nat := (bs.map sizeStep).sum

/-- A duplicate root row consumes neither a SHA message nor a leaf/path row. Its
counter stays at the preceding computed message, and digest gating is disabled. -/
def frame (B : SrcpB) (before : Nat) (k : Kind) : Frame :=
  match k with
  | .root =>
    if B.dup then
      { rootFrame B before with qe := B.ql - 1, le := 0, cId := 0, cLen := 0, gD := false }
    else rootFrame B before
  | .leaf p => leafFrame B before p
  | .path i o => pathFrame B before i o

def recs (bs : List SrcpB) : List (Nat × Kind) :=
  (List.range bs.length).flatMap fun i =>
    (kinds (bs.getD i default)).map fun k => (i, k)

def R (bs : List SrcpB) : Nat := (recs bs).length

def rowFrame (bs : List SrcpB) (pos : Nat) (r : Nat × Kind) : Frame :=
  { frame (bs.getD r.1 default) (size (bs.take r.1)) r.2 with gz := decide (pos + 1 = R bs) }

/-- Column56 carries all-occurrence repetition metadata on root rows only. -/
def cell (bs : List SrcpB) (repeated : Nat → Bool) (pos x : Nat) : Nat :=
  if pos < R bs then
    let r := (recs bs).getD pos default
    if x = 56 then if r.2 = .root then (repeated r.1).toNat else 0
    else (rowFrame bs pos r).cell x
  else if x = SrcpV3.sz then size bs else 0

def rows (bs : List SrcpB) (repeated : Nat → Bool) : Array Row :=
  mkTab (2 ^ logOf (R bs)) width (cell bs repeated)

theorem kinds_length (B : SrcpB) : (kinds B).length = 1 + payloadRows B := by
  cases hb : B.dup <;> simp [kinds, payloadRows, hb, Render.SrcpGen.kinds_length] <;> omega

private theorem map_getD {α β : Type} (d : α) (f : α → β) (xs : List α) :
    (List.range xs.length).map (fun i => f (xs.getD i d)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < xs.length by simpa using h1)]

theorem R_eq (bs : List SrcpB) : R bs = (bs.map fun B => 1 + payloadRows B).sum := by
  simp only [R, recs, List.length_flatMap, List.length_map, kinds_length]
  exact congrArg List.sum (map_getD default (fun B : SrcpB => 1 + payloadRows B) bs)

/-- Exactly one root row per occurrence, with SHA payload rows only for computational representatives. -/
theorem R_accounting (bs : List SrcpB) :
    R bs = bs.length + 32 * (bs.filter (fun B => !B.dup)).length +
      64 * ((bs.filter (fun B => !B.dup)).map fun B => B.path.length).sum := by
  rw [R_eq]
  induction bs with
  | nil => simp
  | cons B rest ih =>
    simp only [payloadRows] at ih
    cases hd : B.dup <;>
      simp only [payloadRows, hd, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
        List.map_cons, List.sum_cons, List.length_cons, List.filter_cons,
        Bool.not_false, Bool.not_true, ih, Nat.mul_add, Nat.mul_one] <;> omega

/-- The established dedup envelope covers this renderer, including all skipped headers. -/
theorem R_bound (bs : List SrcpB) (hl : bs.length ≤ sourceLists)
    (hp : ((bs.filter (fun B => !B.dup)).map fun B => B.path.length).sum ≤ distinctPathItems) :
    R bs ≤ 16334272 := by
  rw [R_accounting]
  have hc := List.length_filter_le (fun B : SrcpB => !B.dup) bs
  simp only [sourceLists, distinctPathItems, witnessBytes] at *
  omega

theorem duplicate_header_only (B : SrcpB) (hd : B.dup = true) (before : Nat) :
    kinds B = [.root] ∧ (frame B before .root).gD = false ∧
      (frame B before .root).q = B.ql - 1 ∧ (frame B before .root).qe = B.ql - 1 ∧
      (frame B before .root).sz = before + B.L := by
  simp [kinds, frame, hd, rootFrame]

theorem rows_capacity (bs : List SrcpB) (repeated : Nat → Bool) :
    R bs ≤ (rows bs repeated).size := by
  rw [rows, mkTab_size]
  exact le_pow_logOf _

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

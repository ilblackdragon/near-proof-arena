import ZkFormal.NearV3.Sched.Complete.Trace
import ZkFormal.NearV3.Sched.Gen.Mem

/-!
# ZkFormal.NearV3.Sched.Complete.MemRows — the honest memory rows as value records (M4)

* `MV`: the 18 cells of a `smmV3` row; `MV.cell` reads column `c < 18`;
* `initV g`, `opV g i tp o`, `segVs g`: the rows of a segment `g` (INIT, then one row per op;
  `tp` = previous op time, `lst` on the last row), `memVs segs` = all rows;
* `RowRel a V`: array `a` has cells `V` (columns `< 18`) and every cell `< P` when `V`'s are;
* `rows_rel`: the generator's rows `Gen.Mem.rows R` are `memVs R.segs`, row by row.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- The cells of a memory row. -/
structure MV where
  act : Nat
  fst : Nat
  lst : Nat
  isRd : Nat
  isGr : Nat
  addr : Nat
  t : Nat
  tp : Nat
  vin : Nat
  v : Nat
  wp : Nat
  w : Nat
  al : Nat
  isL : Nat
  inc : Nat
  ok : Nat
  cc : Nat
  sf : Nat

namespace MV

def cell (X : MV) (c : Nat) : Nat :=
  if c = 0 then X.act else if c = 1 then X.fst else if c = 2 then X.lst else if c = 3 then X.isRd
  else if c = 4 then X.isGr else if c = 5 then X.addr else if c = 6 then X.t else if c = 7 then X.tp
  else if c = 8 then X.vin else if c = 9 then X.v else if c = 10 then X.wp else if c = 11 then X.w
  else if c = 12 then X.al else if c = 13 then X.isL else if c = 14 then X.inc else if c = 15 then X.ok
  else if c = 16 then X.cc else if c = 17 then X.sf else 0

/-- Every cell `< P`. -/
def Small (X : MV) : Prop := ∀ c, X.cell c < P

end MV

def padV : MV := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- INIT row of segment `g`. -/
def initV (g : Seg) : MV :=
  ⟨1, 1, b2n (g.ops.length == 0), 0, 0, g.addr, 0, 0, g.vin0, g.v0, g.w0, g.w0, b2n g.al, b2n g.isL,
   g.w0, 0, b2n g.isL, 0⟩

/-- Op row `i ≥ 1` of segment `g` (op `o`, previous time `tp`). -/
def opV (g : Seg) (i tp : Nat) (o : MOp) : MV :=
  ⟨1, 0, b2n (i == g.ops.length), b2n (o.op == OP_READ), b2n (o.op == OP_GRANT), g.addr, o.t, tp,
   o.vin, o.v, o.wp, o.w, b2n g.al, b2n g.isL, o.inc, b2n o.ok, b2n o.c, b2n o.sf⟩

/-- Op rows after `k` ops, previous time `tp`. -/
def opsVs (g : Seg) : Nat → Nat → List MOp → List MV
  | _, _, [] => []
  | k, tp, o :: os => opV g (k + 1) tp o :: opsVs g (k + 1) o.t os

def segVs (g : Seg) : List MV := initV g :: opsVs g 0 0 g.ops

def memVs (segs : List Seg) : List MV := segs.flatMap segVs

theorem opsVs_length (g : Seg) : ∀ k tp os, (opsVs g k tp os).length = os.length
  | _, _, [] => rfl
  | k, tp, _ :: os => by simp [opsVs, opsVs_length g (k + 1) _ os]

theorem segVs_length (g : Seg) : (segVs g).length = g.ops.length + 1 := by
  simp [segVs, opsVs_length]

theorem memVs_length (segs : List Seg) : (memVs segs).length = (segs.map fun g => g.ops.length + 1).sum := by
  induction segs with
  | nil => rfl
  | cons g segs ih => simp only [memVs, List.flatMap_cons, List.length_append, segVs_length] at *; simp [ih]

/-! ## Arrays and records -/

/-- Array `a` has 18 cells, those of `V`. -/
def RowRel (a : Array Nat) (V : MV) : Prop := (∀ c, c < 18 → gd a c = V.cell c) ∧ a.size = 18

theorem gd_ge (a : Array Nat) {c : Nat} (h : a.size ≤ c) : gd a c = 0 := by
  unfold gd; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

theorem RowRel.cell {a : Array Nat} {V : MV} (h : RowRel a V) (c : Nat) : gd a c = V.cell c := by
  by_cases hc : c < 18
  · exact h.1 c hc
  · rw [gd_ge a (by rw [h.2]; omega)]
    unfold MV.cell
    repeat rw [if_neg (by omega)]

theorem gd_set_lt {a : Array Nat} {i v : Nat} (hv : v < P) (ha : ∀ c, gd a c < P) (c : Nat) :
    gd (a.set! i v) c < P := by
  rw [gd_set]; split
  · exact hv
  · exact ha c

theorem gd_zrow_lt (w c : Nat) : gd (zrow w) c < P := by rw [gd_zrow]; decide

theorem b2n_lt (b : Bool) : b2n b < P := by cases b <;> decide

theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide

/-- The INIT array of the generator. -/
def initArr (g : Seg) : Array Nat :=
  (zrow Mem.width).set! Mem.act 1 |>.set! Mem.addr g.addr |>.set! Mem.al (b2n g.al)
    |>.set! Mem.isL (b2n g.isL) |>.set! Mem.fst 1 |>.set! Mem.lst (b2n (g.ops.length == 0))
    |>.set! Mem.vin g.vin0 |>.set! Mem.v g.v0 |>.set! Mem.wp g.w0 |>.set! Mem.w g.w0
    |>.set! Mem.inc g.w0 |>.set! Mem.cc (b2n g.isL)

/-- The op array of the generator (`i` = op index + 1, `tp` = previous time). -/
def opArr (g : Seg) (i tp : Nat) (o : MOp) : Array Nat :=
  (zrow Mem.width).set! Mem.act 1 |>.set! Mem.addr g.addr |>.set! Mem.al (b2n g.al)
    |>.set! Mem.isL (b2n g.isL) |>.set! Mem.lst (b2n (i == g.ops.length))
    |>.set! Mem.isRd (b2n (o.op == OP_READ)) |>.set! Mem.isGr (b2n (o.op == OP_GRANT))
    |>.set! Mem.t o.t |>.set! Mem.tp tp |>.set! Mem.vin o.vin |>.set! Mem.v o.v |>.set! Mem.wp o.wp
    |>.set! Mem.w o.w |>.set! Mem.inc o.inc |>.set! Mem.ok (b2n o.ok) |>.set! Mem.cc (b2n o.c)
    |>.set! Mem.sf (b2n o.sf)

/-- One step of the generator's op loop. -/
def stepF (g : Seg) (b : Array (Array Nat) × Nat × Nat) (o : MOp) : Array (Array Nat) × Nat × Nat :=
  (b.1.push (opArr g (b.2.2 + 1) b.2.1 o), o.t, b.2.2 + 1)

theorem segRows_eq (g : Seg) : Gen.Mem.segRows g = (g.ops.foldl (stepF g) (#[initArr g], 0, 0)).1 := by
  unfold Gen.Mem.segRows
  simp only [Id.run, List.forIn_pure_yield_eq_foldl]
  rfl

/-- Smallness of a segment's values. -/
def SegSmall (g : Seg) : Prop :=
  g.addr < P ∧ g.vin0 < P ∧ g.v0 < P ∧ g.w0 < P ∧
    ∀ o ∈ g.ops, o.t < P ∧ o.vin < P ∧ o.v < P ∧ o.wp < P ∧ o.w < P ∧ o.inc < P

section
open Mem in
theorem initArr_rel (g : Seg) (hs : SegSmall g) : RowRel (initArr g) (initV g) := by
  obtain ⟨ha, hvi, hv, hw, -⟩ := hs
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨
      c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [initArr, initV, MV.cell, gd_set, gd_setIf, gd_zrow, size_set, size_zrow, Mem.width, Mem.act,
      Mem.fst, Mem.lst, Mem.isRd, Mem.isGr, Mem.addr, Mem.t, Mem.tp, Mem.vin, Mem.v, Mem.wp, Mem.w,
      Mem.al, Mem.isL, Mem.inc, Mem.ok, Mem.cc, Mem.sf, ↓reduceIte, and_self, and_true, true_and,
      and_false, false_and]
  · simp [initArr, size_set, size_zrow, Mem.width]

theorem opArr_rel (g : Seg) (i tp : Nat) (o : MOp) (htp : tp < P)
    (ho : o.t < P ∧ o.vin < P ∧ o.v < P ∧ o.wp < P ∧ o.w < P ∧ o.inc < P) (ha : g.addr < P) :
    RowRel (opArr g i tp o) (opV g i tp o) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ho
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨
      c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [opArr, opV, MV.cell, gd_set, gd_setIf, gd_zrow, size_set, size_zrow, Mem.width, Mem.act,
      Mem.fst, Mem.lst, Mem.isRd, Mem.isGr, Mem.addr, Mem.t, Mem.tp, Mem.vin, Mem.v, Mem.wp, Mem.w,
      Mem.al, Mem.isL, Mem.inc, Mem.ok, Mem.cc, Mem.sf, ↓reduceIte, and_self, and_true, true_and,
      and_false, false_and]
  · simp [opArr, size_set, size_zrow, Mem.width]
end

/-! ## Lists of rows -/

inductive RRel : List (Array Nat) → List MV → Prop
  | nil : RRel [] []
  | cons {a V L1 L2} : RowRel a V → RRel L1 L2 → RRel (a :: L1) (V :: L2)

theorem RRel.append {a b c d} (h1 : RRel a b) (h2 : RRel c d) : RRel (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem RRel.length {a b} (h : RRel a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RRel.get {a b} (h : RRel a b) : ∀ i (h1 : i < a.length) (h2 : i < b.length), RowRel a[i] b[i] := by
  induction h with
  | nil => intro i h1; simp at h1
  | cons hr _ ih =>
    intro i h1 h2
    cases i with
    | zero => exact hr
    | succ i => exact ih i (by simpa using h1) (by simpa using h2)

/-- Times before op `k` (`tp` = previous op time) are `< P` along the loop. -/
theorem foldl_rel (g : Seg) (hs : SegSmall g) :
    ∀ (os : List MOp) (out : Array (Array Nat)) (outVs : List MV) (tp k : Nat),
      (∀ o ∈ os, o ∈ g.ops) → tp < P → RRel out.toList outVs →
      RRel (os.foldl (stepF g) (out, tp, k)).1.toList (outVs ++ opsVs g k tp os)
  | [], out, outVs, tp, k, _, _, h => by simpa [opsVs] using h
  | o :: os, out, outVs, tp, k, hm, htp, h => by
    rw [List.foldl_cons]
    have ho := hs.2.2.2.2 o (hm o List.mem_cons_self)
    have := foldl_rel g hs os (out.push (opArr g (k + 1) tp o)) (outVs ++ [opV g (k + 1) tp o]) o.t (k + 1)
      (fun x hx => hm x (List.mem_cons_of_mem _ hx)) ho.1
      (by rw [Array.toList_push]; exact h.append (.cons (opArr_rel g _ _ _ htp ho hs.1) .nil))
    simpa [opsVs, stepF] using this

theorem segRows_rel (g : Seg) (hs : SegSmall g) : RRel (Gen.Mem.segRows g).toList (segVs g) := by
  rw [segRows_eq]
  have := foldl_rel g hs g.ops #[initArr g] [initV g] 0 0 (fun _ h => h) (by decide)
    (.cons (initArr_rel g hs) .nil)
  simpa [segVs] using this

theorem foldl_append_toList (f : Seg → Array (Array Nat)) :
    ∀ (segs : List Seg) (acc : Array (Array Nat)),
      (segs.foldl (fun acc g => acc ++ f g) acc).toList = acc.toList ++ segs.flatMap (fun g => (f g).toList)
  | [], acc => by simp
  | g :: segs, acc => by
    rw [List.foldl_cons, foldl_append_toList f segs, List.flatMap_cons, Array.toList_append, List.append_assoc]

theorem flat_rel : ∀ (segs : List Seg), (∀ g ∈ segs, SegSmall g) →
    RRel (segs.flatMap fun g => (Gen.Mem.segRows g).toList) (memVs segs)
  | [], _ => .nil
  | g :: segs, hs => by
    rw [List.flatMap_cons]
    exact (segRows_rel g (hs g List.mem_cons_self)).append
      (flat_rel segs fun g' h => hs g' (List.mem_cons_of_mem _ h))

/-- **The generated memory rows are the records `memVs R.segs`.** -/
theorem rows_rel (R : Run) (hs : ∀ g ∈ R.segs, SegSmall g) :
    RRel (Gen.Mem.rows R).toList (memVs R.segs) := by
  unfold Gen.Mem.rows
  rw [foldl_append_toList Gen.Mem.segRows R.segs #[]]
  simpa using flat_rel R.segs hs

end ZkFormal.NearV3.Sched.Complete

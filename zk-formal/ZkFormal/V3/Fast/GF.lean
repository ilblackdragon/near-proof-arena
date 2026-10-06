import NearSpecV3.ReedSolomon

/-!
# GF(2⁸) multiplication by table and the Reed–Solomon matrix (candidate-side `@[csimp]`)

`gfMul` (8 rounds of carry-less multiply-and-reduce on `Nat`) dominates `RSCode.new`
(`buildMatrix`: Vandermonde powers, Gauss–Jordan inverse, product; then the `MUL_TABLE`
rows). `gfMulT` reads a 65 536-entry table built *from `gfMul` itself* (so equality is by
construction, `gfMul_eq_T`, kernel-checked) and the matrix functions are recompiled with
identical bodies after the `@[csimp]` lemma (`rfl`, or induction for `gfPow`).
-/

namespace ZkFormal.V3.Fast

open NearSpecV3

/-- `gfMul a b` for `a, b < 256` at index `256·a + b`. -/
def gfTable : Array Nat := ((List.range 65536).map fun i => gfMul (i / 256) (i % 256)).toArray

def gfMulT (a b : Nat) : Nat :=
  if h : a < 256 ∧ b < 256 then
    gfTable[a * 256 + b]'(by simp [gfTable]; omega)
  else gfMul a b

theorem gfMul_eq_T : @gfMul = @gfMulT := by
  funext a b
  unfold gfMulT
  split
  · rename_i h
    simp only [gfTable, List.getElem_toArray, List.getElem_map, List.getElem_range]
    have h1 : (a * 256 + b) / 256 = a := by omega
    have h2 : (a * 256 + b) % 256 = b := by omega
    rw [h1, h2]
  · rfl

@[csimp] theorem gfMul_csimp : @gfMul = @gfMulT := gfMul_eq_T

def gfPowF (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => gfMul (gfPowF a n) a

theorem gfPow_eq_F : @gfPow = @gfPowF := by
  funext a n
  induction n with
  | zero => rfl
  | succ n ih => simp only [gfPow, gfPowF, ih]

@[csimp] theorem gfPow_csimp : @gfPow = @gfPowF := gfPow_eq_F

def gfInvF (b : Nat) : Nat := gfPow b 254

@[csimp] theorem gfInvF_csimp : @gfInv = @gfInvF := rfl

def gfDivF (a b : Nat) : Nat := if a = 0 then 0 else gfMul a (gfInv b)

@[csimp] theorem gfDivF_csimp : @gfDiv = @gfDivF := rfl

def GFMat_identityF (n : Nat) : GFMat :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0

@[csimp] theorem GFMat_identityF_csimp : @GFMat.identity = @GFMat_identityF := rfl

def GFMat_vandermondeF (rows cols : Nat) : GFMat :=
  (List.range rows).map fun r => (List.range cols).map fun c => gfPow r c

@[csimp] theorem GFMat_vandermondeF_csimp : @GFMat.vandermonde = @GFMat_vandermondeF := rfl

def gfSumF (l : List Nat) : Nat := l.foldl (· ^^^ ·) 0

@[csimp] theorem gfSumF_csimp : @gfSum = @gfSumF := rfl

def GFMat_multiplyF (lhs rhs : GFMat) : GFMat :=
  let cols := (List.range (rhs.headD []).length).map fun c => rhs.map fun row => row.getD c 0
  lhs.map fun row => cols.map fun col => gfSum (List.zipWith gfMul row col)

@[csimp] theorem GFMat_multiplyF_csimp : @GFMat.multiply = @GFMat_multiplyF := rfl

def GFMat_subMatrixF (m : GFMat) (rmin cmin rmax cmax : Nat) : GFMat :=
  ((m.drop rmin).take (rmax - rmin)).map fun row => (row.drop cmin).take (cmax - cmin)

@[csimp] theorem GFMat_subMatrixF_csimp : @GFMat.subMatrix = @GFMat_subMatrixF := rfl

def GFMat_augmentF (lhs rhs : GFMat) : GFMat := List.zipWith (· ++ ·) lhs rhs

@[csimp] theorem GFMat_augmentF_csimp : @GFMat.augment = @GFMat_augmentF := rfl

def GFMat_swapRowsF (m : GFMat) (r1 r2 : Nat) : GFMat :=
  if r1 = r2 then m else
    let a := m.getD r1 []
    let b := m.getD r2 []
    (m.set r1 b).set r2 a

@[csimp] theorem GFMat_swapRowsF_csimp : @GFMat.swapRows = @GFMat_swapRowsF := rfl

def GFMat_addScaledRowF (m : GFMat) (dst src scale : Nat) : GFMat :=
  let s := m.getD src []
  m.set dst (List.zipWith (fun x y => x ^^^ gfMul scale y) (m.getD dst []) s)

@[csimp] theorem GFMat_addScaledRowF_csimp : @GFMat.addScaledRow = @GFMat_addScaledRowF := rfl

def GFMat_pivotF (m : GFMat) (n r : Nat) : GFMat :=
  if m.get r r = 0 then
    match (List.range' (r + 1) (n - (r + 1))).find? (fun rb => m.get rb r != 0) with
    | some rb => m.swapRows r rb
    | none => m
  else m

@[csimp] theorem GFMat_pivotF_csimp : @GFMat.pivot = @GFMat_pivotF := rfl

def GFMat_forwardStepF (n : Nat) (m : GFMat) (r : Nat) : Option GFMat :=
  let m := m.pivot n r
  let p := m.get r r
  if p = 0 then none else
  -- Scale to 1 (`matrix.rs:209-215`): row r ← div(1, p) · row r.
  let m := if p ≠ 1 then
      let scale := gfDiv 1 p
      m.set r ((m.getD r []).map fun x => gfMul scale x)
    else m
  -- Clear below (`matrix.rs:216-229`).
  some <| (List.range' (r + 1) (n - (r + 1))).foldl (fun m rb =>
    let s := m.get rb r
    if s ≠ 0 then m.addScaledRow rb r s else m) m

@[csimp] theorem GFMat_forwardStepF_csimp : @GFMat.forwardStep = @GFMat_forwardStepF := rfl

def GFMat_gaussElimF (m : GFMat) (n : Nat) : Option GFMat := do
  let m ← (List.range n).foldlM (GFMat.forwardStep n) m
  -- Clear above the diagonal (`matrix.rs:232-245`).
  pure <| (List.range n).foldl (fun m d =>
    (List.range d).foldl (fun m ra =>
      let s := m.get ra d
      if s ≠ 0 then m.addScaledRow ra d s else m) m) m

@[csimp] theorem GFMat_gaussElimF_csimp : @GFMat.gaussElim = @GFMat_gaussElimF := rfl

def GFMat_invertF (m : GFMat) (n : Nat) : Option GFMat := do
  let w ← (m.augment (GFMat.identity n)).gaussElim n
  pure (w.subMatrix 0 n n (2 * n))

@[csimp] theorem GFMat_invertF_csimp : @GFMat.invert = @GFMat_invertF := rfl

def buildMatrixF (d t : Nat) : Option GFMat := do
  let v := GFMat.vandermonde t d
  let topInv ← (v.subMatrix 0 0 d d).invert d
  pure (v.multiply topInv)

@[csimp] theorem buildMatrixF_csimp : @buildMatrix = @buildMatrixF := rfl

def mulRowF (c : Nat) : Array UInt8 := ((List.range 256).map fun i => UInt8.ofNat (gfMul c i)).toArray

@[csimp] theorem mulRowF_csimp : @mulRow = @mulRowF := rfl

def RSCode_newF (d t : Nat) : Option RSCode := do
  if !rsParamsOk d t then none
  let m ← buildMatrix d t
  pure { d, parityTables := (m.drop d).map fun row => row.map mulRow }

@[csimp] theorem RSCode_newF_csimp : @RSCode.new = @RSCode_newF := rfl

end ZkFormal.V3.Fast

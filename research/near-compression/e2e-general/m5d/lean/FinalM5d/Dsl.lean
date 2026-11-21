import ZkFormal.Air.Basic

/-!
# FinalM5d.Dsl — named-column layouts and expression helpers (as lane B's `StateM5a.Dsl`)

A table's columns are a `Layout`: a list of `(name, count)` groups in order. `Layout.off L s` is
the first column of group `s`; `Layout.names L` is the per-column name list that `m5d-tool`
exports next to the AIR, so the trace generator addresses columns by name.
-/

namespace FinalM5d

open ZkFormal.Air

abbrev Layout := List (String × Nat)

def Layout.off : Layout → String → Nat
  | [], _ => 0
  | (n, k) :: r, s => if n == s then 0 else k + Layout.off r s

def Layout.width (L : Layout) : Nat := (L.map (·.2)).sum

def Layout.names (L : Layout) : List String :=
  L.flatMap fun (n, k) => if k == 1 then [n] else (List.range k).map fun j => s!"{n}.{j}"

instance : Add Expr := ⟨.add⟩
instance : Mul Expr := ⟨.mul⟩
instance : Neg Expr := ⟨.neg⟩
instance : Sub Expr := ⟨fun a b => .add a (.neg b)⟩
instance (n : Nat) : OfNat Expr n := ⟨.const n⟩

def K (v : Nat) : Expr := .const v
def P (i : Nat) : Expr := .pub i

/-- Sum of a list as a **balanced** tree of additions (the export's JSON nesting stays
logarithmic; the prover's JSON reader has a recursion limit). -/
def sumE (l : List Expr) : Expr :=
  match l with
  | [] => .const 0
  | [a] => a
  | a :: b :: r =>
    let h := (r.length + 2) / 2
    .add (sumE ((a :: b :: r).take h)) (sumE ((a :: b :: r).drop h))
termination_by l.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

def bool (x : Expr) : Expr := x * (x - 1)

def snd (bus : Nat) (m : Expr) (msg : List Expr) : Interaction :=
  { bus, mult := [m], msg, send := true }
def rcv (bus : Nat) (m : Expr) (msg : List Expr) : Interaction :=
  { bus, mult := [m], msg, send := false }
def sndBits (bus : Nat) (bits : List Expr) (msg : List Expr) : Interaction :=
  { bus, mult := bits, msg, send := true }

structure Cols where
  L : Layout

def Cols.c (T : Cols) (s : String) (j : Nat := 0) : Expr := .col (T.L.off s + j) false
def Cols.n (T : Cols) (s : String) (j : Nat := 0) : Expr := .col (T.L.off s + j) true
/-- `j` consecutive columns of group `s` as a list. -/
def Cols.cs (T : Cols) (s : String) (k : Nat) (o : Nat := 0) : List Expr :=
  (List.range k).map fun j => T.c s (o + j)
def Cols.ns (T : Cols) (s : String) (k : Nat) (o : Nat := 0) : List Expr :=
  (List.range k).map fun j => T.n s (o + j)

/-- Little-endian value of bytes. -/
def leVal (bs : List Expr) : Expr := sumE ((List.range bs.length).map fun i => K (256 ^ i) * bs.getD i 0)

/-- 42 digest bytes as 14 limbs of 3 bytes, big-endian within a limb (U-10). -/
def limbs3 (bs : List Expr) : List Expr :=
  (List.range 14).map fun i => K 65536 * bs.getD (3 * i) 0 + K 256 * bs.getD (3 * i + 1) 0 + bs.getD (3 * i + 2) 0

/-- Pairwise equality constraints `g · (a_i − b_i)`. -/
def eqs (g : Expr) (a b : List Expr) : List Expr := (List.zip a b).map fun (x, y) => g * (x - y)

/-- Constant byte strings. -/
def consts (bs : List Nat) : List Expr := bs.map K

/-! ## Buses (local numbering; the prover maps `IF384` = 16 to the native chip's bus 103) -/

def B_SHA_BYTES : Nat := 0
def B_SHA_DIGEST : Nat := 1
/-- `(id, pos, byte)` into a SHA-384 message (`S384`). -/
def B_SB : Nat := 2
/-- `(id, len, digest[48])` of a SHA-384 message. -/
def B_SD : Nat := 3
/-- `(v)`, `v < 256`. -/
def B_R8 : Nat := 4
/-- `(v, v mod 4, v / 4)`, `v < 256`. -/
def B_S2 : Nat := 5
/-- `(v, v mod 32, v / 32)`, `v < 256`. -/
def B_S5 : Nat := 6
/-- `(k, byte)`: byte `k` of the statement stream (to `FIN`). -/
def B_HB : Nat := 7
/-- `(chain, i, acc[42])`: the running accumulator before item `i`. -/
def B_CHD : Nat := 8
/-- `(tree, level, index, digest[32])`. -/
def B_NODE : Nat := 9
/-- `(tree, root[32])`. -/
def B_ROOT : Nat := 10
/-- `(tree, leaf count)`. -/
def B_TSTART : Nat := 11
/-- `(part, offset, byte)`: a Reed–Solomon data byte. -/
def B_RSD : Nat := 12
/-- the segment descriptor `(i, kind, len, start, shaId, shaBase, sId)`. -/
def B_SEGD : Nat := 13
/-- `(k, byte)`: a fixed body byte (the `u32` count prefixes). -/
def B_PFX : Nat := 14
/-- the layout's shard ids, once. -/
def B_SIDS : Nat := 15
def B_IF384 : Nat := 16
/-- `(q, shard id)`. -/
def B_SID : Nat := 17
/-- `(q, count, bytes)`: shard `q`'s receipt count and byte length. -/
def B_SCNT : Nat := 18
def NUM_BUSES : Nat := 19

end FinalM5d

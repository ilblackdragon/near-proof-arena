import ZkFormal.Air.Basic

/-!
# StateM5a.Dsl — named-column layouts and expression helpers for the M5a tables

A table's columns are a `Layout`: a list of `(name, count)` groups laid out in order.
`Layout.off L s` is the first column of group `s`; `Layout.names L` is the per-column name list
that `m5a-tool air` exports next to the AIR, so the Python trace generator addresses columns by
name and never by hand-copied offsets.
-/

namespace StateM5a

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

/-- Sum of a list (`0` for the empty list). -/
def sumE : List Expr → Expr
  | [] => .const 0
  | [a] => a
  | a :: r => .add a (sumE r)

/-- `x · (x − 1)`: booleanity. -/
def bool (x : Expr) : Expr := x * (x - 1)

/-- One-bit send / receive. -/
def snd (bus : Nat) (m : Expr) (msg : List Expr) : Interaction :=
  { bus, mult := [m], msg, send := true }
def rcv (bus : Nat) (m : Expr) (msg : List Expr) : Interaction :=
  { bus, mult := [m], msg, send := false }
/-- Send with a multiplicity given by bit columns (lookup providers). -/
def sndBits (bus : Nat) (bits : List Expr) (msg : List Expr) : Interaction :=
  { bus, mult := bits, msg, send := true }

/-- 32 bytes (big-endian pairs) as 16 limbs of 16 bits: limb `i = 256·b(2i) + b(2i+1)`. -/
def pack2 (b : Nat → Expr) : List Expr :=
  (List.range 16).map fun i => K 256 * b (2 * i) + b (2 * i + 1)

/-- Little-endian 16-bit limb `k` of 8 bytes. -/
def limb16 (b : Nat → Expr) (k : Nat) : Expr := b (2 * k) + K 256 * b (2 * k + 1)

/-- Constant multiple. -/
def sm (v : Nat) (e : Expr) : Expr := .mul (.const v) e

/-- A table-local column accessor. -/
structure Cols where
  L : Layout

def Cols.c (T : Cols) (s : String) (j : Nat := 0) : Expr := .col (T.L.off s + j) false
def Cols.n (T : Cols) (s : String) (j : Nat := 0) : Expr := .col (T.L.off s + j) true
def Cols.i (T : Cols) (s : String) (j : Nat := 0) : Nat := T.L.off s + j

/-! ## Buses (table-local numbering; the prover maps `IF384` to the native SHA-512 chip's
interface bus and offsets the others). -/

def B_SHA_BYTES : Nat := 0
def B_SHA_DIGEST : Nat := 1
/-- `(kid, idx, nibble)`: nibble `idx` of key `kid`. -/
def B_NIB : Nat := 2
/-- `(kid, L)`: key `kid` has `L` nibbles. -/
def B_KLEN : Nat := 3
/-- `(kid, sha256(key) as 16 limbs)`. -/
def B_KDIG : Nat := 4
/-- `(w, d, oldHash16, kid, mode, vlen, vh16)`: walk `w` enters a node at depth `d`. -/
def B_DOWN : Nat := 5
/-- `(w, d, rk, h16, nm4, om4, kid2, st2, alen, avh16, fpres)`: the result of a node. -/
def B_UP : Nat := 6
def B_SIBQ : Nat := 7
def B_SIBA : Nat := 8
def B_MATQ : Nat := 9
def B_MATR : Nat := 10
/-- `(phase, level, index, digest18)`: working-set Merkle tree. -/
def B_TREE : Nat := 11
/-- `(j, root18)`: working-set root after `j` write accesses. -/
def B_RCH : Nat := 12
/-- `(kd16, pres, vlen, vh16)`: a committed write (public in M5a, from STATE rows in M5b). -/
def B_WRITE : Nat := 13
/-- `(j, trieRoot16)`: the post-state trie root after `j` applied changes. -/
def B_TCH : Nat := 14
/-- `(ka, kb)`: key `ka` < key `kb` (byte-lexicographic). -/
def B_ORD : Nat := 15
/-- The native SHA-512 compression chip's interface `(cid, pair, 3 limbs, 3 limbs)`. -/
def B_IF384 : Nat := 16

/-- Split request `(w, e, kid, kid2, xl, A1[16], L, A2[4], vlen, vh16)`: an old leaf / extension
visited at a walk's depth asks for the new branch at depth `e` (the first differing nibble); the
old-side child is a leaf `K_kid2[e+1..] ↦ (L, A1)` (`xl = 1`) or a node `(A1 hash, A2 memory)`. -/
def B_SPQ : Nat := 17
/-- Split result `(w, depth, hash16, mem4)`: the new subtree rooted at `depth`. -/
def B_SPR : Nat := 18
/-- `(w, d, e, kid)`: a new extension over `K_kid[d..e)` above the split branch at `e`. -/
def B_EPQ : Nat := 19
/-- `(w, d, kid, end, childHash16, childMem4)`: a re-keyed extension `K_kid[d..end)` (split). -/
def B_SXQ : Nat := 20
def B_SXR : Nat := 21
/-- Key continuation `(rid, c, p, kA, fA, kB, gB, gO, gN)`: chunk `c` of row `rid`'s node key. -/
def B_KC : Nat := 22
/-- `(rid, c, nibbles from chunk c on)`. -/
def B_KCR : Nat := 23
/-- `(v)`: `v < 256` (the `RNG` table). -/
def B_RNG : Nat := 24
/-- Node versions `(tag, refFlag, ref16, record…)`: a node's record addressed by its *ref* — a
SHA-256 digest (`refFlag = 0`, provided by a row that hashed the record) or a version id
(`refFlag = 1`, the producing row's new-node id; never hashed).  Batched FINAL (M5a-2). -/
def B_VER : Nat := 25

def NUM_BUSES : Nat := 26

/-- `VER` record tags. -/
def VT_BR : Nat := 1
def VT_SN : Nat := 2
/-- Bits of a `VER` provider's multiplicity (readers of one version). -/
def VBITS : Nat := 7

/-! ## Result kinds on `UP` -/
def RK_ANS : Nat := 0
def RK_H : Nat := 1
def RK_HB : Nat := 2
def RK_HE : Nat := 3
def RK_LD : Nat := 4
def RK_NONE : Nat := 5
/-- The subtree is unchanged (`PTrie.del` returned `deleted = false`); the hash field is the
node's own (old) hash. -/
def RK_SAME : Nat := 6

/-! ## SHA-256 message-id spaces -/
def ID_KEY : Nat := 2 ^ 24
def ID_BR : Nat := 2 * 2 ^ 24
def ID_SN : Nat := 3 * 2 ^ 24
/-- SHA-256 message ids of the STATE (`STB`) messages: `ID_ST + m` (M5b; same SHA-256 table). -/
def ID_ST : Nat := 4 * 2 ^ 24
/-- Walk ids of the FINAL changes (INTAKE finds use the leaf index). -/
def W_FINAL : Nat := 2 ^ 20

end StateM5a

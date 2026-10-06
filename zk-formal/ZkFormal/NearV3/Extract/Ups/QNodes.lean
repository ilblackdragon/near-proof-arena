import NearSpec.TrieUpsert
import ZkFormal.NearV3.Spec.Codec

/-!
# ZkFormal.NearV3.Extract.Ups.QNodes — the new path nodes `Q_j` by part kind (spec side)

The node that part `j` of kind `k` must serialize to (`nodeEnc`), built from the source
record's node `P` (the path record the part reads), the case data (`I`, the terminal row
`t* = si + 1`, the record nibble `x`), the new value `v` and the node(s) of the part(s) below,
exactly as `PTrie.upsert` builds it (`TrieUpsert.lean`):

| kind | node |
|---|---|
| `RLP` | `newLeaf k v` (present leaf) |
| `RBR` / `RBV` | `.branch (some (.val v)) cs (m + valueMem |v| − valueMem slen)` (`− 0` without a value) |
| `RBI` | `.branch bv (cs[y] := newLeaf ys v) (m + leafMem ys |v| − 0)` (`Kids.upsert .none`) |
| `NLF` | `newLeaf ys v`, `ys = [0,15].drop (si + 1)` |
| `MVL` | `.leaf xs s (leafMem xs slen)`, `xs = k.drop (I + 1)` |
| `MVE` | `.ext xs c (extOwnMem xs + (m − extOwnMem k))` |
| `SPB` | the branch of `splitLeaf` / `splitExt` (before `wrapExt`) |
| `WEX` | `wrapExt p b`, `p = k.take I` |
| `RDB` | `.branch bv (cs[n] := c') (m + c'.memD − cm)` |
| `RDE`, `PT` | `.ext k c' (m + c'.memD − cm)` (`k = []` for `PT`) |

These are the targets of the layer-2 byte statement (`rowsB part = nodeEnc q`) and of M7e
(`q_root = upsert (prune P) [0,15] v`).
-/

namespace ZkFormal.NearV3.UpsSpec

open NearSpec

/-- The upsert key. -/
def key : List Nat := [0, 15]

/-- The new leaf's key after the terminal row `t* = si + 1` (`ys`), and the nibble `y`. -/
def ysOf (si : Nat) : List Nat := key.drop (si + 1)
def yOf (si : Nat) : Nat := key.getD si 16

/-- Child slot `n` set to `c`. -/
def setKid : Kids → Nat → PTrie → Kids
  | .nil, _, _ => .nil
  | .none r, 0, c => .some c r
  | .some _ r, 0, c => .some c r
  | .none r, n + 1, c => .none (setKid r n c)
  | .some d r, n + 1, c => .some d (setKid r n c)

/-! ## Terminal parts -/

def qRLP (k : List Nat) (v : Bytes) : PTrie := newLeaf k v

def qRBR (s : Slot) (cs : Kids) (m : Nat) (v : Bytes) : PTrie :=
  .branch (some (.val v)) cs (m + valueMem v.length - valueMem s.len)

def qRBV (cs : Kids) (m : Nat) (v : Bytes) : PTrie := .branch (some (.val v)) cs (m + valueMem v.length - 0)

def qNLF (si : Nat) (v : Bytes) : PTrie := newLeaf (ysOf si) v

def qRBI (bv : Option Slot) (cs : Kids) (m si : Nat) (v : Bytes) : PTrie :=
  .branch bv (setKid cs (yOf si) (qNLF si v)) (m + leafMem (ysOf si) v.length - 0)

def qMVL (k : List Nat) (s : Slot) (I : Nat) : PTrie :=
  .leaf (k.drop (I + 1)) s (leafMem (k.drop (I + 1)) s.len)

def qMVE (k : List Nat) (c : PTrie) (m I : Nat) : PTrie :=
  .ext (k.drop (I + 1)) c (extOwnMem (k.drop (I + 1)) + (m - extOwnMem k))

/-- The split branch of `splitLeaf k s key' v` (`key' = [0,15].drop c_D`), before `wrapExt`. -/
def qSPBleaf (k : List Nat) (s : Slot) (key' : List Nat) (v : Bytes) : PTrie :=
  let p := commonPrefix k key'
  match k.drop p.length, key'.drop p.length with
  | [], y :: ys => .branch (some s) (kids1 y (newLeaf ys v)) (50 + valueMem s.len + leafMem ys v.length)
  | x :: xs, [] => .branch (some (.val v)) (kids1 x (.leaf xs s (leafMem xs s.len)))
      (50 + valueMem v.length + leafMem xs s.len)
  | x :: xs, y :: ys => .branch none (kids2 x (.leaf xs s (leafMem xs s.len)) y (newLeaf ys v))
      (50 + leafMem xs s.len + leafMem ys v.length)
  | [], [] => newLeaf key' v

/-- The split branch of `splitExt k c m key' v`, before `wrapExt`. -/
def qSPBext (k : List Nat) (c : PTrie) (m : Nat) (key' : List Nat) (v : Bytes) : PTrie :=
  let p := commonPrefix k key'
  let cm := m - extOwnMem k
  match k.drop p.length with
  | [] => .ext k c m
  | x :: xs =>
    let sub : PTrie := match xs with
      | [] => c
      | _ :: _ => .ext xs c (extOwnMem xs + cm)
    let subMem := match xs with
      | [] => cm
      | _ :: _ => extOwnMem xs + cm
    match key'.drop p.length with
    | [] => .branch (some (.val v)) (kids1 x sub) (50 + valueMem v.length + subMem)
    | y :: ys => .branch none (kids2 x sub y (newLeaf ys v)) (50 + subMem + leafMem ys v.length)

def qWEX (p : List Nat) (b : PTrie) : PTrie := wrapExt p b

/-! ## Upper parts (descend, pass-through) -/

def qRDB (bv : Option Slot) (cs : Kids) (m n : Nat) (c' : PTrie) (cm : Nat) : PTrie :=
  .branch bv (setKid cs n c') (m + c'.memD - cm)

def qRDE (k : List Nat) (m : Nat) (c' : PTrie) (cm : Nat) : PTrie := .ext k c' (m + c'.memD - cm)

def qPT (m : Nat) (c' : PTrie) (cm : Nat) : PTrie := .ext [] c' (m + c'.memD - cm)

/-! ## Serialization -/

/-- `NLF` serializes as the fresh new-leaf bytes. -/
theorem qNLF_enc (si : Nat) (v : Bytes) :
    nodeEnc (qNLF si v) = [0] ++ u32 (hexPrefix (ysOf si) true).length ++ hexPrefix (ysOf si) true ++
      u32 v.length ++ sha256 v ++ u64 (leafMem (ysOf si) v.length) := by
  simp [qNLF, newLeaf, nodeEnc, Slot.valueRef]

end ZkFormal.NearV3.UpsSpec

import ZkFormal.Near.Spec.Good
import ZkFormal.Algebra.Fp
import Std.Data.HashMap

/-!
# ZkFormal.Near.Render.Common — shared data for the honest-trace generators

Executable helpers for the NEAR table generators (lane L6e): the record
analysis of an `Ext` (`Info`: serializations, digests, depths, walk targets,
post values), the key walks over the edges the `node` table provides, and
the emitted SHA messages.

Cells are naturals `< p` (`Fp.ofNat` is applied when a trace is assembled).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1

/-- A table row: cell values as naturals (`< p`). -/
abbrev Row := Array Nat

def toNats (b : Bytes) : List Nat := b.map UInt8.toNat
def ofNats (b : List Nat) : Bytes := b.map UInt8.ofNat
def shaN (b : List Nat) : List Nat := toNats (sha256 (ofNats b))

/-- A message emitted on the `BYTES` bus (`id = kind + 16·idx`); its digest is
consumed exactly once on `DIGEST` (every NEAR message is). -/
structure Msg where
  id : Nat
  bytes : List Nat
  deriving Repr, Inhabited

/-- Smallest `l` with `n ≤ 2^l`. -/
def clog2 (n : Nat) : Nat := go n 0 where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | fuel + 1, acc => if n ≤ 2 ^ acc then acc else go fuel (acc + 1)

/-- `log₂` height of a table of `n` rows (at least `1`, i.e. two rows). -/
def logOf (n : Nat) : Nat := max 1 (clog2 n)

/-- Pad `rows` with copies of `pad` to `2^logOf |rows|` rows. -/
def padTo (rows : Array Row) (pad : Row) : Array Row :=
  rows ++ Array.replicate (2 ^ logOf rows.size - rows.size) pad

def zeroRow (w : Nat) : Row := Array.replicate w 0

/-- The table of `H` rows of width `W` with cells `f row col` (closed-form generators). -/
def mkTab (H W : Nat) (f : Nat → Nat → Nat) : Array Row :=
  (Array.range H).map fun q => (Array.range W).map (f q)

/-- Little-endian bytes of `x` (width `w`). -/
def leBytes (w x : Nat) : List Nat := toNats (leN w x)

def P : Nat := ZkFormal.Algebra.P

/-- `x^(p−2) mod p` (the field inverse, `0 ↦ 0`). -/
def invP (x : Nat) : Nat := (ZkFormal.Algebra.Fp.ofNat x)⁻¹.toNat

/-! ## Record analysis -/

/-- Revealed child ids of a record. -/
def kidIds (nr : NodeRec) : List Nat :=
  nr.kids.filterMap fun k => match k with | .node c => some c | _ => none

/-- Empty-key extension with a revealed child: walks skip it. -/
def eextOf : NodeRec → Bool
  | .ext [] _ _ => true
  | _ => false

def NodeRec.isTouched (nr : NodeRec) : Bool := nr.touched

/-- Everything the generators need about an `Ext` and its claim. -/
structure Info where
  e : Ext
  c : Claim
  ns : Array NodeRec
  /-- pre / post serialization (`ser`) of each node -/
  pre : Array (List Nat)
  post : Array (List Nat)
  /-- depth of each node (root `0`) -/
  depth : Array Nat
  /-- walk target: the node itself, or (empty-key extension with a revealed
  child) its child's target -/
  res : Array Nat
  /-- pre / post value bytes of touched slots (72 bytes; `[]` elsewhere) -/
  vpre : Array (List Nat)
  vpost : Array (List Nat)
  /-- touched slots, ascending -/
  touched : List Nat

namespace Info
variable (I : Info)

def preDig (n : Nat) : List Nat := shaN (I.pre.getD n [])
def postDig (n : Nat) : List Nat := shaN (I.post.getD n [])
def nodeAt (n : Nat) : NodeRec := I.ns.getD n (.branch none [] 0)
def nRcpt : Nat := I.e.rs.length

end Info

/-- Walk target of node `n` (fuel `f`): an empty-key extension with a revealed
child forwards to its child's target. -/
def resF (ns : Array NodeRec) : Nat → Nat → Nat
  | 0, n => n
  | f + 1, n =>
    match ns.getD n (.branch none [] 0) with
    | .ext [] (.node c) _ => resF ns f c
    | _ => n

/-- The bytes a revealed node's hash is taken of: `PTrie.hashOf p = sha256 (nodeSer p)`
for every revealed `p` (`[]` for `.hash`). -/
def nodeSer : PTrie → Bytes
  | .hash _ => []
  | .leaf k v mem =>
    let hp := hexPrefix k true
    [0] ++ u32 hp.length ++ hp ++ v.valueRef ++ u64 mem
  | .ext k c mem =>
    let hp := hexPrefix k false
    [3] ++ u32 hp.length ++ hp ++ c.hashOf ++ u64 mem
  | .branch none cs mem => [1] ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem
  | .branch (some v) cs mem => [2] ++ v.valueRef ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem

/-- Preorder `(node, depth)` pairs of the revealed subtree of node `n` at depth `d` (fuel `f`). -/
def subD (ns : Array NodeRec) : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | f + 1, n, d => (n, d) :: (kidIds (ns.getD n (.branch none [] 0))).flatMap fun c => subD ns f c (d + 1)

/-- Build the `Info` of an `Ext`: the pre/post serializations are those of the
nodes of the record tries (`treeOf`, whose hashes are the state roots), depths
from a preorder traversal. -/
def mkInfo (c : Claim) (e : Ext) : Info :=
  let ns := e.ns.toArray
  let N := ns.size
  let touched := (List.range N).filter fun k => (ns.getD k (.branch none [] 0)).touched
  let vpre : Array (List Nat) := (Array.range N).map fun k =>
    if (ns.getD k (.branch none [] 0)).touched then toNats (e.vals0 k) else []
  let vpost : Array (List Nat) := (Array.range N).map fun k =>
    if (ns.getD k (.branch none [] 0)).touched then toNats (e.valsAt e.rs.length k) else []
  let res : Array Nat := (Array.range N).map (resF ns (N + 1))
  let pre : Array (List Nat) := (Array.range N).map fun n => toNats (nodeSer (treeOf e.ns e.vals0 N n))
  let post : Array (List Nat) := (Array.range N).map fun n =>
    toNats (nodeSer (treeOf e.ns (e.valsAt e.rs.length) N n))
  let depth : Array Nat := (subD ns (N + 1) 0 0).foldl (fun a p => a.set! p.1 p.2) (Array.replicate N 0)
  { e, c, ns, pre, post, depth, res, vpre, vpost, touched }

/-! ## Walks -/

/-- An edge `(N, I) –sym→ (N2, I2)`. -/
abbrev Edge := List Nat

/-- The key symbols of receipt `r`: `nibbles (0 ‖ receiver) ++ [END]`. -/
def keySyms (rc : Receipt) : List Nat := accountKeyPath rc.receiverId ++ [SYM_END]

/-- One walk step from state `(N, i)` on symbol `sym` (the table's edges). -/
def stepOf (I : Info) (N i sym : Nat) : Except String (Nat × Nat) :=
  match I.ns[N]? with
  | none => .error s!"walk: node {N} missing"
  | some nr =>
    match nr with
    | .leaf k v _ =>
      if sym < 16 then
        if k[i]? = some sym then .ok (N, i + 1) else .error s!"walk: leaf {N} key mismatch at {i}"
      else if sym = SYM_END ∧ i = k.length ∧ v = .touched then .ok (N, 0)
      else .error s!"walk: leaf {N} END at {i}"
    | .ext k kid _ =>
      if sym < 16 ∧ k[i]? = some sym then
        if i + 1 = k.length then
          match kid with
          | .node c' => .ok (I.res.getD c' c', 0)
          | _ => .error s!"walk: ext {N} child unrevealed"
        else .ok (N, i + 1)
      else .error s!"walk: ext {N} key mismatch at {i}"
    | .branch v kids _ =>
      if i ≠ 0 then .error s!"walk: branch {N} at {i}"
      else if sym < 16 then
        match kids[sym]? with
        | some (.node c') => .ok (I.res.getD c' c', 0)
        | _ => .error s!"walk: branch {N} slot {sym} not revealed"
      else if sym = SYM_END ∧ v = some .touched then .ok (N, 0)
      else .error s!"walk: branch {N} END"

/-- A walk step: symbol index `t` (`none` for `START`), symbol, edge. -/
structure WStep where
  t : Option Nat
  sym : Nat
  edge : Edge
  last : Bool
  deriving Repr, Inhabited

/-- Steps from state `st` consuming `syms` (symbol index from `t`). -/
def walkFrom (I : Info) : Nat × Nat → List Nat → Nat → Except String (List WStep)
  | _, [], _ => .ok []
  | st, sym :: syms, t => do
    let st' ← stepOf I st.1 st.2 sym
    let rest ← walkFrom I st' syms (t + 1)
    return ⟨some t, sym, [st.1, st.2, sym, st'.1, st'.2], sym = SYM_END⟩ :: rest

/-- The walk of receipt `rc`: `START` then one step per key symbol. -/
def walkOf (I : Info) (rc : Receipt) : Except String (List WStep) := do
  let r0 := I.res.getD 0 0
  let rest ← walkFrom I (r0, 0) (keySyms rc) 0
  return ⟨none, SYM_START, [0, 0, SYM_START, r0, 0], false⟩ :: rest

/-- All walks, receipt order (a walk that fails is empty; see `walkErrors`). -/
def walksOf (I : Info) : List (List WStep) :=
  I.e.rs.map fun rc => match walkOf I rc with | .ok w => w | .error _ => []

/-- The walks that fail (none for honest records). -/
def walkErrors (I : Info) : List String :=
  I.e.rs.filterMap fun rc => match walkOf I rc with | .ok _ => none | .error err => some err

/-- Edge use counts. -/
def edgeUses (ws : List (List WStep)) : Std.HashMap Edge Nat :=
  ws.foldl (fun m w => w.foldl (fun m s => m.insert s.edge (m.getD s.edge 0 + 1)) m) {}

/-- The slot each walk reaches. -/
def finalOf (w : List WStep) : Nat := match w.getLast? with
  | some s => s.edge.getD 3 0
  | none => 0

/-! ## Memory timestamps -/

/-- `tprev` of receipt `r` (slot `k`): `1 +` the previous receipt on `k`, or `0`. -/
def tprevOf (e : Ext) (r : Nat) : Nat :=
  ((List.range r).filter fun r' => e.slot r' = e.slot r).getLast?.map (· + 1) |>.getD 0

/-- `tlast` of slot `k`: `1 +` the last receipt on `k`, or `0`. -/
def tlastOf (e : Ext) (k : Nat) : Nat :=
  ((List.range e.rs.length).filter fun r' => e.slot r' = k).getLast?.map (· + 1) |>.getD 0

end ZkFormal.Near.Render

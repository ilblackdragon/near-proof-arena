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

/-- Little-endian bytes of `x` (width `w`). -/
def leBytes (w x : Nat) : List Nat := toNats (leN w x)

def P : Nat := ZkFormal.Algebra.P

/-- `x^(p−2) mod p` (the field inverse, `0 ↦ 0`). -/
def invP (x : Nat) : Nat := (ZkFormal.Algebra.Fp.ofNat x)⁻¹.toNat

/-! ## Record analysis -/

/-- Revealed child ids of a record. -/
def kidIds (nr : NodeRec) : List Nat :=
  nr.kids.filterMap fun k => match k with | .node c => some c | _ => none

/-- Post-order of the revealed tree from node `n` (fuel `f`). -/
def postOrder (ns : Array NodeRec) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n =>
    ((ns[n]?.map kidIds).getD []).flatMap (postOrder ns f) ++ [n]

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

/-- Build the `Info` of an `Ext` (pre/post serializations bottom-up). -/
def mkInfo (c : Claim) (e : Ext) : Info := Id.run do
  let ns := e.ns.toArray
  let N := ns.size
  let order := postOrder ns (N + 1) 0
  let touched := (List.range N).filter fun k => (ns.getD k (.branch none [] 0)).touched
  let mut vpre : Array (List Nat) := Array.replicate N []
  let mut vpost : Array (List Nat) := Array.replicate N []
  for k in touched do
    vpre := vpre.set! k (toNats (e.vals0 k))
    vpost := vpost.set! k (toNats (e.valsAt e.rs.length k))
  let mut pre : Array (List Nat) := Array.replicate N []
  let mut post : Array (List Nat) := Array.replicate N []
  let mut res : Array Nat := (List.range N).toArray
  let mut dpre : Array Bytes := Array.replicate N []
  let mut dpost : Array Bytes := Array.replicate N []
  for n in order do
    let nr := ns.getD n (.branch none [] 0)
    let vhPre := sha256 (ofNats (vpre.getD n []))
    let vhPost := sha256 (ofNats (vpost.getD n []))
    let sPre := ser vhPre (fun c => dpre.getD c []) nr
    let sPost := ser vhPost (fun c => dpost.getD c []) nr
    pre := pre.set! n (toNats sPre)
    post := post.set! n (toNats sPost)
    dpre := dpre.set! n (sha256 sPre)
    dpost := dpost.set! n (sha256 sPost)
    if eextOf nr then
      match kidIds nr with
      | [c'] => res := res.set! n (res.getD c' c')
      | _ => pure ()
  let mut depth : Array Nat := Array.replicate N 0
  for n in order.reverse do
    for c' in kidIds (ns.getD n (.branch none [] 0)) do
      depth := depth.set! c' (depth.getD n 0 + 1)
  return { e, c, ns, pre, post, depth, res, vpre, vpost, touched }

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

/-- The walk of receipt `rc`: `START` then one step per key symbol. -/
def walkOf (I : Info) (rc : Receipt) : Except String (List WStep) := do
  let r0 := I.res.getD 0 0
  let mut steps : Array WStep := #[⟨none, SYM_START, [0, 0, SYM_START, r0, 0], false⟩]
  let mut st := (r0, 0)
  let syms := keySyms rc
  for (sym, t) in syms.zip (List.range syms.length) do
    let st' ← stepOf I st.1 st.2 sym
    steps := steps.push ⟨some t, sym, [st.1, st.2, sym, st'.1, st'.2], sym = SYM_END⟩
    st := st'
  return steps.toList

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

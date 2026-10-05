import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Node

/-!
# ZkFormal.Near.Render.Node — honest rows of the `node` table

One row per byte of each node's serialization (node-id order, root first),
then the `SUM` row, then padding (`sz` carried).  See
`ZkFormal.Near.Tables.Node` for the row semantics this follows.
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

namespace NodeGen

/-- A hash window: lookup flag, child data (`CH`), pre/post bytes. -/
structure Win where
  look : Bool
  cid : Nat := 0
  clen : Nat := 0
  cres : Nat := 0
  w : Nat := 0
  lastw : Bool := false
  slot : Option Nat := none
  pre : List Nat
  post : List Nat
  deriving Inhabited

inductive F where
  | tag | hpl | hpf | key | vlen | vh (w : Win) | bm | ch (w : Win) | mem
  deriving Inhabited

def F.state : F → Nat
  | .tag => Node.sTAG | .hpl => Node.sHPL | .hpf => Node.sHPF | .key => Node.sKEY
  | .vlen => Node.sVLEN | .vh _ => Node.sVH | .bm => Node.sBM | .ch _ => Node.sCH
  | .mem => Node.sMEM

def F.len (hplen : Nat) : F → Nat
  | .tag => 1 | .hpl => 4 | .hpf => 1 | .key => hplen - 1 | .vlen => 4 | .vh _ => 32
  | .bm => 2 | .ch _ => 32 | .mem => 8

/-- Child window of slot `kid`. -/
def kidWin (I : Info) (kid : Kid) (w : Nat) (lastw : Bool) (slot : Option Nat) : Win :=
  match kid with
  | .node c' =>
    { look := true, cid := c', clen := (I.pre.getD c' []).length, cres := I.res.getD c' c',
      w, lastw, slot, pre := I.preDig c', post := I.postDig c' }
  | .hash h => { look := false, w, lastw, slot, pre := toNats h, post := toNats h }
  | .none => { look := false, w, lastw, slot, pre := [], post := [] }

def valWin (I : Info) (n : Nat) : VSlot → Win
  | .touched => { look := true, pre := shaN (I.vpre.getD n []), post := shaN (I.vpost.getD n []) }
  | .ref _ h => { look := false, pre := toNats h, post := toNats h }

def branchWins (I : Info) (kids : List Kid) : List F :=
  let present := (kids.zip (List.range kids.length)).filter fun (k, _) => k ≠ .none
  (present.zip (List.range present.length)).map fun ((k, j), w) =>
    .ch (kidWin I k w (w + 1 = present.length) (some j))

/-- The fields of a node, in serialization order. -/
def fieldsOf (I : Info) (n : Nat) : NodeRec → List F
  | .leaf _ v _ => [.tag, .hpl, .hpf, .key, .vlen, .vh (valWin I n v), .mem]
  | .ext _ kid _ => [.tag, .hpl, .hpf, .key, .ch (kidWin I kid 0 true none), .mem]
  | .branch none kids _ => [.tag, .bm] ++ branchWins I kids ++ [.mem]
  | .branch (some v) kids _ => [.tag, .vlen, .vh (valWin I n v), .bm] ++ branchWins I kids ++ [.mem]

def bitOf (x b : Nat) : Nat := (x / 2 ^ b) % 2
def b2n (b : Bool) : Nat := if b then 1 else 0

/-! ## Node-level data -/

/-- Leaf or extension (a node with a key). -/
def isLE : NodeRec → Bool
  | .leaf .. => true
  | .ext .. => true
  | .branch .. => false

def isExtR : NodeRec → Bool
  | .ext .. => true
  | _ => false

def hplenOf (nr : NodeRec) : Nat := if isLE nr then 1 + nr.key.length / 2 else 0
def oddOf (nr : NodeRec) : Nat := if isLE nr then nr.key.length % 2 else 0
def nokeyOf (nr : NodeRec) : Nat := b2n (isLE nr && hplenOf nr == 1)
def bmvOf (nr : NodeRec) : Nat := if isLE nr then 0 else bitmapOf nr.kids 0
def popOf (nr : NodeRec) : Nat := (List.range 16).foldl (fun a i => a + bitOf (bmvOf nr) i) 0
def nochildOf (nr : NodeRec) : Nat := b2n (!isLE nr && popOf nr == 0)

/-- Extension: child revealed, its walk target. -/
def xrvOf : NodeRec → Bool
  | .ext _ (.node _) _ => true
  | _ => false

def xresOf (I : Info) : NodeRec → Nat
  | .ext _ (.node c') _ => I.res.getD c' c'
  | _ => 0

def xdeadOf (nr : NodeRec) : Bool := isExtR nr && !xrvOf nr
def xlast0Of (nr : NodeRec) : Bool := isExtR nr && nokeyOf nr == 1
def eextOf' (nr : NodeRec) : Bool := isExtR nr && nokeyOf nr == 1 && oddOf nr == 0

/-- Type flags `(tl, te, tb1, tb2)`. -/
def typeOf : NodeRec → Nat × Nat × Nat × Nat
  | .leaf .. => (1, 0, 0, 0)
  | .ext .. => (0, 1, 0, 0)
  | .branch none .. => (0, 0, 1, 0)
  | .branch (some _) .. => (0, 0, 0, 1)

/-- Field layout: `(field, index in the field)` per byte. -/
def layout (fs : List F) (hplen : Nat) : List (F × Nat) :=
  fs.flatMap fun f => (List.range (f.len hplen)).map (f, ·)

/-- Revealed size added by node `n` (its bytes, plus 72 if touched). -/
def nodeSz (I : Info) (n : Nat) : Nat :=
  (I.pre.getD n []).length + (if (I.nodeAt n).touched then 72 else 0)

/-- Revealed size before node `n`. -/
def szBefore (I : Info) (n : Nat) : Nat := ((List.range n).map (nodeSz I)).sum

/-- A node row: node, byte position, field and index in the field, pre/post byte. -/
structure NRec where
  n : Nat
  pos : Nat
  f : F
  idx : Nat
  b : Nat
  pb : Nat
  deriving Inhabited

/-- The rows of node `n`. -/
def nodeRecs (I : Info) (n : Nat) : List NRec :=
  let nr := I.nodeAt n
  let lay := (layout (fieldsOf I n nr) (hplenOf nr)).toArray
  let pre := (I.pre.getD n []).toArray
  let post := (I.post.getD n []).toArray
  (List.range lay.size).map fun pos =>
    let fi := lay.getD pos default
    ⟨n, pos, fi.1, fi.2, pre.getD pos 0, post.getD pos 0⟩

/-- All node rows, node-id order. -/
def recsOf (I : Info) : List NRec := (List.range I.ns.size).flatMap (nodeRecs I)

/-- Edge provider A of a row (edge, gate); `none`: no edge contents. -/
def edgeAOf (I : Info) (r : NRec) : Option (Edge × Bool) :=
  let n := r.n
  let nr := I.nodeAt n
  let odd := oddOf nr
  let ki := 2 * r.idx + odd
  if r.pos = 0 ∧ n = 0 then some ([0, 0, SYM_START, I.res.getD n n, 0], true) else
  match r.f with
  | .ch wn => if r.idx = 0 ∧ wn.look = true ∧ isLE nr = false then
      some ([n, 0, wn.slot.getD 0, wn.cres, 0], true) else none
  | .vh wn => if r.idx = 0 ∧ wn.look = true then
      some ([n, (typeOf nr).1 * nr.key.length, SYM_END, n, 0], true) else none
  | .hpf => if odd = 1 then
      some (if xlast0Of nr then [n, 0, r.b % 16, xresOf I nr, 0] else [n, 0, r.b % 16, n, 1],
        !(nokeyOf nr == 1 && xdeadOf nr)) else none
  | .key => some ([n, ki, r.b / 16, n, ki + 1], true)
  | _ => none

/-- Edge provider B of a row (key bytes: the low nibble). -/
def edgeBOf (I : Info) (r : NRec) : Option (Edge × Bool) :=
  let n := r.n
  let nr := I.nodeAt n
  let ki := 2 * r.idx + oddOf nr
  match r.f with
  | .key => if r.idx + 1 = F.key.len (hplenOf nr) ∧ isExtR nr = true then
      some ([n, ki + 1, r.b % 16, xresOf I nr, 0], !xdeadOf nr) else
      some ([n, ki + 1, r.b % 16, n, ki + 2], true)
  | _ => none

/-- The hash window of a row. -/
def F.win : F → Option Win
  | .vh w => some w
  | .ch w => some w
  | _ => none

def F.chw : F → Option Win
  | .ch w => some w
  | _ => none

/-- Digest lookup of a row: `(dI, dL, child?)`. -/
def digOf (r : NRec) : Option (Nat × Nat × Bool) :=
  match r.f with
  | .ch w => if r.idx = 0 ∧ w.look = true then some (msgId K_NPRE w.cid, w.clen, true) else none
  | .vh w => if r.idx = 0 ∧ w.look = true then some (msgId K_VPRE r.n, 72, false) else none
  | _ => none

def F.nib : F → Bool
  | .hpf => true
  | .key => true
  | _ => false

def edgeCell (A : Option (Edge × Bool)) (u : Std.HashMap Edge Nat) (j : Nat) : Nat :=
  match A with
  | some (e, _) => e.getD j 0
  | none => 0

def gateCell (A : Option (Edge × Bool)) : Nat :=
  match A with
  | some (_, true) => 1
  | _ => 0

def multCell (A : Option (Edge × Bool)) (u : Std.HashMap Edge Nat) : Nat :=
  match A with
  | some (e, true) => u.getD e 0
  | _ => 0

/-- Cells of a node row. -/
def rowCell (I : Info) (u : Std.HashMap Edge Nat) (r : NRec) (col : Nat) : Nat :=
  let n := r.n
  let nr := I.nodeAt n
  let len := (I.pre.getD n []).length
  let hplen := hplenOf nr
  if col < 29 then
    match col with
    | 0 => 1  -- act
    | 1 => b2n (r.pos = 0)  -- nf
    | 2 => b2n (r.pos + 1 = len)  -- nl
    | 3 => 0  -- sumr
    | 4 => n  -- nid
    | 5 => r.pos
    | 6 => len
    | 7 => I.depth.getD n 0
    | 8 => r.b
    | 9 => r.pb
    | 10 => (typeOf nr).1
    | 11 => (typeOf nr).2.1
    | 12 => (typeOf nr).2.2.1
    | 13 => (typeOf nr).2.2.2
    | 23 => r.idx
    | 24 => b2n (r.idx = 0)  -- fs
    | 25 => b2n (r.idx + 1 = r.f.len hplen)  -- fe
    | 26 => hplen
    | 27 => oddOf nr
    | 28 => nokeyOf nr
    | c => b2n (r.f.state = c)  -- states 14 … 22
  else if col < 33 then (if r.f.nib then bitOf (r.b / 16) (col - 29) else 0)  -- hbit
  else if col < 37 then (if r.f.nib then bitOf (r.b % 16) (col - 33) else 0)  -- lbit
  else if col < 53 then bitOf (bmvOf nr) (col - 37)  -- bm
  else if col = 53 then nochildOf nr
  else if col < 70 then  -- jj
    (match r.f.chw with | some w => b2n (w.slot = some (col - 54)) | none => 0)
  else if col = 70 then (match r.f.chw with | some w => w.w | none => 0)
  else if col = 71 then (match r.f.chw with | some w => b2n w.lastw | none => 0)
  else if col < 104 then (match r.f.win with | some w => w.pre.getD (r.idx + (col - 72)) 0 | none => 0)
  else if col < 136 then (match r.f.win with | some w => w.post.getD (r.idx + (col - 104)) 0 | none => 0)
  else
    match col with
    | 136 => (match r.f.chw with | some w => b2n w.look | none => 0)  -- rv
    | 137 => (match r.f.chw with | some w => w.cid | none => 0)
    | 138 => (match r.f.chw with | some w => w.clen | none => 0)
    | 139 => b2n nr.touched  -- tv
    | 140 => (match digOf r with | some d => d.1 | none => 0)  -- dI
    | 141 => (match digOf r with | some d => d.2.1 | none => 0)  -- dL
    | 142 => (match digOf r with | some _ => 1 | none => 0)  -- gD
    | 143 => (match digOf r with | some (_, _, true) => 1 | _ => 0)  -- gP
    | 144 => b2n (r.pos = 0 ∧ nr.touched = true)  -- gV
    | 145 => gateCell (edgeAOf I r)
    | 146 => edgeCell (edgeAOf I r) u 1
    | 147 => edgeCell (edgeAOf I r) u 2
    | 148 => edgeCell (edgeAOf I r) u 3
    | 149 => edgeCell (edgeAOf I r) u 4
    | 150 => multCell (edgeAOf I r) u
    | 151 => multCell (edgeBOf I r) u
    | 152 => szBefore I n + r.pos  -- sz
    | 153 => I.res.getD n n
    | 154 => (match r.f.chw with | some w => w.cres | none => 0)
    | 155 => xresOf I nr
    | 156 => b2n (xrvOf nr)
    | 157 => b2n (xdeadOf nr)
    | 158 => b2n (xlast0Of nr)
    | 159 => b2n (eextOf' nr)
    | 160 => gateCell (edgeBOf I r)
    | 161 => edgeCell (edgeBOf I r) u 3
    | 162 => edgeCell (edgeBOf I r) u 4
    | _ => 0

/-- Cells of the `SUM` row (`total` revealed bytes). -/
def sumCell (total col : Nat) : Nat :=
  if col = Node.sumr then 1 else if col = Node.sz then total
  else if 72 ≤ col ∧ col < 94 then bitOf (3000000 - total) (col - 72) else 0

/-- Cells of a padding row. -/
def padCell (total col : Nat) : Nat := if col = Node.sz then total else 0

/-- The cells of the node table. -/
def cell (I : Info) (u : Std.HashMap Edge Nat) (recs : Array NRec) (total q col : Nat) : Nat :=
  if q < recs.size then rowCell I u (recs.getD q default) col
  else if q = recs.size then sumCell total col
  else padCell total col

end NodeGen

open NodeGen in
/-- Honest rows of the `node` table: one row per serialized byte (node-id
order), the `SUM` row, padding. -/
def nodeRowsAll (I : Info) (uses : Std.HashMap Edge Nat) : Array Row :=
  let recs := (recsOf I).toArray
  let total := szBefore I I.ns.size
  mkTab (2 ^ logOf (recs.size + 1)) Node.width (cell I uses recs total)

/-- Messages the `node` table emits: `NPRE(N)`, `NPOST(N)`. -/
def nodeMsgs (I : Info) : List Msg :=
  (List.range I.ns.size).flatMap fun n =>
    [⟨msgId K_NPRE n, I.pre.getD n []⟩, ⟨msgId K_NPOST n, I.post.getD n []⟩]

end ZkFormal.Near.Render

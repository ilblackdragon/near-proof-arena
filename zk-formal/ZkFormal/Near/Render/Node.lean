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

/-- Rows of node `n`; `sz0` = revealed count before the node; `uses` edge counts.
Returns the rows and the edge-provider tuples (for diagnostics). -/
def nodeRows (I : Info) (uses : Std.HashMap Edge Nat) (n sz0 : Nat) : Array Row := Id.run do
  let nr := I.nodeAt n
  let pre := I.pre.getD n []
  let post := I.post.getD n []
  let len := pre.length
  let key := nr.key
  let s := key.length
  let isLeaf := nr matches .leaf ..
  let isExt := nr matches .ext ..
  let hplen := if isLeaf || isExt then 1 + s / 2 else 0
  let odd := if isLeaf || isExt then s % 2 else 0
  let nokey := b2n ((isLeaf || isExt) && hplen == 1)
  let kids := nr.kids
  let bmv := if isLeaf || isExt then 0 else bitmapOf kids 0
  let pop := (List.range 16).foldl (fun a i => a + bitOf bmv i) 0
  let isBr := !(isLeaf || isExt)
  let nochild := b2n (isBr && pop == 0)
  let tv := nr.touched
  let (xrv, xres) := match nr with
    | .ext _ (.node c') _ => (true, I.res.getD c' c')
    | _ => (false, 0)
  let xdead := isExt && !xrv
  let xlast0 := isExt && nokey == 1
  let eext := isExt && nokey == 1 && odd == 0
  let res := I.res.getD n n
  let (tl, te, tb1, tb2) := match nr with
    | .leaf .. => (1, 0, 0, 0) | .ext .. => (0, 1, 0, 0)
    | .branch none .. => (0, 0, 1, 0) | .branch (some _) .. => (0, 0, 0, 1)
  let base : Row := Id.run do
    let mut r := zeroRow Node.width
    r := r.set! Node.act 1
    r := r.set! Node.nid n
    r := r.set! Node.len len
    r := r.set! Node.depth (I.depth.getD n 0)
    r := r.set! Node.tl tl
    r := r.set! Node.te te
    r := r.set! Node.tb1 tb1
    r := r.set! Node.tb2 tb2
    r := r.set! Node.hplen hplen
    r := r.set! Node.odd odd
    r := r.set! Node.nokey nokey
    r := r.set! Node.nochild nochild
    r := r.set! Node.tv (b2n tv)
    r := r.set! Node.res res
    r := r.set! Node.xres xres
    r := r.set! Node.xrv (b2n xrv)
    r := r.set! Node.xdead (b2n xdead)
    r := r.set! Node.xlast0 (b2n xlast0)
    r := r.set! Node.eext (b2n eext)
    for i in List.range 16 do
      r := r.set! (Node.bm i) (bitOf bmv i)
    return r
  -- edge contents are constrained on their rows even when the gate is off
  let setA (r : Row) (e : Edge) (gate : Bool := true) : Row := Id.run do
    let mut r := r
    if gate then
      r := r.set! Node.gA 1
      r := r.set! Node.mA (uses.getD e 0)
    r := r.set! Node.aI (e.getD 1 0)
    r := r.set! Node.aS (e.getD 2 0)
    r := r.set! Node.aN (e.getD 3 0)
    r := r.set! Node.aJ (e.getD 4 0)
    return r
  let setB (r : Row) (e : Edge) (gate : Bool := true) : Row := Id.run do
    let mut r := r
    if gate then
      r := r.set! Node.gB 1
      r := r.set! Node.mB (uses.getD e 0)
    r := r.set! Node.bN (e.getD 3 0)
    r := r.set! Node.bJ (e.getD 4 0)
    return r
  let mut rows : Array Row := #[]
  let mut pos := 0
  let mut sz := sz0
  for f in fieldsOf I n nr do
    let flen := f.len hplen
    for idx in List.range flen do
      let mut r := base
      let b := pre.getD pos 0
      r := r.set! Node.nf (b2n (pos = 0))
      r := r.set! Node.nl (b2n (pos + 1 = len))
      r := r.set! Node.pos pos
      r := r.set! Node.b b
      r := r.set! Node.pb (post.getD pos 0)
      r := r.set! f.state 1
      r := r.set! Node.idx idx
      r := r.set! Node.fs (b2n (idx = 0))
      r := r.set! Node.fe (b2n (idx + 1 = flen))
      r := r.set! Node.sz sz
      match f with
      | .hpf | .key =>
        for i in List.range 4 do
          r := r.set! (Node.hbit i) (bitOf (b / 16) i)
          r := r.set! (Node.lbit i) (bitOf (b % 16) i)
      | _ => pure ()
      -- windows
      match f with
      | .vh wn | .ch wn =>
        for i in List.range 32 do
          r := r.set! (Node.reg i) (wn.pre.getD (idx + i) 0)
          r := r.set! (Node.preg i) (wn.post.getD (idx + i) 0)
      | _ => pure ()
      match f with
      | .ch wn =>
        r := r.set! Node.rv (b2n wn.look)
        r := r.set! Node.cid wn.cid
        r := r.set! Node.clen wn.clen
        r := r.set! Node.cres wn.cres
        r := r.set! Node.w wn.w
        r := r.set! Node.lastw (b2n wn.lastw)
        match wn.slot with
        | some j => r := r.set! (Node.jj j) 1
        | none => pure ()
        if idx = 0 ∧ wn.look then
          r := r.set! Node.gP 1
          r := r.set! Node.gD 1
          r := r.set! Node.dI (msgId K_NPRE wn.cid)
          r := r.set! Node.dL wn.clen
          if isBr then
            r := setA r [n, 0, wn.slot.getD 0, wn.cres, 0]
      | .vh wn =>
        if idx = 0 ∧ wn.look then
          r := r.set! Node.gD 1
          r := r.set! Node.dI (msgId K_VPRE n)
          r := r.set! Node.dL 72
          r := setA r [n, tl * s, SYM_END, n, 0]
      | .hpf =>
        if odd == 1 then
          r := setA r (if xlast0 then [n, 0, b % 16, xres, 0] else [n, 0, b % 16, n, 1])
            (!(nokey == 1 && xdead))
      | .key =>
        let ki := 2 * idx + odd
        r := setA r [n, ki, b / 16, n, ki + 1]
        if idx + 1 == flen && isExt then
          r := setB r [n, ki + 1, b % 16, xres, 0] (!xdead)
        else r := setB r [n, ki + 1, b % 16, n, ki + 2]
      | _ => pure ()
      if pos = 0 ∧ tv then r := r.set! Node.gV 1
      if pos = 0 ∧ n = 0 then r := setA r [0, 0, SYM_START, res, 0]
      rows := rows.push r
      pos := pos + 1
      sz := sz + 1
  return rows

/-- Revealed size added by node `n` (its bytes, plus 72 if touched). -/
def nodeSz (I : Info) (n : Nat) : Nat :=
  (I.pre.getD n []).length + (if (I.nodeAt n).touched then 72 else 0)

end NodeGen

open NodeGen in
/-- Honest rows of the `node` table (padded). -/
def nodeRowsAll (I : Info) (uses : Std.HashMap Edge Nat) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  let mut sz := 0
  for n in List.range I.ns.size do
    rows := rows ++ nodeRows I uses n sz
    sz := sz + nodeSz I n
  let mut sum := zeroRow Node.width
  sum := sum.set! Node.sumr 1
  sum := sum.set! Node.sz sz
  for i in List.range 22 do
    sum := sum.set! (Node.reg i) (bitOf (3000000 - sz) i)
  rows := rows.push sum
  return padTo rows ((zeroRow Node.width).set! Node.sz sz)

/-- Messages the `node` table emits: `NPRE(N)`, `NPOST(N)`. -/
def nodeMsgs (I : Info) : List Msg :=
  (List.range I.ns.size).flatMap fun n =>
    [⟨msgId K_NPRE n, I.pre.getD n []⟩, ⟨msgId K_NPOST n, I.post.getD n []⟩]

end ZkFormal.Near.Render

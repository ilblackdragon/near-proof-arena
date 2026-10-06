import ZkFormal.Near.Extract.NodeView
import ZkFormal.NearV3.Tables.Node
import ZkFormal.NearV3.IdsUps
import ZkFormal.Near.Extract.Segments

/-!
# ZkFormal.NearV3.Extract.NodeView — what `nodeV3` holds (view statement)

Lane `v3-trie`.  v1's `NodeView` (`Near/Extract/NodeView.lean`) with the v3 deltas of
`Tables/Node.lean`: one `NodeS3` per record (node-id order), each with its instance `τ`,
depth, walk target, edge use counts, `BMAP` use count and weak-uniqueness flags; a revealed
value slot is a window onto value record `vid` of length `vlen`, written in lockstep or not.

`nodeTraffic3` is the exact message list of every interaction; `NodeWf3` the local facts.
`NodeV3ViewStmt` is the extraction obligation (mirrors L6's `NodeViewStmt`).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec

/-- A value slot of a v3 record. -/
inductive NSlot3 where
  /-- unrevealed: `u32` length bytes and hash window -/
  | ref (lenB h : List Nat)
  /-- revealed: length bytes, value record `vid` of length `vlen`, pre/post digest windows,
  written in lockstep (`set`) or not (`post = pre`) -/
  | val (lenB : List Nat) (vid vlen : Nat) (pre post : List Nat) (written : Bool)
  deriving Repr, DecidableEq, Inhabited

inductive NodeV3 where
  | leaf (key : List Nat) (v : NSlot3) (memB : List Nat)
  | ext (key : List Nat) (kid : NKid) (memB : List Nat)
  | branch (v : Option NSlot3) (kids : List NKid) (memB : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One record. -/
structure NodeS3 where
  v : NodeV3
  tau : Nat
  depth : Nat
  res : Nat
  /-- use counts of the edges it provides (`edgesOf3` order) -/
  uses : List Nat
  /-- `BMAP` use count (branches) -/
  ubm : Nat
  dup : Bool
  hd : Bool
  repE : Nat
  /-- per byte: the row's window child id `cid` (`UPB`; the child on a revealed window's
  rows, free elsewhere) -/
  ucid : List Nat
  /-- per byte: `UPB` use count of the post byte (`upsV3` reads) -/
  mU : List Nat
  deriving Repr, Inhabited

/-! ## Serialization (raw) -/

def NSlot3.bytes (post : Bool) : NSlot3 → List Nat
  | .ref lenB h => lenB ++ h
  | .val lenB _ _ pre po _ => lenB ++ (if post then po else pre)

def NodeV3.ser (post : Bool) : NodeV3 → List Nat
  | .leaf k v memB => [0] ++ u32r (hpN k true).length ++ hpN k true ++ v.bytes post ++ memB
  | .ext k kid memB => [3] ++ u32r (hpN k false).length ++ hpN k false ++ kid.bytes post ++ memB
  | .branch v kids memB =>
    (match v with | none => [1] | some s => [2] ++ s.bytes post) ++
      [kidBitmap kids % 256, kidBitmap kids / 256] ++ (kids.flatMap (NKid.bytes post)) ++ memB

/-- The revealed value slot `(vid, vlen, pre, post, written)`, if any. -/
def NodeV3.value : NodeV3 → Option (Nat × Nat × List Nat × List Nat × Bool)
  | .leaf _ (.val _ i l pre po w) _ => some (i, l, pre, po, w)
  | .branch (some (.val _ i l pre po w)) _ _ => some (i, l, pre, po, w)
  | _ => none

/-- Revealed children `(cid, clen, cres, pre, post)` in slot order. -/
def NodeV3.revealed : NodeV3 → List (Nat × Nat × Nat × List Nat × List Nat)
  | .ext _ (.node c l r pre po) _ => [(c, l, r, pre, po)]
  | .branch _ kids _ => kids.filterMap fun
      | .node c l r pre po => some (c, l, r, pre, po)
      | _ => none
  | _ => []

/-! ## Walk edges `[N, I, sym, N', I', kind]` -/

def keyEdges3 (n : Nat) (k : List Nat) : List Msg :=
  (List.range k.length).map fun i => [n, i, k.getD i 0, n, i + 1, EK_KEY]

/-- Edges record `n` provides (in a fixed order; `uses` is aligned with it). -/
def edgesOf3 (n : Nat) (s : NodeS3) : List Msg :=
  match s.v with
  | .leaf k v _ =>
    keyEdges3 n k ++
      (match v with | .val _ i _ _ _ _ => [[n, k.length, SYM_END, i, 0, EK_VAL]] | _ => []) ++
      [[n, k.length, SYM_END, n, k.length, EK_LEND]]
  | .ext k kid _ =>
    keyEdges3 n k.dropLast ++
      (match kid, k.getLast? with
       | .node _ _ cr _ _, some x => [[n, k.length - 1, x, cr, 0, EK_KEY]]
       | _, some x => [[n, k.length - 1, x, n, k.length, EK_KEY]]
       | _, none => [])
  | .branch v kids _ =>
    ((kids.zip (List.range kids.length)).filterMap fun
      | (.node _ _ cr _ _, j) => some [n, 0, j, cr, 0, EK_DOWN]
      | _ => none) ++
    (match v with | some (.val _ i _ _ _ _) => [[n, 0, SYM_END, i, 0, EK_VAL]] | _ => [])

/-- Branch facts `(bm, hasValue)` for `BMAP`. -/
def NodeV3.bmap : NodeV3 → Option (Nat × Nat)
  | .branch v kids _ => some (kidBitmap kids, if v.isSome then 1 else 0)
  | _ => none

/-! ## Traffic -/

def eidN (n : Nat) : Nat := msgId K_NPRE n

/-- `UPB (NPOST(n), pos, pb, len, depth, cid, u p)` for every byte `p` of record `n`. -/
def upbOf (n : Nat) (s : NodeS3) (u : Nat → Nat) : List Msg :=
  (List.range (s.v.ser false).length).map fun p =>
    [msgId K_NPOST n, p, (s.v.ser true).getD p 0, (s.v.ser false).length, s.depth, s.ucid.getD p 0, u p]

def nodeSends3 (vs : List NodeS3) (b : Nat) : List Msg :=
  let ns := vs.zip (List.range vs.length)
  if b = B_BYTES then
    ns.flatMap fun (s, n) => emitAt (msgId K_NPRE n) 0 (s.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (s.v.ser true)
  else if b = B_PARENT then
    ns.flatMap fun (s, _) => s.v.revealed.map fun (c, l, r, _, _) => [c, s.tau, s.depth + 1, l, r]
  else if b = B_VPARENT then
    ns.flatMap fun (s, _) => match s.v.value with | some (i, l, _, _, _) => [[i, l]] | none => []
  else if b = B_EDGE then
    ns.flatMap fun (s, n) => (edgesOf3 n s).map (· ++ [0])
  else if b = B_BMAP then
    ns.flatMap fun (s, n) => match s.v.bmap with | some (bm, hv) => [[n, bm, hv, 0]] | none => []
  else if b = B_DIGS then
    ns.flatMap fun (s, _) =>
      (s.v.revealed.flatMap fun (c, _, _, pre, _) =>
        (List.range 32).map fun i => [msgId K_NPRE c, s.tau, i, pre.getD i 0]) ++
      (match s.v.value with
       | some (i, _, pre, _, _) => (List.range 32).map fun j => [msgId K_VPRE i, s.tau, j, pre.getD j 0]
       | none => [])
  else if b = B_ENT then
    ns.flatMap fun (s, n) => if s.hd then
      (List.range (s.v.ser false).length).map fun p => [eidN n, (s.v.ser false).length, p, (s.v.ser false).getD p 0]
      else []
  else if b = B_SIZE then
    [[0, ((vs.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum]]
  else if b = B_UPB then
    ns.flatMap fun (s, n) => upbOf n s fun _ => 0
  else []

def nodeRecvs3 (vs : List NodeS3) (b : Nat) : List Msg :=
  let ns := vs.zip (List.range vs.length)
  if b = B_DIGEST then
    ns.flatMap fun (s, _) =>
      (s.v.revealed.flatMap fun (c, l, _, pre, po) =>
        [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]) ++
      (match s.v.value with
       | some (i, l, pre, po, w) =>
         [digMsg (msgId K_VPRE i) l pre] ++ (if w then [digMsg (msgId K_VPOST i) l po] else [])
       | none => [])
  else if b = B_PARENT then
    ns.map fun (s, n) => [n, s.tau, s.depth, (s.v.ser false).length, s.res]
  else if b = B_EDGE then
    ns.flatMap fun (s, n) => ((edgesOf3 n s).zip s.uses).map fun (e, u) => e ++ [u]
  else if b = B_BMAP then
    ns.flatMap fun (s, n) => match s.v.bmap with | some (bm, hv) => [[n, bm, hv, s.ubm]] | none => []
  else if b = B_DUP then
    ns.filterMap fun (s, n) => if s.dup then some [eidN n, s.repE] else none
  else if b = B_ENT then
    ns.flatMap fun (s, _) => if s.dup then
      (List.range (s.v.ser false).length).map fun p => [s.repE, (s.v.ser false).length, p, (s.v.ser false).getD p 0]
      else []
  else if b = B_UPB then
    ns.flatMap fun (s, n) => upbOf n s fun p => s.mU.getD p 0
  else []

def nodeTraffic3 (vs : List NodeS3) : Traffic := ⟨nodeSends3 vs, nodeRecvs3 vs⟩

/-! ## Local facts -/

def NSlot3.wf : NSlot3 → Prop
  | .ref lenB h => lenB.length = 4 ∧ h.length = 32
  | .val lenB _ vlen pre po w => lenB.length = 4 ∧ pre.length = 32 ∧ po.length = 32 ∧
      (w = false → po = pre) ∧
      -- the length bytes encode `vlen` (stated for byte values), top byte 0
      lenB.getD 3 0 = 0 ∧ ((∀ x ∈ lenB, x < 256) → le256 lenB = vlen)

def NodeV3.wf : NodeV3 → Prop
  | .leaf k v memB => (∀ x ∈ k, x < 16) ∧ v.wf ∧ memB.length = 8
  | .ext k kid memB => (∀ x ∈ k, x < 16) ∧ kid ≠ .none ∧ kid.wf ∧ memB.length = 8
  | .branch v kids memB => kids.length = 16 ∧ (∀ s, v = some s → s.wf) ∧ (∀ kd ∈ kids, kd.wf) ∧
      memB.length = 8

/-- Walk target (v1). -/
def NodeS3.resOk (n : Nat) (s : NodeS3) : Prop :=
  match s.v with
  | .ext [] (.node _ _ cr _ _) _ => s.res = cr
  | _ => s.res = n

def NSlot3.raw : NSlot3 → List Nat
  | .ref lenB h => lenB ++ h
  | .val lenB i l pre po _ => lenB ++ [i, l] ++ pre ++ po

def NodeV3.raw : NodeV3 → List Nat
  | .leaf k v memB => k ++ v.raw ++ memB
  | .ext k kid memB => k ++ kid.raw ++ memB
  | .branch v kids memB => (v.map NSlot3.raw).getD [] ++ kids.flatMap NKid.raw ++ memB

/-- The window child ids: the first byte of every revealed child's window carries the child
`c` (offset `5 + |hp|` in an extension; `o + 2 + 32·(present kids before j)` in a branch,
`o = 1` or `37` with a value). -/
def NodeV3.kidCidOk (ucid : List Nat) : NodeV3 → Prop
  | .leaf _ _ _ => True
  | .ext k kid _ => ∀ c l r pre po, kid = .node c l r pre po → ucid.getD (5 + (hpN k false).length) 0 = c
  | .branch v kids _ => ∀ j c l r pre po, kids.getD j .none = .node c l r pre po →
      ucid.getD ((if v.isSome then 37 else 1) + 2 + 32 * ((kids.take j).filter (·.present)).length) 0 = c

structure NodeWf3 (vs : List NodeS3) : Prop where
  wf : ∀ s ∈ vs, s.v.wf
  /-- `depth + 112` is a 9-bit value: `depth < 400` unless it wrapped below `0` -/
  depth : ∀ s ∈ vs, s.depth < 400 ∨ P - 112 ≤ s.depth
  res : ∀ n (h : n < vs.length), vs[n].resOk n
  uses : ∀ n (h : n < vs.length), vs[n].uses.length = (edgesOf3 n vs[n]).length
  small : ∀ s ∈ vs, s.tau < P ∧ s.depth < P ∧ s.res < P ∧ s.ubm < P ∧ s.repE < P ∧ ∀ u ∈ s.uses, u < P
  canon : ∀ s ∈ vs, ∀ x ∈ s.v.raw, x < P
  /-- ids are row-segment indices (`< 2^22`) -/
  count : vs.length ≤ 2 ^ 22
  /-- one row per record byte, plus the `SUM` row -/
  rows : (vs.map fun s => (s.v.ser false).length).sum + 1 ≤ 2 ^ 22
  /-- `UPB` columns: one value per byte, canonical -/
  upbLen : ∀ s ∈ vs, s.ucid.length = (s.v.ser false).length ∧ s.mU.length = (s.v.ser false).length
  upbSmall : ∀ s ∈ vs, (∀ x ∈ s.ucid, x < P) ∧ ∀ x ∈ s.mU, x < P
  /-- window child ids on `UPB` -/
  kidCid : ∀ s ∈ vs, s.v.kidCidOk s.ucid

/-- **The `nodeV3` view statement** (any table index `t`). -/
def NodeV3ViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal NodeV3.table tr t pub →
    ∃ vs, NodeWf3 vs ∧ TableTraffic NodeV3.interactions tr t pub (nodeTraffic3 vs)

end ZkFormal.NearV3

import ZkFormal.Near.Extract.Common

/-!
# ZkFormal.Near.Extract.NodeView — what the `node` table holds

A *view* of the node table: one `NodeS` per node segment, in node-id order.
Bytes that the table does not range-check itself (they are range-checked by
the SHA table they are sent to) are kept raw (`List Nat`, values `< p`).
`nodeTraffic` is the exact message list of every interaction; `NodeWf` the
local facts.  The extraction obligation (`NodeViewStmt`) says: a legal node
table has a well-formed view whose traffic is the table's traffic.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec

/-- A child slot as the table holds it. -/
inductive NKid where
  | none
  /-- unrevealed: the 32 window bytes -/
  | hash (h : List Nat)
  /-- revealed: node id, its length and walk target (sent on `PARENT`), and the
  pre/post windows (looked up on `DIGEST`) -/
  | node (cid clen cres : Nat) (pre post : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A value slot as the table holds it. -/
inductive NSlot where
  /-- untouched: `u32` length bytes and hash window -/
  | ref (lenB h : List Nat)
  /-- touched: pre/post value-hash windows (`VPRE/VPOST(nid)`, length 72) -/
  | touched (pre post : List Nat)
  deriving Repr, DecidableEq, Inhabited

inductive NodeV where
  | leaf (key : List Nat) (v : NSlot) (memB : List Nat)
  | ext (key : List Nat) (kid : NKid) (memB : List Nat)
  | branch (v : Option NSlot) (kids : List NKid) (memB : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One node segment: contents, `depth` and walk target `res` (sent on
`PARENT`), and the use counts of the edges it provides (`edgesOf` order). -/
structure NodeS where
  v : NodeV
  depth : Nat
  res : Nat
  uses : List Nat
  deriving Repr, Inhabited

/-! ## Serialization (raw) -/

def hpN (k : List Nat) (leaf : Bool) : List Nat := (hexPrefix k leaf).map (·.toNat)

def NSlot.bytes (post : Bool) : NSlot → List Nat
  | .ref lenB h => lenB ++ h
  | .touched pre po => u32r 72 ++ (if post then po else pre)

def NKid.bytes (post : Bool) : NKid → List Nat
  | .none => []
  | .hash h => h
  | .node _ _ _ pre po => if post then po else pre

def NKid.present : NKid → Bool
  | .none => false
  | _ => true

def kidBitmap (kids : List NKid) : Nat :=
  ((kids.zip (List.range kids.length)).map fun (kd, j) => if kd.present then 2 ^ j else 0).sum

/-- The pre (`post = false`) or post serialization the segment emits. -/
def NodeV.ser (post : Bool) : NodeV → List Nat
  | .leaf k v memB => [0] ++ u32r (hpN k true).length ++ hpN k true ++ v.bytes post ++ memB
  | .ext k kid memB => [3] ++ u32r (hpN k false).length ++ hpN k false ++ kid.bytes post ++ memB
  | .branch v kids memB =>
    (match v with | none => [1] | some s => [2] ++ s.bytes post) ++
      [kidBitmap kids % 256, kidBitmap kids / 256] ++ (kids.flatMap (NKid.bytes post)) ++ memB

def NodeV.touched : NodeV → Bool
  | .leaf _ (.touched _ _) _ => true
  | .branch (some (.touched _ _)) _ _ => true
  | _ => false

/-- Revealed children `(cid, clen, cres, pre, post)` in slot order. -/
def NodeV.revealed : NodeV → List (Nat × Nat × Nat × List Nat × List Nat)
  | .ext _ (.node c l r pre po) _ => [(c, l, r, pre, po)]
  | .branch _ kids _ => kids.filterMap fun
      | .node c l r pre po => some (c, l, r, pre, po)
      | _ => none
  | _ => []

/-! ## Walk edges `[N, I, sym, N', I']` -/

def keyEdges (n : Nat) (k : List Nat) : List Msg :=
  (List.range k.length).map fun i => [n, i, k.getD i 0, n, i + 1]

/-- Edges node `n` provides (in a fixed order; `uses` is aligned with it). -/
def edgesOf (n : Nat) (s : NodeS) : List Msg :=
  (if n = 0 then [[0, 0, SYM_START, s.res, 0]] else []) ++
  match s.v with
  | .leaf k v _ =>
    keyEdges n k ++ (match v with | .touched _ _ => [[n, k.length, SYM_END, n, 0]] | _ => [])
  | .ext k kid _ =>
    keyEdges n (k.dropLast) ++
      (match kid, k.getLast? with
       | .node _ _ cr _ _, some x => [[n, k.length - 1, x, cr, 0]]
       | _, _ => [])
  | .branch v kids _ =>
    ((kids.zip (List.range kids.length)).filterMap fun
      | (.node _ _ cr _ _, j) => some [n, 0, j, cr, 0]
      | _ => none) ++
    (match v with | some (.touched _ _) => [[n, 0, SYM_END, n, 0]] | _ => [])

/-! ## Traffic -/

def nodeSends (vs : List NodeS) (b : Nat) : List Msg :=
  let ns := vs.zip (List.range vs.length)
  if b = B_BYTES then
    ns.flatMap fun (s, n) => emitAt (msgId K_NPRE n) 0 (s.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (s.v.ser true)
  else if b = B_PARENT then
    ns.flatMap fun (s, _) => s.v.revealed.map fun (c, l, r, _, _) => [c, s.depth + 1, l, r]
  else if b = B_EDGE then
    ns.flatMap fun (s, n) => (edgesOf n s).map (· ++ [0])
  else []

def nodeRecvs (vs : List NodeS) (pub : List Fp) (b : Nat) : List Msg :=
  let ns := vs.zip (List.range vs.length)
  let len0 := ((vs.headD default).v.ser false).length
  if b = B_DIGEST then
    [digMsg K_NPRE len0 ((List.range 32).map fun j => pubNat pub (PV_PRE + j)),
     digMsg K_NPOST len0 ((List.range 32).map fun j => pubNat pub (PV_POST + j))] ++
    ns.flatMap fun (s, n) =>
      (s.v.revealed.flatMap fun (c, l, _, pre, po) =>
        [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]) ++
      (match s.v with
       | .leaf _ (.touched pre po) _ | .branch (some (.touched pre po)) _ _ =>
         [digMsg (msgId K_VPRE n) 72 pre, digMsg (msgId K_VPOST n) 72 po]
       | _ => [])
  else if b = B_PARENT then
    (ns.drop 1).map fun (s, n) => [n, s.depth, (s.v.ser false).length, s.res]
  else if b = B_VSLOT then
    ns.filterMap fun (s, n) => if s.v.touched then some [n] else none
  else if b = B_EDGE then
    ns.flatMap fun (s, n) => ((edgesOf n s).zip s.uses).map fun (e, u) => e ++ [u]
  else []

def nodeTraffic (vs : List NodeS) (pub : List Fp) : Traffic := ⟨nodeSends vs, nodeRecvs vs pub⟩

/-! ## Local facts -/

def NKid.wf : NKid → Prop
  | .none => True
  | .hash h => h.length = 32
  | .node _ _ _ pre po => pre.length = 32 ∧ po.length = 32

def NSlot.wf : NSlot → Prop
  | .ref lenB h => lenB.length = 4 ∧ h.length = 32
  | .touched pre po => pre.length = 32 ∧ po.length = 32

def NodeV.wf : NodeV → Prop
  | .leaf k v memB => (∀ x ∈ k, x < 16) ∧ v.wf ∧ memB.length = 8
  | .ext k kid memB => (∀ x ∈ k, x < 16) ∧ kid ≠ .none ∧ kid.wf ∧ memB.length = 8
  | .branch v kids memB => kids.length = 16 ∧ (∀ s, v = some s → s.wf) ∧ (∀ kd ∈ kids, kd.wf) ∧
      memB.length = 8

/-- Walk target: an empty-key extension with a revealed child forwards its
child's target; every other node is its own target. -/
def NodeS.resOk (n : Nat) (s : NodeS) : Prop :=
  match s.v with
  | .ext [] (.node _ _ cr _ _) _ => s.res = cr
  | _ => s.res = n

/-! ## Raw values (all column values, hence canonical naturals `< p`) -/

def NSlot.raw : NSlot → List Nat
  | .ref lenB h => lenB ++ h
  | .touched pre po => pre ++ po

def NKid.raw : NKid → List Nat
  | .none => []
  | .hash h => h
  | .node c l r pre po => [c, l, r] ++ pre ++ po

def NodeV.raw : NodeV → List Nat
  | .leaf k v memB => k ++ v.raw ++ memB
  | .ext k kid memB => k ++ kid.raw ++ memB
  | .branch v kids memB => (v.map NSlot.raw).getD [] ++ kids.flatMap NKid.raw ++ memB

structure NodeWf (vs : List NodeS) : Prop where
  nonempty : vs ≠ []
  wf : ∀ s ∈ vs, s.v.wf
  root_depth : (vs.headD default).depth = 0
  res : ∀ n (h : n < vs.length), vs[n].resOk n
  uses : ∀ n (h : n < vs.length), vs[n].uses.length = (edgesOf n vs[n]).length
  /-- revealed size (node bytes plus 72 per touched value) -/
  size : (vs.map fun s => (s.v.ser false).length + (if s.v.touched then 72 else 0)).sum ≤ 3000000
  /-- field values are canonical naturals -/
  small : ∀ s ∈ vs, s.depth < P ∧ s.res < P ∧ ∀ u ∈ s.uses, u < P
  /-- every raw value of the view is a canonical natural (`Fp.toNat` of a column) -/
  canon : ∀ s ∈ vs, ∀ x ∈ s.v.raw, x < P

def NodeViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal Node.table tr T_NODE pub →
    ∃ vs, NodeWf vs ∧ TableTraffic Node.interactions tr T_NODE pub (nodeTraffic vs pub)

end ZkFormal.Near

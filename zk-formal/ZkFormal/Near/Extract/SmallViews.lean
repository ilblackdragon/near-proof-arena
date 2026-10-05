import ZkFormal.Near.Extract.Common

/-!
# ZkFormal.Near.Extract.SmallViews — views of `walk`, `acct`, `sort`, `mrk`

See `Extract/Common.lean` for the method.  Each `…ViewStmt` is one
extraction obligation.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec

/-! ## walk -/

/-- One walk: receipt `r` and its steps (edge `[N, I, sym, N', I']`, use count). -/
structure WalkV where
  r : Nat
  steps : List (Msg × Nat)
  deriving Repr, Inhabited

def WalkV.edge (w : WalkV) (i : Nat) : Msg := (w.steps.getD i ([], 0)).1

structure WalkWf (ws : List WalkV) : Prop where
  nonempty : ws ≠ []
  steps : ∀ w ∈ ws, 2 ≤ w.steps.length ∧ (∀ st ∈ w.steps, st.1.length = 5 ∧ st.2 < P) ∧ w.r < P
  start : ∀ w ∈ ws, (w.edge 0).take 3 = [0, 0, SYM_START]
  chain : ∀ w ∈ ws, ∀ i, i + 1 < w.steps.length → (w.edge i).drop 3 = (w.edge (i + 1)).take 2
  /-- edge components are canonical naturals -/
  canon : ∀ w ∈ ws, ∀ st ∈ w.steps, ∀ x ∈ st.1, x < P

def walkSends (ws : List WalkV) (b : Nat) : List Msg :=
  if b = B_EDGE then ws.flatMap fun w => w.steps.map fun (e, u) => e ++ [u + 1]
  else if b = B_FINAL then ws.map fun w => [w.r, (w.edge (w.steps.length - 1)).getD 3 0]
  else []

def walkRecvs (ws : List WalkV) (b : Nat) : List Msg :=
  if b = B_EDGE then ws.flatMap fun w => w.steps.map fun (e, u) => e ++ [u]
  else if b = B_KEYNIB then
    ws.flatMap fun w => (List.range (w.steps.length - 1)).map fun t =>
      [w.r, t, (w.edge (t + 1)).getD 2 0, if t + 2 = w.steps.length then 1 else 0]
  else []

def walkTraffic (ws : List WalkV) : Traffic := ⟨walkSends ws, walkRecvs ws⟩

def WalkViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal WalkTab.table tr T_WALK pub →
    ∃ ws, WalkWf ws ∧ TableTraffic WalkTab.interactions tr T_WALK pub (walkTraffic ws)

/-! ## acct -/

/-- One touched slot `k`: pre value (72 raw bytes), post amount (16 raw bytes),
time of the closing memory read. -/
structure AcctV where
  k : Nat
  tlast : Nat
  pre : List Nat
  post : List Nat
  deriving Repr, Inhabited

structure AcctWf (as : List AcctV) : Prop where
  nonempty : as ≠ []
  len : ∀ a ∈ as, a.pre.length = 72 ∧ a.post.length = 16 ∧ a.k < P ∧ a.tlast < P
  /-- AccountV1: the pre amount is not `u128::MAX` (stated for byte values) -/
  notMax : ∀ a ∈ as, (∀ i, i < 16 → a.pre.getD i 0 < 256) → ∃ i, i < 16 ∧ a.pre.getD i 0 ≠ 255
  /-- raw bytes are canonical naturals -/
  canon : ∀ a ∈ as, ∀ x ∈ a.pre ++ a.post, x < P

def acctLane (a : AcctV) (amt : List Nat) (i : Nat) : List Nat :=
  [amt.getD i 0, a.pre.getD (16 + i) 0, if i < 8 then a.pre.getD (64 + i) 0 else 0]

def acctSends (as : List AcctV) (b : Nat) : List Msg :=
  if b = B_BYTES then
    as.flatMap fun a => emitAt (msgId K_VPRE a.k) 0 a.pre ++
      emitAt (msgId K_VPOST a.k) 0 (a.post ++ a.pre.drop 16)
  else if b = B_MEM then
    as.flatMap fun a => (List.range 16).map fun i => [a.k, 0, i] ++ acctLane a a.pre i
  else if b = B_VSLOT then as.map fun a => [a.k]
  else []

def acctRecvs (as : List AcctV) (b : Nat) : List Msg :=
  if b = B_MEM then
    as.flatMap fun a => (List.range 16).map fun i => [a.k, a.tlast, i] ++ acctLane a a.post i
  else []

def acctTraffic (as : List AcctV) : Traffic := ⟨acctSends as, acctRecvs as⟩

def AcctViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal Acct.table tr T_ACCT pub →
    ∃ as, AcctWf as ∧ TableTraffic Acct.interactions tr T_ACCT pub (acctTraffic as)

/-! ## sort -/

/-- The ids in table order: receipt index and 32 raw bytes (LSB first). -/
structure SortWf (ids : List (Nat × List Nat)) : Prop where
  len : ∀ x ∈ ids, x.2.length = 32 ∧ x.1 < P
  /-- raw bytes are canonical naturals -/
  canon : ∀ x ∈ ids, ∀ y ∈ x.2, y < P
  /-- strictly increasing as little-endian integers (stated for byte values) -/
  incr : ∀ t, t + 1 < ids.length →
    (∀ x ∈ ids, ∀ y ∈ x.2, y < 256) →
    leNat ((ids.getD t (0, [])).2.map UInt8.ofNat) < leNat ((ids.getD (t + 1) (0, [])).2.map UInt8.ofNat)

def sortTraffic (ids : List (Nat × List Nat)) : Traffic :=
  ⟨fun _ => [], fun b => if b = B_RIDS then
    ids.flatMap fun (r, bs) => (List.range 32).map fun i => [r, i, bs.getD i 0] else []⟩

def SortViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal Sort.table tr T_SORT pub →
    ∃ ids, SortWf ids ∧ TableTraffic Sort.interactions tr T_SORT pub (sortTraffic ids)

/-! ## mrk -/

/-- `merklize` shape for `n` leaves: the list `(level, index, hashed?)` of the
nodes of levels `1, 2, …` up to the first level of size 1 (fuel `f`). -/
def mrkLevels : Nat → Nat → Nat → List (Nat × Nat × Bool)
  | 0, _, _ => []
  | f + 1, j, sp =>
    let s := (sp + 1) / 2
    ((List.range s).map fun i => (j, i, decide (2 * i + 1 < sp))) ++
      (if s = 1 then [] else mrkLevels f (j + 1) s)

def mrkShape (n : Nat) : List (Nat × Nat × Bool) := mrkLevels (n + 1) 1 n

/-- A child reference `(Id, len)` and, for hashed nodes, its 32-byte window. -/
inductive MrkNode where
  | hashed (lId lLen : Nat) (l : List Nat) (rId rLen : Nat) (r : List Nat)
  | promoted (cId cLen : Nat)
  deriving Repr, Inhabited

/-- The mrk table: root reference `(J, Id, len)` and the nodes in row order. -/
structure MrkV where
  J : Nat
  rootId : Nat
  rootLen : Nat
  nodes : List MrkNode
  deriving Repr, Inhabited

def nPubNat (pub : List Fp) : Nat := (List.range 4).foldr (fun x acc => pubNat pub (PV_N + x) + 256 * acc) 0

def MrkNode.raw : MrkNode → List Nat
  | .hashed lI lL l rI rL r => [lI, lL, rI, rL] ++ l ++ r
  | .promoted cId cLen => [cId, cLen]

structure MrkWf (pub : List Fp) (v : MrkV) : Prop where
  /-- the node kinds follow `merklize` for `n` leaves (`n` from the public bytes,
  stated when those are bytes and `1 ≤ n`) -/
  shape : (∀ x, x < 4 → pubNat pub (PV_N + x) < 256) → 1 ≤ nPubNat pub → nPubNat pub ≤ 256 →
    v.nodes.length = (mrkShape (nPubNat pub)).length ∧
    ∀ q (h : q < v.nodes.length), (match v.nodes[q] with
      | .hashed .. => true | .promoted .. => false) = ((mrkShape (nPubNat pub)).getD q (0, 0, false)).2.2
  windows : ∀ nd ∈ v.nodes, match nd with
    | .hashed _ _ l _ _ r => l.length = 32 ∧ r.length = 32
    | .promoted _ _ => True
  /-- raw values are canonical naturals -/
  canon : v.J < P ∧ v.rootId < P ∧ v.rootLen < P ∧ ∀ nd ∈ v.nodes, ∀ x ∈ nd.raw, x < P

/-- Index among hashed nodes (the `MRK` message index) of node `q`. -/
def hashedBefore (nodes : List MrkNode) (q : Nat) : Nat :=
  ((nodes.take q).filter fun nd => match nd with | .hashed .. => true | _ => false).length

def mrkPos (pub : List Fp) (q : Nat) : Nat × Nat :=
  let p := (mrkShape (nPubNat pub)).getD q (0, 0, false); (p.1, p.2.1)

def mrkSends (pub : List Fp) (v : MrkV) (b : Nat) : List Msg :=
  let qs := v.nodes.zip (List.range v.nodes.length)
  if b = B_BYTES then
    qs.flatMap fun (nd, q) => match nd with
      | .hashed _ _ l _ _ r => emitAt (msgId K_MRK (hashedBefore v.nodes q)) 0 (l ++ r)
      | _ => []
  else if b = B_MPOS then
    qs.map fun (nd, q) => match nd with
      | .hashed .. => [(mrkPos pub q).1, (mrkPos pub q).2, msgId K_MRK (hashedBefore v.nodes q), 64]
      | .promoted cId cLen => [(mrkPos pub q).1, (mrkPos pub q).2, cId, cLen]
  else []

def mrkRecvs (pub : List Fp) (v : MrkV) (b : Nat) : List Msg :=
  let qs := v.nodes.zip (List.range v.nodes.length)
  if b = B_DIGEST then
    digMsg v.rootId v.rootLen ((List.range 32).map fun j => pubNat pub (PV_OUT + j)) ::
    qs.flatMap fun (nd, _) => match nd with
      | .hashed lI lL l rI rL r => [digMsg lI lL l, digMsg rI rL r]
      | _ => []
  else if b = B_MPOS then
    [v.J, 0, v.rootId, v.rootLen] ::
    qs.flatMap fun (nd, q) => match nd with
      | .hashed lI lL _ rI rL _ =>
        [[(mrkPos pub q).1 - 1, 2 * (mrkPos pub q).2, lI, lL],
         [(mrkPos pub q).1 - 1, 2 * (mrkPos pub q).2 + 1, rI, rL]]
      | .promoted cId cLen => [[(mrkPos pub q).1 - 1, 2 * (mrkPos pub q).2, cId, cLen]]
  else []

def mrkTraffic (pub : List Fp) (v : MrkV) : Traffic := ⟨mrkSends pub v, mrkRecvs pub v⟩

def MrkViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp), TableLocal Mrk.table tr T_MRK pub →
    ∃ v, MrkWf pub v ∧ TableTraffic Mrk.interactions tr T_MRK pub (mrkTraffic pub v)

end ZkFormal.Near

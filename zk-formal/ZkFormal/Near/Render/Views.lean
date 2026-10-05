import ZkFormal.Near.Render.Tables
import ZkFormal.Near.Extract.Statements

/-!
# ZkFormal.Near.Render.Views — the honest table views of an `Ext`

The extraction side (`Near/Extract`) describes each table's content by a
*view* (`NodeS`, `WalkV`, `RcptV`, `AcctV`, `MrkV`, sort ids) and its bus
traffic by `xTraffic view`.  Here: the views of the honest trace, built from
the records.  `Render.Statements` states that `render`'s tables have exactly
this traffic, and that the traffic balances.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-! ## node -/

def nslotOf (I : Info) (n : Nat) : VSlot → NSlot
  | .ref len h => .ref (leBytes 4 len) (toNats h)
  | .touched => .touched (shaN (I.vpre.getD n [])) (shaN (I.vpost.getD n []))

def nkidOf (I : Info) : Kid → NKid
  | .none => .none
  | .hash h => .hash (toNats h)
  | .node c' => .node c' (I.pre.getD c' []).length (I.res.getD c' c') (I.preDig c') (I.postDig c')

def nodeVOf (I : Info) (n : Nat) : NodeRec → NodeV
  | .leaf k v mem => .leaf k (nslotOf I n v) (leBytes 8 mem)
  | .ext k kid mem => .ext k (nkidOf I kid) (leBytes 8 mem)
  | .branch v kids mem => .branch (v.map (nslotOf I n)) (kids.map (nkidOf I)) (leBytes 8 mem)

def nodeViewOf (I : Info) (uses : Std.HashMap Edge Nat) (n : Nat) : NodeS :=
  let s0 : NodeS := ⟨nodeVOf I n (I.nodeAt n), I.depth.getD n 0, I.res.getD n n, []⟩
  { s0 with uses := (edgesOf n s0).map fun e => uses.getD e 0 }

def nodeViewsOf (I : Info) (uses : Std.HashMap Edge Nat) : List NodeS :=
  (List.range I.ns.size).map (nodeViewOf I uses)

/-! ## walk -/

/-- Steps with their chained counters, in table order. -/
def walkViewsOf (ws : List (List WStep)) : List WalkV := Id.run do
  let mut cnt : Std.HashMap Edge Nat := {}
  let mut out : Array WalkV := #[]
  for (w, r) in ws.zip (List.range ws.length) do
    let mut steps : Array (ZkFormal.Near.Msg × Nat) := #[]
    for s in w do
      let u := cnt.getD s.edge 0
      cnt := cnt.insert s.edge (u + 1)
      steps := steps.push (s.edge, u)
    out := out.push ⟨r, steps.toList⟩
  return out.toList

/-! ## acct, sort -/

def acctViewsOf (I : Info) : List AcctV :=
  I.touched.map fun k => ⟨k, tlastOf I.e k, I.vpre.getD k [], (I.vpost.getD k []).take 16⟩

def sortIdsOf (I : Info) : List (Nat × List Nat) := sortedIds I

/-! ## mrk -/

/-- The merkle view (same level walk as `mrkBuild`). -/
def mrkViewOf (I : Info) : MrkV := Id.run do
  let n := I.nRcpt
  let mut cur : List MNode := (List.range n).map fun r => ⟨msgId K_LEAF r, 68, shaN (leafBytes I r)⟩
  let mut j := 1
  let mut q := 0
  let mut nodes : Array MrkNode := #[]
  let mut fuel := n + 2
  let mut done := false
  while !done && fuel > 0 do
    fuel := fuel - 1
    let sp := cur.length
    let s := (sp + 1) / 2
    let mut nxt : Array MNode := #[]
    for i in List.range s do
      if 2 * i + 1 < sp then
        let L := cur.getD (2 * i) default
        let R := cur.getD (2 * i + 1) default
        nodes := nodes.push (.hashed L.id L.len L.dig R.id R.len R.dig)
        nxt := nxt.push ⟨msgId K_MRK q, 64, shaN (L.dig ++ R.dig)⟩
        q := q + 1
      else
        let C := cur.getD (2 * i) default
        nodes := nodes.push (.promoted C.id C.len)
        nxt := nxt.push C
    cur := nxt.toList
    if s == 1 then done := true else j := j + 1
  let root := cur.getD 0 default
  return ⟨n, j, root.id, root.len, nodes.toList⟩

/-! ## rcpt -/

def rcptViewOf (d : RcptGen.RD) : RcptV :=
  let aft := d.bef + d.dep
  { p := d.pred, v := d.recv, s := d.signer, rid := d.id, kt := d.kt, pk := d.pk,
    gp := leBytes 16 d.gp, dep := leBytes 16 d.dep, hr := d.hr, ge := d.ge, kslot := d.kslot,
    tprev := d.tprev, bef := leBytes 16 d.bef, lk := leBytes 16 d.locked,
    st := leBytes 8 d.stor ++ List.replicate 8 0, aft := leBytes 16 aft,
    burnt := leBytes 16 d.burnt, ramt := leBytes 16 d.ramt,
    rfid := if d.hr then d.refundId else List.replicate 32 0, peoh := d.peoDig }

def rcptViewsOf (I : Info) : RcptVs := (rcptData I).map rcptViewOf

/-! ## sha -/

/-- The SHA table's traffic on messages `ms` (L5's expected traffic). -/
def shaTraffic (ms : List Render.Msg) : Traffic :=
  let gm : List Sha.Gen.Msg := ms.map fun m => ⟨m.id, m.bytes, true⟩
  ⟨fun b => if b = B_DIGEST then Sha.Gen.expectedDigests gm else [],
   fun b => if b = B_BYTES then Sha.Gen.expectedBytes gm else []⟩

/-! ## All honest traffic -/

/-- The honest traffic of the seven tables (`nearAir` order). -/
def honestTraffic (c : Claim) (e : Ext) : List Traffic :=
  let B := bundle c e
  let pub := pubOf c
  let I := B.info
  let uses := edgeUses B.walks
  [shaTraffic B.msgs, nodeTraffic (nodeViewsOf I uses) pub, walkTraffic (walkViewsOf B.walks),
   rcptTraffic pub (rcptViewsOf I), acctTraffic (acctViewsOf I), mrkTraffic pub (mrkViewOf I),
   sortTraffic (sortIdsOf I)]

end ZkFormal.Near.Render

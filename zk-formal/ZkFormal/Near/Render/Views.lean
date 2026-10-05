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

/-- Index of the first step of walk `r` in table order. -/
def walkOff (ws : List (List WStep)) (r : Nat) : Nat := ((ws.take r).map List.length).sum

/-- Steps with their chained counters, in table order. -/
def walkViewsOf (ws : List (List WStep)) : List WalkV :=
  let us := usesL (walkSteps ws)
  (List.range ws.length).map fun r =>
    ⟨r, (List.range (ws.getD r []).length).map fun j =>
      (((ws.getD r []).getD j default).edge, us.getD (walkOff ws r + j) 0)⟩

/-! ## acct, sort -/

def acctViewsOf (I : Info) : List AcctV :=
  I.touched.map fun k => ⟨k, tlastOf I.e k, I.vpre.getD k [], (I.vpost.getD k []).take 16⟩

def sortIdsOf (I : Info) : List (Nat × List Nat) := sortedIds I

/-! ## mrk -/

/-- The merkle view (the levels of `MrkGen`). -/
def mrkViewOf (I : Info) : MrkV :=
  let n := I.nRcpt
  let lv := (List.range (MrkGen.topJ n + 1)).map (MrkGen.levels I)
  let C (j k : Nat) : MNode := (lv.getD (j - 1) []).getD k default
  let root := (lv.getD (MrkGen.topJ n) []).getD 0 default
  ⟨n, MrkGen.topJ n, root.id, root.len, (mrkShape n).map fun (j, i, h) =>
    if h then .hashed (C j (2 * i)).id (C j (2 * i)).len (C j (2 * i)).dig
      (C j (2 * i + 1)).id (C j (2 * i + 1)).len (C j (2 * i + 1)).dig
    else .promoted (C j (2 * i)).id (C j (2 * i)).len⟩

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

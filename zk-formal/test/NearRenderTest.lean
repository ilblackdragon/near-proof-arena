import ZkFormal.Near.Render.Views
import ZkFormal.Near.Render.Trace

/-! Executable checks of the NEAR honest-trace generators (lane L6e): all six
NEAR tables (node, walk, rcpt, acct, mrk, sort) and every bus, with the `sha`
side from L5's expected traffic.
Run: `lake env lean test/NearRenderTest.lean`.  Not part of the library.

Each example is a small hand-built `Ext` (with the claim computed from it);
for each we print the constraint violations of each table and the balance
of every bus (`sha*` in the contributions = simulated sha side). -/

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air

namespace NearRenderTest

def str (s : String) : Bytes := s.toUTF8.toList
def hsh (s : String) : Bytes := sha256 (str s)
def keyOf (name : String) : List Nat := accountKeyPath (str name)
def kidsL (l : List (Nat × Kid)) : List Kid := (List.range 16).map fun i => (l.lookup i).getD .none

def acctBytes (amt : Nat) (stor : Nat := 182) : Bytes :=
  Account.encode ⟨amt, 7 * 10 ^ 20, hsh "code", stor⟩

def rcptOf (recv : String) (i gp dep : Nat) : Receipt :=
  ⟨str "carol.near", str recv, hsh s!"receipt{i}", str "carol.near", ⟨0, hsh "pk"⟩, gp, dep⟩

def bgp : Nat := 100000000

def mkExt (ns : List NodeRec) (amts : List (Nat × Nat)) (rs : List (Receipt × Nat)) : Ext :=
  { ns, vals0 := fun k => match amts.lookup k with | some a => acctBytes a | none => [],
    rs := rs.map (·.1), slot := fun r => (rs.map (·.2)).getD r 0 }

def mkClaim (e : Ext) : Claim :=
  let c0 : Claim :=
    { protocolVersion := 86, chainId := Params.chainId, shardId := 3, blockHeight := 1000,
      blockGasPrice := bgp, gasLimit := 10 ^ 15, preStateRoot := zeroHash,
      receiptCount := e.rs.length, receiptsCommitment := zeroHash, slicePostRoot := zeroHash,
      outcomeRoot := zeroHash, refundCount := 0, refundsCommitment := zeroHash,
      gasBurntTotal := 0, tokensBurntTotal := 0 }
  { c0 with preStateRoot := (trieOf e.ns e.vals0).hashOf,
            receiptsCommitment := receiptsCommitment c0.shardId e.rs,
            slicePostRoot := (trieOf e.ns (e.valsAt e.rs.length)).hashOf,
            outcomeRoot := outcomeRoot (e.outcomes c0),
            refundCount := (e.refunds c0).length,
            refundsCommitment := refundsCommitment (e.refunds c0),
            gasBurntTotal := e.rs.length * Params.G,
            tokensBurntTotal := e.tokAt c0 e.rs.length }

def nodeGroups : List (String × Nat) :=
  [("cBool", Node.cBool.length), ("cRows", Node.cRows.length), ("cTrans", Node.cTrans.length),
   ("cFields", Node.cFields.length), ("cBytes", Node.cBytes.length),
   ("cWindows", Node.cWindows.length), ("cLinks", Node.cLinks.length)]

def run (name : String) (e : Ext) : IO Unit := do
  let c := mkClaim e
  let pub := pubOf c
  IO.println s!"=== {name}: {e.ns.length} nodes, {e.rs.length} receipts, pub {pub.length}"
  match bundle c e with
  | .error err => IO.println s!"generator error: {err}"
  | .ok B =>
    for (nm, T, rows) in B.tables do
      let groups := if nm == "node" then nodeGroups else []
      for l in reportTable nm T rows pub groups do IO.println l
    for l in reportBus (B.bus pub) do IO.println l

/-! ## Examples -/

def ref1 : VSlot := .ref 100 (hsh "someval")

/-- Root branch (with an unrevealed value) → branches → a branch with two touched leaves. -/
def ex1 : Ext := mkExt
  [ .branch (some ref1) (kidsL [(0, .node 1), (4, .hash (hsh "h1"))]) 1000,
    .branch none (kidsL [(0, .node 2), (3, .hash (hsh "h2"))]) 900,
    .branch none (kidsL [(6, .node 3)]) 800,
    .branch none (kidsL [(1, .node 4), (2, .node 5), (7, .hash (hsh "h3"))]) 700,
    .leaf ((keyOf "alice").drop 4) .touched 300,
    .leaf ((keyOf "bob").drop 4) .touched 310 ]
  [(4, 5 * 10 ^ 24), (5, 10 ^ 24)]
  [(rcptOf "alice" 0 (2 * bgp) (10 ^ 23), 4), (rcptOf "bob" 1 bgp (3 * 10 ^ 22), 5)]

/-- Extension (odd key) → branch → two touched leaves, plus dead extensions; 3 receipts. -/
def ex2 : Ext := mkExt
  [ .ext [0, 0, 6] (.node 1) 2000,
    .branch none (kidsL [(1, .node 2), (2, .node 3), (9, .node 4), (10, .node 5)]) 1500,
    .leaf ((keyOf "alice").drop 4) .touched 300,
    .leaf ((keyOf "bob").drop 4) .touched 310,
    .ext [5] (.hash (hsh "d1")) 200,
    .ext [3, 4, 5] (.hash (hsh "d2")) 210 ]
  [(2, 5 * 10 ^ 24), (3, 10 ^ 24)]
  [(rcptOf "alice" 0 (2 * bgp) (10 ^ 23), 2), (rcptOf "bob" 1 bgp 7, 3),
   (rcptOf "alice" 2 (3 * bgp) (10 ^ 21), 2)]

/-- Branch with a touched value (`bob`) and a touched leaf below (`bobx`). -/
def ex3 : Ext := mkExt
  [ .ext (keyOf "bob") (.node 1) 2000,
    .branch (some .touched) (kidsL [(7, .node 2), (3, .hash (hsh "h"))]) 1500,
    .leaf [8] .touched 300 ]
  [(1, 4 * 10 ^ 24), (2, 10 ^ 24)]
  [(rcptOf "bobx" 0 (2 * bgp) 5, 2), (rcptOf "bob" 1 (2 * bgp) 6, 1)]

/-- Empty-key extensions (root and inner) and a one-nibble extension; 1 receipt. -/
def ex4 : Ext := mkExt
  [ .ext [] (.node 1) 3000,
    .ext [0, 0] (.node 2) 2900,
    .branch none (kidsL [(6, .node 3), (2, .hash (hsh "x"))]) 2800,
    .ext [] (.node 4) 2700,
    .ext [1] (.node 5) 2600,
    .leaf ((keyOf "alice").drop 4) .touched 300 ]
  [(5, 5 * 10 ^ 24)]
  [(rcptOf "alice" 0 (2 * bgp) (10 ^ 23), 5)]

/-- Check of `render`: the NEAR tables read back from the trace (tables
`1 … 6` of `nearAir`), whole-AIR bus balance with `sha` simulated. -/
def runFull (name : String) (e : Ext) : IO Unit := do
  let c := mkClaim e
  let pub := pubOf c
  let tr := render c e
  let names := ["node", "walk", "rcpt", "acct", "mrk", "sort"]
  IO.println s!"=== render {name}: logs {(List.range 7).map tr.log}"
  let mut traffic : List (String × BusMsg) := []
  for (nm, t) in names.zip (List.range 6) do
    let T := nearAir.tables.getD (t + 1) default
    let rows : Array Row := (List.range (tr.height (t + 1))).toArray.map fun r =>
      (List.range T.width).toArray.map fun col => (tr.cell (t + 1) r col).toNat
    for l in reportTable nm T rows pub (if nm == "node" then nodeGroups else []) do IO.println l
    traffic := traffic ++ tableBus nm T rows pub
  traffic := traffic ++ ((shaSim (renderParts c e).1).map ("sha*", ·))
  for l in reportBus traffic do IO.println l

def mkExt' (ns : List NodeRec) (amts : List (Nat × Nat × Nat)) (rs : List (Receipt × Nat)) : Ext :=
  { ns, vals0 := fun k => match amts.lookup k with | some (a, st) => acctBytes a st | none => [],
    rs := rs.map (·.1), slot := fun r => (rs.map (·.2)).getD r 0 }

def long64 : String := "abcdefghijklmnopqrstuvwxyz-0123456789_abcdefghijklmnopqrstuvw.xy"
def hexish : String := "0x" ++ "0123456789abcdef0123456789abcdef0123456g"

def rcptFull (pred recv signer : String) (pk : PublicKey) (i gp dep : Nat) : Receipt :=
  ⟨str pred, str recv, hsh s!"receipt{i}", str signer, pk, gp, dep⟩

def secpPk : PublicKey := ⟨1, hsh "k1" ++ hsh "k2"⟩

/-- Receipt-level variety: a 64-char receiver, a SECP256K1 signer key, gas price
below / equal to / above the block price (refund only above), predecessor of
length 6 (≠ "system"), a `0x`+40 receiver that is not hex (named), storage
`≤ 770` with balance below the storage stake and storage `> 770` above it. -/
def ex5 : Ext := mkExt'
  [ .branch none (kidsL [(0, .node 1), (1, .hash (hsh "o"))]) 1000,
    .branch none (kidsL [(0, .node 2)]) 900,
    .branch none (kidsL [(6, .node 3), (3, .node 4)]) 800,
    .leaf ((keyOf long64).drop 3) .touched 300,
    .leaf ((keyOf hexish).drop 3) .touched 310 ]
  [(3, 5 * 10 ^ 24, 5000), (4, 10 ^ 21, 700)]
  [(rcptFull "carol.near" long64 "dave_1.near" secpPk 0 (bgp / 2) (10 ^ 23), 3),
   (rcptFull "sysabc" hexish "eve.tg" ⟨0, hsh "pk"⟩ 1 (3 * bgp) 12345, 4),
   (rcptFull "x-y.z_w" long64 "dave_1.near" secpPk 2 bgp 0, 3),
   (rcptFull "carol.near" hexish "zz" secpPk 3 (bgp + 1) (2 ^ 100), 4)]

/-- Messages as a sorted list (multiset comparison). -/
def msort (l : List (List Nat)) : List (List Nat) :=
  l.mergeSort fun a b => decide (toString a ≤ toString b)

/-- `TrafficStmt` check: each table's traffic equals its honest view traffic
(`Render.Views`), and the honest traffic balances on every bus (`BusStmt`). -/
def runViews (name : String) (e : Ext) : IO Unit := do
  let c := mkClaim e
  let pub := pubOf c
  match bundle c e with
  | .error err => IO.println s!"generator error: {err}"
  | .ok B =>
    let tfs := honestTraffic c e
    let mut ok := true
    for ((nm, T, rows), t) in B.tables.zip [1, 2, 3, 4, 5, 6] do
      let act := tableBus nm T rows pub
      let tf := tfs.getD t ⟨fun _ => [], fun _ => []⟩
      for b in List.range 10 do
        for s in [true, false] do
          let got := msort ((act.filter fun (_, m) => m.bus == b && m.send == s).flatMap
            fun (_, m) => List.replicate m.mult m.msg)
          let want := msort (if s then tf.sends b else tf.recvs b)
          if got != want then
            ok := false
            IO.println s!"  {nm} bus {busName b} {if s then "send" else "recv"}: table {got.length} vs view {want.length}; first diff {((got.filter (!want.contains ·)).take 2)} / {((want.filter (!got.contains ·)).take 2)}"
    let traffic : List (String × BusMsg) := (tfs.zip (List.range 7)).flatMap fun (tf, t) =>
      (List.range 10).flatMap fun b =>
        (tf.sends b).map (fun m => (s!"t{t}", ({ bus := b, send := true, msg := m } : BusMsg))) ++
        (tf.recvs b).map (fun m => (s!"t{t}", ({ bus := b, send := false, msg := m } : BusMsg)))
    let ims := imbalances traffic
    IO.println s!"=== views {name}: traffic = view traffic: {ok}; honest view traffic unbalanced messages: {ims.length}"
    for im in ims.take 5 do IO.println s!"    {busName im.bus} {im.msg.take 8} net {im.net} by {im.by_}"

end NearRenderTest

open NearRenderTest in
#eval do
  run "ex1 branch, 2 leaves" ex1
  run "ex2 ext→branch→leaves, 3 receipts" ex2
  run "ex3 branch with value" ex3
  run "ex4 empty-key extensions, 1 receipt" ex4
  run "ex5 receipt variety (long ids, secp key, gas below/equal/above, storage cases)" ex5

open NearRenderTest in
#eval do
  for (nm, e) in [("ex1", ex1), ("ex2", ex2), ("ex3", ex3), ("ex4", ex4), ("ex5", ex5)] do
    runViews nm e

open NearRenderTest in
#eval do
  runFull "ex4" ex4
  runFull "ex3" ex3

/-! Negative check: a 65-character predecessor (invalid account id) violates
exactly the `L ≤ 64` constraint added to `rcpt` (before the fix the honest-style
trace of this receipt satisfied every rcpt constraint). -/
open NearRenderTest in
#eval do
  let long65 := long64 ++ "q"
  let e := mkExt' ex5.ns [(3, 5 * 10 ^ 24, 5000), (4, 10 ^ 21, 700)]
    [(rcptFull long65 long64 "dave_1.near" secpPk 0 (bgp / 2) (10 ^ 23), 3)]
  let c := mkClaim e
  match bundle c e with
  | .error err => IO.println err
  | .ok B =>
    let vs := violations Rcpt.table B.rcpt (pubOf c)
    IO.println s!"65-char predecessor: rcpt violations {groupViol vs}"

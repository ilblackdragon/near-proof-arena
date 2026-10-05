import ZkFormal.Near.Render.Trace

/-! Executable checks of the NEAR honest-trace generators (lane L6e).
Run: `lake env lean test/NearRenderTest.lean`.  Not part of the library.

Each example is a small hand-built `Ext` (with the claim computed from it);
for each we print the constraint violations of node / walk / acct / mrk /
sort and the balance of every bus, with `sha` and `rcpt` simulated
(`rcpt*`, `sha*` in the contributions). -/

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
`1 … 6` of `nearAir`), whole-AIR bus balance with `sha` and `rcpt` simulated. -/
def runFull (name : String) (e : Ext) : IO Unit := do
  let c := mkClaim e
  let pub := pubOf c
  let tr := render c e
  let names := ["node", "walk", "rcpt(placeholder)", "acct", "mrk", "sort"]
  IO.println s!"=== render {name}: logs {(List.range 7).map tr.log}"
  let mut traffic : List (String × BusMsg) := []
  for (nm, t) in names.zip (List.range 6) do
    let T := nearAir.tables.getD (t + 1) default
    let rows : Array Row := (List.range (tr.height (t + 1))).toArray.map fun r =>
      (List.range T.width).toArray.map fun col => (tr.cell (t + 1) r col).toNat
    for l in reportTable nm T rows pub (if nm == "node" then nodeGroups else []) do IO.println l
    traffic := traffic ++ tableBus nm T rows pub
  let I := mkInfo c e
  traffic := traffic ++ ((rcptBus I ++ bytesSends (rcptMsgs I)).map ("rcpt*", ·)) ++
    ((shaSim (renderParts c e).1).map ("sha*", ·))
  for l in reportBus traffic do IO.println l

end NearRenderTest

open NearRenderTest in
#eval do
  run "ex1 branch, 2 leaves" ex1
  run "ex2 ext→branch→leaves, 3 receipts" ex2
  run "ex3 branch with value" ex3
  run "ex4 empty-key extensions, 1 receipt" ex4

open NearRenderTest in
#eval do
  runFull "ex4" ex4
  runFull "ex3" ex3

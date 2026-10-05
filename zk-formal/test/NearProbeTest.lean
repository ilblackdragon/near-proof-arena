import ZkFormal.Near.Render.Tables

/-! Single-cell mutation probe of the NEAR tables on honest traces (lane L6e).
Run: `lake env lean test/NearProbeTest.lean`.  For each table, a sample of
rows (one per pattern of its flag columns) and every column: a `+1` change
that no constraint and no interaction observes is listed as free.  Free cells
are expected for don't-care columns; a free cell that carries meaning is a
soundness hole. -/

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air

namespace NearProbeTest

def str (s : String) : Bytes := s.toUTF8.toList
def hsh (s : String) : Bytes := sha256 (str s)
def keyOf (name : String) : List Nat := accountKeyPath (str name)
def kidsL (l : List (Nat × Kid)) : List Kid := (List.range 16).map fun i => (l.lookup i).getD .none
def acctBytes (amt : Nat) : Bytes := Account.encode ⟨amt, 7 * 10 ^ 20, hsh "code", 182⟩
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

/-- Mixed example: odd extension, branch with touched value and children,
dead extension, leaves (odd/even keys); 3 receipts. -/
def ex : Ext := mkExt
  [ .ext [0, 0, 6] (.node 1) 2000,
    .branch none (kidsL [(1, .node 2), (2, .node 3), (9, .node 4)]) 1500,
    .leaf ((keyOf "alice").drop 4) .touched 300,
    .ext ((keyOf "bob").drop 4) (.node 5) 310,
    .ext [5] (.hash (hsh "d1")) 200,
    .branch (some .touched) (kidsL [(7, .node 6), (3, .hash (hsh "h"))]) 1400,
    .leaf [8] .touched 300 ]
  [(2, 5 * 10 ^ 24), (5, 10 ^ 24), (6, 10 ^ 22)]
  [(rcptOf "alice" 0 (2 * bgp) (10 ^ 23), 2), (rcptOf "bob" 1 bgp 7, 5),
   (rcptOf "bobx" 2 (3 * bgp) (10 ^ 21), 6)]

def probe (nm : String) (T : Table) (rows : Array Row) (pub : List ZkFormal.Algebra.Fp)
    (key : List Nat) : IO Unit := do
  let smp := sampleRows rows key
  let fr := freeCells T rows pub smp
  IO.println s!"{nm}: probed {smp.length} rows × {T.width} cols, {fr.length} free cells"
  let cols := fr.foldl (fun acc (_, c) => if acc.contains c then acc else acc ++ [c]) []
  for c in cols do
    let rs := (fr.filter (·.2 == c)).map (·.1)
    IO.println s!"  col {c}: free on rows {rs}"

/-- Per sampled row: its rcpt field state and free columns. -/
def probeRcpt (rows : Array Row) (pub : List ZkFormal.Algebra.Fp) : IO Unit := do
  let key := [Rcpt.act, Rcpt.fs, Rcpt.fe, Rcpt.rl, Rcpt.hr, Rcpt.kz, Rcpt.r1, Rcpt.lo8, Rcpt.lo4,
    Rcpt.big, Rcpt.ge] ++ Rcpt.states
  let smp := sampleRows rows key
  let fr := freeCells Rcpt.table rows pub smp
  let names := ["CL", "PL", "P", "VL", "V", "RID", "T0", "SL", "S", "KT", "PK", "GP", "TL", "DEP",
    "XP0", "XRI", "XG", "XST", "XL0", "XLH", "XRH", "XRF", "XRZ"]
  for r in smp do
    let row := rows.getD r #[]
    let st := ((Rcpt.states.zip names).find? fun (c, _) => row.getD c 0 == 1).map (·.2) |>.getD "pad"
    let cols := (fr.filter (·.1 == r)).map (·.2)
    IO.println s!"row {r} {st} idx {row.getD Rcpt.idx 0} fs {row.getD Rcpt.fs 0} fe {row.getD Rcpt.fe 0}: {cols}"

end NearProbeTest

open NearProbeTest in
#eval do
  let c := mkClaim ex
  let pub := pubOf c
  let B := bundle c ex
  if !B.errors.isEmpty then IO.println s!"generator error: {B.errors}"
  do
    -- node: patterns of type, state, fs/fe, nf/nl, gates
    probe "node" Node.table B.node pub
      ([Node.act, Node.nf, Node.nl, Node.sumr, Node.tl, Node.te, Node.tb1, Node.tb2, Node.fs,
        Node.fe, Node.odd, Node.nokey, Node.rv, Node.tv, Node.gA, Node.gB, Node.lastw] ++ Node.states)
    probe "walk" WalkTab.table B.walk pub [WalkTab.act, WalkTab.ws, WalkTab.we]
    probeRcpt B.rcpt pub
    probe "acct" Acct.table B.acct pub [Acct.act, Acct.af, Acct.al, Acct.lo8, Acct.i]
    probe "mrk" Mrk.table B.mrk pub [Mrk.rt, Mrk.sg, Mrk.pr, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.pw]
    probe "sort" Sort.table B.sort pub [Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.i]

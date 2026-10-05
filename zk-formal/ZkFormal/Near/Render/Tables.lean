import ZkFormal.Near.Render.Node
import ZkFormal.Near.Render.Walk
import ZkFormal.Near.Render.Acct
import ZkFormal.Near.Render.Mrk
import ZkFormal.Near.Render.Sort
import ZkFormal.Near.Render.Check

/-!
# ZkFormal.Near.Render.Tables — all honest NEAR-side tables of an `Ext`

`bundle c e` runs every generator (node, walk, acct, mrk, sort), collects
the SHA messages of every table (rcpt's simulated) and the simulated `rcpt`
bus traffic; `bundleBus` is the whole traffic of the AIR with `sha` and `rcpt`
simulated, for `imbalances`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

structure Bundle where
  info : Info
  walks : List (List WStep)
  node : Array Row
  walk : Array Row
  acct : Array Row
  mrk : Array Row
  sort : Array Row
  /-- every SHA message (node, acct, mrk, rcpt) -/
  msgs : List Msg

def bundle (c : Claim) (e : Ext) : Except String Bundle := do
  let I := mkInfo c e
  let ws ← walksOf I
  let uses := edgeUses ws
  pure { info := I, walks := ws, node := nodeRowsAll I uses, walk := walkRowsAll ws,
         acct := acctRowsAll I, mrk := mrkRowsAll I, sort := sortRowsAll I,
         msgs := nodeMsgs I ++ acctMsgs I ++ mrkMsgs I ++ rcptMsgs I }

/-- Public inputs of a claim (`publicOf`). -/
def pubOf (c : Claim) : List Fp := c.encode.map fun b => Fp.ofNat b.toNat

/-- The five rendered tables with names. -/
def Bundle.tables (B : Bundle) : List (String × Table × Array Row) :=
  [("node", Node.table, B.node), ("walk", WalkTab.table, B.walk), ("acct", Acct.table, B.acct),
   ("mrk", Mrk.table, B.mrk), ("sort", Sort.table, B.sort)]

/-- All bus traffic: rendered tables + simulated `rcpt` (incl. its BYTES) +
simulated `sha`. -/
def Bundle.bus (B : Bundle) (pub : List Fp) : List (String × BusMsg) :=
  (B.tables.flatMap fun (nm, T, rows) => tableBus nm T rows pub) ++
  ((rcptBus B.info ++ bytesSends (rcptMsgs B.info)).map ("rcpt*", ·)) ++
  ((shaSim B.msgs).map ("sha*", ·))

end ZkFormal.Near.Render

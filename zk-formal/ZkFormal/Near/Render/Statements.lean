import ZkFormal.Near.Render.Views
import ZkFormal.Near.Render.Trace
import ZkFormal.Near.Extract.Compose
import ZkFormal.Near.Statements

/-!
# ZkFormal.Near.Render.Statements — the split of `RenderStmt`

`RenderStmt : ∀ c e, Good c.1 e → Holds nearAir (publicOf c) (render c.1 e)`
follows (`Render.Compose`) from

| statement | content |
|---|---|
| `LocalStmt t T` (×7) | table `t` of the honest trace is locally legal: height in `[2, 2^maxLog]`, every constraint on every row, every multiplicity bit boolean |
| `TrafficStmt t is tf` (×7) | table `t`'s bus traffic is exactly the honest view traffic `honestTraffic c e` (the extraction side's `xTraffic` of the honest views, `Render.Views`; for `sha`, L5's expected traffic) |
| `BusStmt b` (×10) | the honest traffic balances on bus `b` (trace-free) |
| `other_bus` | (proved) no honest traffic on buses `≥ 10` |

All are stated under `Good c.1 e` (the honest records), and `render` is
`ZkFormal.Near.Render.render`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- The honest traffic of table `t`. -/
def htf (c : Claim) (e : Ext) (t : Nat) : Traffic :=
  (honestTraffic c e).getD t ⟨fun _ => [], fun _ => []⟩

/-- Table `t` (`T`) of the honest trace is locally legal. -/
def LocalStmt (t : Nat) (T : Table) : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → TableLocal T (render c.1 e) t (publicOf c)

/-- Table `t` (interactions `is`) of the honest trace has the honest traffic. -/
def TrafficStmt (t : Nat) (is : List Interaction) : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → TableTraffic is (render c.1 e) t (publicOf c) (htf c.1 e t)

/-- Sends (`s = true`) or receives of a traffic. -/
def sel (s : Bool) (tf : Traffic) : Nat → List ZkFormal.Near.Msg := if s then tf.sends else tf.recvs

/-- Count of `m` on bus `b`, side `s`, in table `t`'s honest traffic. -/
def hc (c : Claim) (e : Ext) (b : Nat) (s : Bool) (m : List Fp) (t : Nat) : Nat :=
  cnt (sel s (htf c e t) b) m

/-- Total count over the seven tables (same shape as `busCount_near`). -/
def hcount (c : Claim) (e : Ext) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  hc c e b s m 0 + (hc c e b s m 1 + (hc c e b s m 2 + (hc c e b s m 3 + (hc c e b s m 4 +
    (hc c e b s m 5 + (hc c e b s m 6 + 0))))))

/-- The honest traffic balances on bus `b`. -/
def BusStmt (b : Nat) : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → ∀ m, hcount c.1 e b true m = hcount c.1 e b false m

def ShaLocalStmt : Prop := LocalStmt T_SHA (Sha.Table.table B_BYTES B_DIGEST)
def NodeLocalStmt : Prop := LocalStmt T_NODE Node.table
def WalkLocalStmt : Prop := LocalStmt T_WALK WalkTab.table
def RcptLocalStmt : Prop := LocalStmt T_RCPT Rcpt.table
def AcctLocalStmt : Prop := LocalStmt T_ACCT Acct.table
def MrkLocalStmt : Prop := LocalStmt T_MRK Mrk.table
def SortLocalStmt : Prop := LocalStmt T_SORT Sort.table

def ShaTrafficStmt : Prop := TrafficStmt T_SHA (Sha.Table.interactions B_BYTES B_DIGEST)
def NodeTrafficStmt : Prop := TrafficStmt T_NODE Node.interactions
def WalkTrafficStmt : Prop := TrafficStmt T_WALK WalkTab.interactions
def RcptTrafficStmt : Prop := TrafficStmt T_RCPT Rcpt.interactions
def AcctTrafficStmt : Prop := TrafficStmt T_ACCT Acct.interactions
def MrkTrafficStmt : Prop := TrafficStmt T_MRK Mrk.interactions
def SortTrafficStmt : Prop := TrafficStmt T_SORT Sort.interactions

def BytesBusStmt : Prop := BusStmt B_BYTES
def DigestBusStmt : Prop := BusStmt B_DIGEST
def ParentBusStmt : Prop := BusStmt B_PARENT
def VslotBusStmt : Prop := BusStmt B_VSLOT
def EdgeBusStmt : Prop := BusStmt B_EDGE
def KeynibBusStmt : Prop := BusStmt B_KEYNIB
def FinalBusStmt : Prop := BusStmt B_FINAL
def MemBusStmt : Prop := BusStmt B_MEM
def RidsBusStmt : Prop := BusStmt B_RIDS
def MposBusStmt : Prop := BusStmt B_MPOS

/-- All the obligations of `RenderStmt`. -/
structure RenderObligations : Prop where
  shaL : ShaLocalStmt
  nodeL : NodeLocalStmt
  walkL : WalkLocalStmt
  rcptL : RcptLocalStmt
  acctL : AcctLocalStmt
  mrkL : MrkLocalStmt
  sortL : SortLocalStmt
  shaT : ShaTrafficStmt
  nodeT : NodeTrafficStmt
  walkT : WalkTrafficStmt
  rcptT : RcptTrafficStmt
  acctT : AcctTrafficStmt
  mrkT : MrkTrafficStmt
  sortT : SortTrafficStmt
  bytes : BytesBusStmt
  digest : DigestBusStmt
  parent : ParentBusStmt
  vslot : VslotBusStmt
  edge : EdgeBusStmt
  keynib : KeynibBusStmt
  final : FinalBusStmt
  mem : MemBusStmt
  rids : RidsBusStmt
  mpos : MposBusStmt

end ZkFormal.Near.Render

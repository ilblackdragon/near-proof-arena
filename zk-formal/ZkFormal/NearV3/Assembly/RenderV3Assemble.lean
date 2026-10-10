import ZkFormal.NearV3.Assembly.NearAirBus
import ZkFormal.NearV3.Assembly.ComposeV3

/-!
# ZkFormal.NearV3.Assembly.RenderV3Assemble — helpers for the render composition

v1's `Render/Compose.lean:render_stmt` proves `Holds nearAir` from the per-table
`LocalStmt`/`TrafficStmt` and the per-bus `BusStmt`.  The same composition works
for `nearAirV3`, and this module supplies the two trace-free ingredients:

* `count_sel` — a table's `tableBusCount` equals the count of the messages of its
  `TableTraffic` (v1's `count_sel`);
* `holdsP_of_parts` / `balance_decomp` (`ComposeV3`) and `busCount_nearAirV3`
  (`NearAirBus`) — assembling `HoldsP` from the per-table `TableLocal`s, the
  public fit and the balance, with the `nearAirV3` bus count decomposed over its
  25 tables.

The remaining `render-assembly` work is the concrete `renderV3` trace and the
per-table `TableLocal`/`TableTraffic` pairs (see
`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §3.2).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- Count of a message `m` in a list of NEAR messages. -/
def cnt (l : List ZkFormal.Near.Msg) (m : List Fp) : Nat := (l.map ZkFormal.Near.Msg.toFp).count m

/-- Sends (`s = true`) or receives of a traffic. -/
def sel (s : Bool) (tf : ZkFormal.Near.Traffic) : Nat → List ZkFormal.Near.Msg :=
  if s then tf.sends else tf.recvs

/-- `tableBusCount` of an exact traffic is the count of the selected message list. -/
theorem count_sel {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {tf : ZkFormal.Near.Traffic} (h : ZkFormal.Near.TableTraffic is tr t pub tf)
    (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount is tr t pub b s m = cnt (sel s tf b) m := by
  cases s
  · exact (h b m).2
  · exact (h b m).1

end ZkFormal.NearV3.Assembly

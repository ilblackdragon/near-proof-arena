import ZkFormal.NearV3.Assembly.NearAirBus
import ZkFormal.NearV3.Assembly.ComposeV3

/-!
# ZkFormal.NearV3.Assembly.RenderV3Assemble — the render-composition plumbing

v1's `Render/Compose.lean:render_stmt` proves `Holds nearAir` from the per-table
`LocalStmt`/`TrafficStmt` and the per-bus `BusStmt`.  The same composition works
for `nearAirV3`; the two trace-free ingredients are supplied here:

* `count_sel` — a table's `tableBusCount` equals the count of the messages of its
  `TableTraffic` (v1's `count_sel`);
* `holdsP_of_table_traffic` — assemble `HoldsP nearAirV3` from the per-table
  `TableLocal`s, the per-table `tableBusCount`-decomposed balance, and the public
  fit, via `busCount_nearAirV3` (`NearAirBus`) and `holdsP_of_parts` (`ComposeV3`).

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

/-- **`HoldsP nearAirV3` from per-table obligations.**  The balance is given in the
`nearAirV3`-decomposed (per-table `tableBusCount`) form; `busCount_nearAirV3`
connects it to the AIR's `busCount`.  `count_sel` turns `tableBusCount` into the
count of each table's traffic, so the render package supplies the traffic balance.
-/
theorem holdsP_of_table_traffic {pub : List Fp} {tr : Trace Fp}
    (hL : ∀ (t : Nat) (ht : t < nearAirV3.tables.length),
      ZkFormal.Near.TableLocal nearAirV3.tables[t] tr t pub)
    (hfit : pubFit nearAirV3 pub = true)
    (hbal : ∀ b m,
      (nearTablesFull.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
          tableBusCount T.interactions tr t pub b true m).sum + pubCount nearAirV3 pub b true m =
        (nearTablesFull.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
          tableBusCount T.interactions tr t pub b false m).sum + pubCount nearAirV3 pub b false m) :
    HoldsP nearAirV3 pub tr := by
  refine holdsP_of_parts hL hfit ?_
  intro b m
  rw [busCount_nearAirV3 tr pub b true m, busCount_nearAirV3 tr pub b false m]
  exact hbal b m

end ZkFormal.NearV3.Assembly

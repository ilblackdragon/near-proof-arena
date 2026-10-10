import ZkFormal.NearV3.Assembly.NearAirBus
import ZkFormal.NearV3.Assembly.ComposeV3

/-!
# ZkFormal.NearV3.Assembly.RenderV3Assemble — `HoldsP` from traffic obligations

v1's `Render/Compose.lean:render_stmt` proves `Holds nearAir` from the per-table
`LocalStmt`/`TrafficStmt` and the per-bus `BusStmt`.  This module does the same
for `nearAirV3`: from the per-table `TableLocal`s, the per-table `TableTraffic`s
of a fixed traffic `tf t`, the public fit, and the balance of the *honest
traffic* (trace-free, with the public messages), assemble `HoldsP nearAirV3`.

The two bridges are `count_sel` (a table's `tableBusCount` = count of its
traffic) and `busCount_nearAirV3` (the `nearAirV3` bus count decomposed over the
25 tables).
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

set_option maxHeartbeats 1000000 in
/-- `mapIdx` is congruent when the functions agree at every index. -/
theorem mapIdx_get_congr {α β : Type} {f g : Nat → α → β} :
    ∀ (l : List α), (∀ i (h : i < l.length), f i (l.get ⟨i, h⟩) = g i (l.get ⟨i, h⟩)) →
      List.mapIdx f l = List.mapIdx g l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapIdx_cons, List.mapIdx_cons]
    congr 1
    · exact h 0 (by simp)
    · apply mapIdx_get_congr l
      intro i hi
      have hh := h (i + 1) (by simpa using hi)
      simpa [List.getElem_cons_succ] using hh

set_option maxHeartbeats 1000000 in
/-- The `nearAirV3` table `tableBusCount` sum equals the count of a fixed
per-table traffic. -/
theorem busSum_eq (tr : Trace Fp) (pub : List Fp) (tf : Nat → ZkFormal.Near.Traffic)
    (hT : ∀ t (ht : t < nearAirV3.tables.length),
      ZkFormal.Near.TableTraffic nearAirV3.tables[t].interactions tr t pub (tf t))
    (b : Nat) (s : Bool) (m : List Fp) :
    (nearTablesFull.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
        tableBusCount T.interactions tr t pub b s m).sum =
      (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) =>
        cnt (sel s (tf t) b) m).sum := by
  have hlen : nearTablesFull.length = nearAirV3.tables.length := by rw [nearAirV3_tables]
  have h := mapIdx_get_congr nearTablesFull
    (f := fun (t : Nat) (T : ZkFormal.Air.Table) => tableBusCount T.interactions tr t pub b s m)
    (g := fun (t : Nat) (_ : ZkFormal.Air.Table) => cnt (sel s (tf t) b) m)
    (fun i hi => by
      have hi' : i < nearAirV3.tables.length := by rw [← hlen]; exact hi
      exact count_sel (hT i hi') b s m)
  rw [h]

/-- **`HoldsP nearAirV3` from the per-table render obligations.**  The balance is
the trace-free balance of the per-table honest traffic `tf` with the public
messages (v1's `BusStmt` analogue over the 25 buses). -/
theorem holdsP_of_table_traffic {pub : List Fp} {tr : Trace Fp}
    (tf : Nat → ZkFormal.Near.Traffic)
    (hL : ∀ (t : Nat) (ht : t < nearAirV3.tables.length),
      ZkFormal.Near.TableLocal nearAirV3.tables[t] tr t pub)
    (hT : ∀ (t : Nat) (ht : t < nearAirV3.tables.length),
      ZkFormal.Near.TableTraffic nearAirV3.tables[t].interactions tr t pub (tf t))
    (hfit : pubFit nearAirV3 pub = true)
    (hbal : ∀ b m,
      (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) =>
          cnt (sel true (tf t) b) m).sum + pubCount nearAirV3 pub b true m =
        (nearTablesFull.mapIdx fun (t : Nat) (_ : ZkFormal.Air.Table) =>
          cnt (sel false (tf t) b) m).sum + pubCount nearAirV3 pub b false m) :
    HoldsP nearAirV3 pub tr := by
  refine holdsP_of_parts hL hfit ?_
  intro b m
  rw [busCount_nearAirV3 tr pub b true m, busCount_nearAirV3 tr pub b false m,
    busSum_eq tr pub tf hT b true m, busSum_eq tr pub tf hT b false m]
  exact hbal b m

end ZkFormal.NearV3.Assembly

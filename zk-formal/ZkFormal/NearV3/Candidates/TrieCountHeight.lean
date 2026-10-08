import ZkFormal.NearV3.Candidates.TrieHeight
import ZkFormal.NearV3.Candidates.CountLift
namespace ZkFormal.NearV3.Candidates.TrieCountHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render Rcpt.Candidates.SizeCount

/-- Actual candidate count columns, constructed from the native increment stream. -/
def node (vs : List NodeS3) (pub : List Fp) : Trace Fp :=
  CountLift.trace (TrieHeight.node vs) nodeCount nodeIncrement pub

def value (es : List ValE) (pub : List Fp) : Trace Fp :=
  CountLift.trace (TrieHeight.value es) valCount valIncrement pub

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem node_bounds : NodeV3.tableU.exprs.all (fun e=>decide (e.colBound≤nodeCount))=true ∧
    nodeIncrement.colBound≤nodeCount := by decide +kernel

theorem value_bounds : ValV3.table.exprs.all (fun e=>decide (e.colBound≤valCount))=true ∧
    valIncrement.colBound≤valCount := by decide +kernel

theorem node_local (vs : List NodeS3) (hok : NodeOk vs) (t : Nat) (pub : List Fp) :
    TableLocal nodeTable (node vs pub) t pub := by
  exact CountLift.lift_local (TrieHeight.node_complete vs hok t pub).1
    (by intro e he; exact of_decide_eq_true (List.all_eq_true.mp node_bounds.1 e he)) node_bounds.2

theorem value_local (es : List ValE) (hok : ValOk es) (t : Nat) (pub : List Fp) :
    TableLocal valTable (value es pub) t pub := by
  exact CountLift.lift_local (TrieHeight.value_complete es hok t pub).1
    (by intro e he; exact of_decide_eq_true (List.all_eq_true.mp value_bounds.1 e he)) value_bounds.2

theorem node_log (vs : List NodeS3) (pub : List Fp) (t : Nat) : (node vs pub).log t=22 := rfl

theorem value_log (es : List ValE) (pub : List Fp) (t : Nat) : (value es pub).log t=22 := rfl
end ZkFormal.NearV3.Candidates.TrieCountHeight

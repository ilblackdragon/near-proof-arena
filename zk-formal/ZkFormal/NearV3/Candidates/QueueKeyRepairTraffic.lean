import ZkFormal.NearV3.Candidates.QueueKeyRepairPrefix

namespace ZkFormal.NearV3.Candidates.QueueKeyRepair
open ZkFormal.Near Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra ValueGen

theorem key_silent (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hw : tr.cell t r CombinedTable.walk=0) (hl : tr.cell t r CombinedTable.wl=0) :
    rowTraffic interactions tr t r pub B_KEYNIB true=[] := by
  rw [key_filter]
  simp [keys,interactions,CombinedTable.interactions,rowTraffic,Dsl.send,Dsl.recv,
    Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,Dsl.c,hw,hl]

theorem suffix_silent (ws : List Walk) (vs : List Record) (log j : Nat) (pub : List Fp) :
    rowTraffic interactions (mixedTrace ws vs log) 0 ((ws.flatMap Walk.rows).length+j) pub B_KEYNIB true=[] := by
  apply key_silent
  · rw [mixedTrace_suffix]
    exact recordsCell_high vs j _ (by decide)
  · rw [mixedTrace_suffix]
    exact recordsCell_high vs j _ (by decide)

/-- All physical repaired queue key sends equal native queue request packets;
parser and padding rows are silent, with no provider validity premise. -/
theorem all_keys (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp)
    (hfit : (ws.flatMap Walk.rows).length≤2^log) :
    (List.range (2^log)).flatMap (fun r=>rowTraffic interactions
      (mixedTrace ws vs log) 0 r pub B_KEYNIB true)=(ws.flatMap keyMessages).map Msg.toFp := by
  have he : 2^log=(ws.flatMap Walk.rows).length+(2^log-(ws.flatMap Walk.rows).length) := by omega
  have hrange:=congrArg List.range he
  rw [List.range_add] at hrange
  rw [hrange,List.flatMap_append,List.flatMap_map,prefix_keys]
  simp only [suffix_silent]
  rw [List.flatMap_eq_nil_iff.mpr (fun _ _=>rfl),List.append_nil]

end ZkFormal.NearV3.Candidates.QueueKeyRepair

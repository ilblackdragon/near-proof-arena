import ZkFormal.Prover.Statements
import ZkFormal.Stark.ChunkBound

/-!
# ZkFormal.Prover.BcsChunk — the honest prover's `QUERY`-chunk budget (P4)

`prover_chunk : ProverChunkStmt`.  Every query of `proveTree` outside
`queryAnswers` is a wide-hash half with tag `0x00..0x04`, which `Bcs.chunkDec`
rejects (lane L4c's `ZQ`); `queryAnswers` makes `numChunks` chunk queries.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

theorem mapOC_zq {α β : Type} (f : α → OracleComp hashSpec β) (hf : ∀ a, ZQ (f a)) :
    ∀ l : List α, ZQ (mapOC f l)
  | [] => .pure _
  | a :: as => (hf a).bind fun _ => (mapOC_zq f hf as).bind fun _ => .pure _

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

theorem buildTree_go_zq (o : Oracle F) (n : Nat) :
    ∀ (k : Nat) (below : List Bytes) (acc : List (List Bytes)),
      ZQ (buildTree.go (K := K) o n k below acc)
  | 0, _, _ => .pure _
  | k + 1, below, acc => by
    simp only [buildTree.go]
    exact (mapOC_zq _ (fun _ => WH_zq _ tagNode_ne _) _).bind fun lvl =>
      buildTree_go_zq o n k lvl _

theorem buildTree_zq (o : Oracle F) : ZQ (buildTree (K := K) o) := by
  simp only [buildTree]
  exact (mapOC_zq _ (fun _ => WH_zq _ tagLeaf_ne _) _).bind fun lv => buildTree_go_zq _ _ _ _ _

theorem commitMsg_zq (st : CState F K) (m : List (PartV K (Oracle F))) :
    ZQ (commitMsg st m) := by
  simp only [commitMsg]
  exact (mapOC_zq _ (fun o => buildTree_zq o) _).bind fun _ =>
    (WH_zq _ tagAbs_ne _).bind fun _ => .pure _

theorem commitLoop_zq (pr : IopProver F K) :
    ∀ (ss : List Slot) (st : CState F K), ZQ (commitLoop pr ss st)
  | [], _ => .pure _
  | .msg _ :: ss, st => by
    simp only [commitLoop]
    exact (commitMsg_zq _ _).bind fun st' => commitLoop_zq pr ss st'
  | .chal _ :: ss, st => by
    simp only [commitLoop]
    exact (WH_zq _ tagChal_ne _).bind fun _ => commitLoop_zq pr ss _

end

/-- **(P4)** The honest prover makes at most `numChunks` `QUERY`-chunk queries. -/
theorem prover_chunk : ProverChunkStmt := by
  intro F K _ _ _ _ V pr pub cb
  simp only [proveTree]
  split
  · refine OracleComp.QueryBound.mono (n := 0 + (0 + (V.numChunks + 0))) ?_ (by omega)
    refine ZkFormal.QueryBound.bind (ZQ.toQB (WH_zq _ tagInit_ne _)) fun d0 => ?_
    refine ZkFormal.QueryBound.bind (ZQ.toQB (commitLoop_zq pr _ _)) fun st => ?_
    refine ZkFormal.QueryBound.bind (queryAnswers_chunk _ _) fun answers => ?_
    exact .pure _ _
  · exact .pure _ _

end ZkFormal.Prover

import ZkFormal.NearV3.Candidates.ProcCodecGeneratedTrailer
namespace ZkFormal.NearV3.Candidates.ProcCodecRemainingConstraints
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

def remaining : List Expr :=
  (cKind.filter fun e=>!(ProcPriorCodecActual.retiredKind.contains e)) ++
  (cRec.filter fun e=>!(ProcPriorCodecActual.retiredRec.contains e)) ++
  ProcPriorCodecActual.additions

/-- Trailer, bit, capacity and padding obligations have been discharged from
native generation. This theorem records exactly the active groups still needed. -/
theorem table_of_remaining (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn : R.n≤64)
    (t : Nat) (pub : List Fp)
    (hc : ∀r,r<out.rows.size→∀e∈remaining,
      e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace out.rows codecPad) t pub := by
  apply ProcCodecGeneratedBits.table_of_constraints I R present vid gb fwd out h hn t pub
  intro r hr e he
  simp only [ProcPriorCodecActual.constraints,List.mem_append] at he
  rcases he with ((hk|hrec)|htrl)|hadd
  · exact hc r hr e (List.mem_append_left _ (List.mem_append_left _ hk))
  · exact hc r hr e (List.mem_append_left _ (List.mem_append_right _ hrec))
  · exact ProcCodecGeneratedTrailer.active I R present vid gb fwd out h r hr e htrl
  · exact hc r hr e (List.mem_append_right _ hadd)
end ZkFormal.NearV3.Candidates.ProcCodecRemainingConstraints

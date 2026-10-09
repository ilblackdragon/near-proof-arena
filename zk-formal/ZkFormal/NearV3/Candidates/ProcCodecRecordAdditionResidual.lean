import ZkFormal.NearV3.Candidates.ProcCodecRemainingConstraints
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedFullKind
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordAdditionResidual
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

def remaining : List Expr :=
  (cRec.filter fun e=>!(ProcPriorCodecActual.retiredRec.contains e)) ++ ProcPriorCodecActual.additions

theorem table_of_remaining (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hparam : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn1 : 0<R.n) (hn : R.n≤64) (ht : R.tau<P) (t : Nat) (pub : List Fp)
    (hc : ∀r,r<out.rows.size→∀e∈remaining,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace out.rows codecPad) t pub := by
  apply ProcCodecRemainingConstraints.table_of_remaining I R present vid gb fwd out h hn t pub
  intro r hr e he
  simp only [ProcCodecRemainingConstraints.remaining,List.mem_append] at he
  rcases he with (hk|hrec)|hadd
  · exact ProcCodecGeneratedFullKind.active I R present vid gb fwd out h hparam hn1 hn ht r hr e hk
  · exact hc r hr e (List.mem_append_left _ hrec)
  · exact hc r hr e (List.mem_append_right _ hadd)
end ZkFormal.NearV3.Candidates.ProcCodecRecordAdditionResidual

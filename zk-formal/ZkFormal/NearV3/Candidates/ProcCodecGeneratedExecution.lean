import ZkFormal.NearV3.Candidates.ProcCodecExecutionTrace
import ZkFormal.NearV3.Assembly.SchedulerCodecPlacement
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedExecution
open ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h : x >>= f = .ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

/-- Exact record-loop state and execution are preserved alongside physical
header/hash placement, ready for local-row arithmetic proofs. -/
theorem core_execution (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : coreLayout I R present vid gb fwd=.ok out) :
    ∃mid : RecordState,
      forIn (List.range (R.n*R.n)) ((headerRows I R present vid).toArray,[])
        (blockStep I R present vid gb fwd)=.ok mid ∧
      out.rows.toList=mid.1.toList++hashRows I R present vid++ashRows I R present vid := by
  unfold coreLayout at h
  dsimp only at h
  simp only [pure,Except.pure] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  obtain ⟨mid,hloop,h⟩ := bind_ok h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  cases h
  refine ⟨mid,hloop,?_⟩
  simp [hashRows,ashRows,ProcPriorCodecNativeHash.instanceCells]

theorem generated_execution (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) :
    ∃mid : RecordState,
      ProcCodecExecutionTrace.Steps (blockStep I R present vid gb fwd) (List.range (R.n*R.n))
        ((headerRows I R present vid).toArray,[]) mid ∧
      out.rows.toList=mid.1.toList++hashRows I R present vid++ashRows I R present vid := by
  rw [←coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc,Except.map] at h
  | ok o =>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    obtain ⟨mid,hm,hr⟩ := core_execution I R present vid gb fwd o hc
    exact ⟨mid,ProcCodecExecutionTrace.blocks_execution I R present vid gb fwd _ mid hm,hr⟩
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedExecution

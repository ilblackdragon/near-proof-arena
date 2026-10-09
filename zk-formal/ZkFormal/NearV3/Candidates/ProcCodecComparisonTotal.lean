import ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedExecution
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecComparisonCost

theorem field_cost (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (st : RecordState) (out : ForInStep RecordState)
    (h:fieldStep I R present vid gb fwd k f st=.ok out) :
    ∃s,out=.yield s ∧ s.2.length≤st.2.length+2 := by
  unfold fieldStep at h
  cases he:forIn (List.range 8) (st.1,st.2,0,0,0,0)
    (fun g s=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g s) with
  | error e=>simp only [he,bind,Except.bind] at h;cases h
  | ok s=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst out
    exact ⟨_,rfl,phase_cost I R present gb fwd _ k f _ s he⟩

theorem block_cost (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k : Nat) (st : RecordState) (out : ForInStep RecordState)
    (h:blockStep I R present vid gb fwd k st=.ok out) :
    ∃s,out=.yield s ∧ s.2.length≤st.2.length+6 := by
  unfold blockStep at h
  cases he:forIn (List.range 3) st (fieldStep I R present vid gb fwd k) with
  | error e=>simp only [he,bind,Except.bind] at h;cases h
  | ok s=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst out
    refine ⟨_,rfl,?_⟩
    have hh:=loop_cost (List.range 3) (fieldStep I R present vid gb fwd k)
      (fun s:RecordState=>s.2.length) (fun _=>2)
      (fun f _ s o=>field_cost I R present vid gb fwd k f s o) st s he
    have hc:((List.range 3).map (fun _=>2)).sum=6:=by decide +kernel
    simpa only [hc] using hh

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem core_cost (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:coreLayout I R present vid gb fwd=.ok out) : out.cmps.length≤6*(R.n*R.n) := by
  unfold coreLayout at h
  dsimp only at h
  simp only [pure,Except.pure] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  obtain ⟨mid,hloop,h⟩:=bind_ok h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  rw [push_loop] at h
  simp only [bind,Except.bind] at h
  cases h
  have hh:=loop_cost (List.range (R.n*R.n)) (blockStep I R present vid gb fwd)
    (fun s:RecordState=>s.2.length) (fun _=>6)
    (fun k _ s o=>block_cost I R present vid gb fwd k s o) _ mid hloop
  simpa [List.map_const',List.sum_replicate_nat,Nat.mul_comm] using hh

theorem generated_cost (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) :
    out.cmps.length≤6*(R.n*R.n) := by
  rw [←coreLayout_eq] at h
  cases hc:coreLayout I R present vid gb fwd with
  | error e=>simp [hc,Except.map] at h
  | ok o=>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core_cost I R present vid gb fwd o hc
end ZkFormal.NearV3.Candidates.ProcCodecComparisonTotal

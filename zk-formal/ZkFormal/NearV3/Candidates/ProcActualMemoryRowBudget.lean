import ZkFormal.NearV3.Candidates.ProcActualRunComparisonInventory
import ZkFormal.NearV3.Candidates.MemConcatCells
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryRowBudget
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem ops (os : List Gen.MOp) (tp : Nat) : os.length≤(ProcActualMemoryComparisonInventory.requests tp os).length := by
  induction os generalizing tp with
  | nil=>simp [ProcActualMemoryComparisonInventory.requests]
  | cons o os ih=>
    simp only [ProcActualMemoryComparisonInventory.requests,List.length_append,List.length_cons]
    have hh:=ih o.t
    simp [ProcActualMemoryComparisonInventory.opRequests]
    split <;> omega

theorem records (gs : List Gen.Seg) : (memVs gs).length≤gs.length+
    (gs.flatMap (fun g=>ProcActualMemoryComparisonInventory.requests 0 g.ops)).length := by
  induction gs with
  | nil=>simp [memVs]
  | cons g gs ih=>
    have hh:=ops g.ops 0
    simp only [memVs,List.flatMap_cons,List.length_append,segVs_length,List.length_cons] at *
    omega

theorem append (f : Nat→Gen.Seg) (xs : List Nat) (gs out : Array Gen.Seg)
    (h:forIn xs gs (ProcActualSegments.appendStep f)=.ok out) : out.size=gs.size+xs.length := by
  induction xs generalizing gs with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp
  | cons i xs ih=>
    simp only [List.forIn_cons,ProcActualSegments.appendStep,bind,Except.bind] at h
    have hh:=ih (gs.push (f i)) h
    simp only [Array.size_push,List.length_cons] at *
    omega

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem build (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (out : Array Gen.Seg)
    (h:ProcActualSegments.build I tau s=.ok out) : out.size=I.ids.length*I.ids.length+2*I.ids.length := by
  unfold ProcActualSegments.build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  obtain ⟨b,hb,h⟩:=bind_ok h
  have h1:=append _ _ _ a ha
  have h2:=append _ _ a b hb
  have h3:=append _ _ b out h
  simp only [Array.size_empty,List.length_range] at h1 h2 h3
  omega

theorem run_segments (I : Input) (tau : Nat) (R : Run) (h:ActualRun.run I tau=.ok R) :
    R.segs.length=I.ids.length*I.ids.length+2*I.ids.length := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,_,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,_,h⟩:=bind_ok h
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,_,h⟩:=bind_ok h
  have hg:=build I tau s gs hgs
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,_,h⟩:=bind_ok h
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  exact hg

theorem run (I : Input) (tau : Nat) (R : Run) (h:ActualRun.run I tau=.ok R)
    (hn:I.ids.length≤64) (hc:R.cmps.length≤62976) : (Gen.Mem.rows R).size≤67200 := by
  have hrel:=MemNativeCells.rows R
  have hl:(Gen.Mem.rows R).size=(memVs R.segs).length:=by simpa only [Array.length_toList] using hrel.length
  have hr:=records R.segs
  have hs:=run_segments I tau R h
  have he:=congrArg List.length (ProcActualRunComparisonInventory.run I tau R h)
  simp only [List.length_append] at he
  have hmul:I.ids.length*I.ids.length≤4096:=Nat.mul_le_mul hn hn
  omega
end ZkFormal.NearV3.Candidates.ProcActualMemoryRowBudget

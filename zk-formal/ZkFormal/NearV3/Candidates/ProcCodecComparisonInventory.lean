import ZkFormal.NearV3.Candidates.ProcCodecComparisonConservationLoops
import ZkFormal.NearV3.Candidates.ProcCodecComparisonSides
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonInventory
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Assembly.CodecDigest

def traffic (rows : List (Array Nat)) := rows.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row B_SCMP true)

theorem headers (I : Input) (R : Run) (present : Bool) (vid : Nat) :
    traffic (headerRows I R present vid)=[] := by
  unfold traffic headerRows
  rw [List.flatMap_eq_nil_iff]
  intro row hm
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
  exact ProcCodecComparisonSides.quiet _ (ProcCodecComparisonSides.header I R present vid i _ _)

theorem hashes (I : Input) (R : Run) (present : Bool) (vid : Nat) :
    traffic (hashRows I R present vid)=[] := by
  unfold traffic hashRows
  rw [List.flatMap_eq_nil_iff]
  intro row hm
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
  exact ProcCodecComparisonSides.quiet _ (ProcCodecComparisonSides.hash I R present vid _ i _ _)

theorem ashes (I : Input) (R : Run) (present : Bool) (vid : Nat) :
    traffic (ashRows I R present vid)=[] := by
  unfold traffic ashRows
  rw [List.flatMap_eq_nil_iff]
  intro row hm
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
  exact ProcCodecComparisonSides.quiet _ (ProcCodecComparisonSides.ash I R present vid _ i)

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem core (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:coreLayout I R present vid gb fwd=.ok out) : traffic out.rows.toList=out.cmps.map cmpMsg := by
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
  have hh:ProcCodecComparisonConservationLoops.Good mid :=
    ExceptLoop.invariant _ _ ProcCodecComparisonConservationLoops.Good
      (fun k _ s hs u hu=>ProcCodecComparisonConservationLoops.block I R present vid gb fwd k s u hs hu)
      _ mid (by change traffic (headerRows I R present vid)=[]; exact headers I R present vid) hloop
  have hf:traffic (mid.1.toList++hashRows I R present vid++ashRows I R present vid)=mid.2.map cmpMsg := by
    unfold traffic
    rw [List.flatMap_append,List.flatMap_append]
    change traffic mid.1.toList ++ traffic (hashRows I R present vid) ++ traffic (ashRows I R present vid)=mid.2.map cmpMsg
    rw [hashes,ashes,List.append_nil,List.append_nil]
    exact hh
  simpa only [traffic,List.toList_toArray,Array.toList_append,hashRows,ashRows,
    ProcPriorCodecNativeHash.instanceCells] using hf

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) : traffic out.rows.toList=out.cmps.map cmpMsg := by
  rw [←coreLayout_eq] at h
  cases hc:coreLayout I R present vid gb fwd with
  | error e=>simp [hc,Except.map] at h
  | ok o=>
    simp only [hc,Except.map,Except.ok.injEq] at h
    subst out
    exact core I R present vid gb fwd o hc
end ZkFormal.NearV3.Candidates.ProcCodecComparisonInventory

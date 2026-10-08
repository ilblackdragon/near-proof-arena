import ZkFormal.NearV3.Assembly.RcptSkeletonControl

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def advance (row : Coord) : Coord := {row with index:=row.index+1}

theorem control_continuation (row : Coord) (hs : row.state∈states)
    (hi : row.index+1<row.length) (pub : List Fp) :
    ∀e∈continuationConstraints,e.eval (controlPair row (advance row)) 0 0 pub=0 := by
  have hf : row.index+1≠row.length := by omega
  have hi0 : row.index+1≠0 := by omega
  intro e he
  simp only [continuationConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (he|he|he)|he
  · subst e
    rw [eval_sub,control_onehot row (advance row) hs pub]
    change (1:Fp)-1=0
    grind only
  · subst e
    simp only [eval_mul3,eval_c,eval_not,eval_sub,eval_n,eval_add,eval_k]
    simp only [controlPair,Trace.height,Nat.reducePow,Nat.reduceAdd,Nat.reduceMod,show ¬(1=0) by decide,↓reduceIte,
      controlCell,advance,idx,act,fe,fs,↓reduceIte]
    have hcast : Fp.ofNat (row.index+1)=Fp.ofNat row.index+1 := by
      change ((row.index+1:Nat):Fp)=(row.index:Fp)+1
      grind only
    rw [hcast]
    grind only
  · subst e
    simp only [eval_mul3,eval_c,eval_not,eval_n]
    simp only [controlPair,Trace.height,Nat.reducePow,Nat.reduceAdd,Nat.reduceMod,show ¬(1=0) by decide,↓reduceIte,
      controlCell,advance,idx,act,fe,fs,↓reduceIte,if_neg hi0]
    grind only
  · obtain ⟨s,hsm,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul3,eval_c,eval_not,eval_sub,eval_n]
    simp only [controlPair,Trace.height,Nat.reducePow,Nat.reduceAdd,Nat.reduceMod,show ¬(1=0) by decide,↓reduceIte]
    rw [control_state row hsm,control_state (advance row) hsm]
    change _*_*((if s=row.state then (1:Fp) else 0)-(if s=row.state then 1 else 0))=0
    grind only

theorem segment_get (s len i : Nat) (hi : i<len) :
    (segment s len)[i]?=some ⟨s,i,len⟩ := by
  simp [segment,hi]

/-- Consecutive generated rows of one segment use exactly the checked advancing
control pair, so no adjacency witness is supplied by the prover. -/
theorem segment_adjacent {s len i : Nat} (hs : s∈states) (hi : i+1<len) (pub : List Fp) :
    ∃row next,(segment s len)[i]?=some row ∧ (segment s len)[i+1]?=some next ∧
      ∀e∈continuationConstraints,e.eval (controlPair row next) 0 0 pub=0 := by
  refine ⟨⟨s,i,len⟩,⟨s,i+1,len⟩,segment_get s len i (by omega),segment_get s len (i+1) hi,?_⟩
  exact control_continuation ⟨s,i,len⟩ hs hi pub

end ZkFormal.NearV3.Assembly.RcptSkeleton

import ZkFormal.NearV3.Candidates.HorizontalTrace

namespace ZkFormal.NearV3.Candidates.HorizontalJoin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace

/-- Two adjacent column blocks, with both component clocks at the same height. -/
def pair (A B : Air.Table) : Air.Table :=
  {width:=A.width+B.width, maxLog:=max A.maxLog B.maxLog,
   constraints:=A.constraints++(shifted A.width B).constraints,
   interactions:=A.interactions++(shifted A.width B).interactions}

theorem join_local {A B : Air.Table} {a b : Trace Fp} {t : Nat} {pub : List Fp}
    (ha : TableLocal A a t pub) (hb : TableLocal B b t pub)
    (height : a.log t=b.log t)
    (bounds : ∀ e∈A.exprs, e.colBound≤A.width) :
    TableLocal (pair A B) (join A.width a b) t pub := by
  refine ⟨ha.log_ge,?_,?_,?_⟩
  · exact Nat.le_trans ha.log_le (Nat.le_max_left _ _)
  · intro r hr e he
    rcases List.mem_append.mp he with he | he
    · rw [join_left_eval _ _ _ _ _ _ _ (bounds e (List.mem_append_left _ he))]
      exact ha.constr r hr e he
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      rw [join_right_eval _ _ _ _ _ _ height]
      apply hb.constr r _ f hf
      simpa only [Trace.height,join,height] using hr
  · intro r hr i hi v hv
    rcases List.mem_append.mp hi with hi | hi
    · have bound : v.colBound≤A.width := bounds v (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ hv⟩))
      rw [join_left_eval _ _ _ _ _ _ _ bound]
      exact ha.bits r hr i hi v hv
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
      rw [join_right_eval _ _ _ _ _ _ height]
      apply hb.bits r _ j hj w hw
      simpa only [Trace.height,join,height] using hr
end ZkFormal.NearV3.Candidates.HorizontalJoin

import ZkFormal.NearV3.Candidates.ProcPriorIdOrder
namespace ZkFormal.NearV3.Candidates.ProcPriorIdValue
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler ProcPriorIds

theorem index_from_records (ids : List Nat) (key start : Nat) :
    indexOf.go key ids start = ((ids.zipIdx start).find? fun x=>x.1==key).map Prod.snd := by
  induction ids generalizing start with
  | nil => rfl
  | cons id ids ih =>
    by_cases h:id=key
    · simp [indexOf.go,List.zipIdx_cons,h]
    · simp [indexOf.go,List.zipIdx_cons,h,ih]

theorem first_public (ids : List Nat) (key : Nat) :
    ((publicEvents ids).filter fun e=>e.key==key).head?.map (·.ordinal)=indexOf ids key := by
  rw [indexOf,index_from_records]
  simp only [publicEvents,List.filter_map,List.head?_map,List.head?_filter,Option.map_map]
  congr 1

/-- The query's result is precisely the first public index in its ID group;
unknown IDs use none, with no fabricated public record. -/
theorem query_first_public (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈requestEvents ids rs) :
    e.result=((publicEvents ids).filter fun p=>p.key==e.key).head?.map (·.ordinal) := by
  obtain ⟨_,_,_,_,hr,_⟩:=request_source ids rs e h
  rw [hr,first_public]

end ZkFormal.NearV3.Candidates.ProcPriorIdValue

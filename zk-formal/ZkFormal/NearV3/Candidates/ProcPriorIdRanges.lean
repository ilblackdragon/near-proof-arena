import ZkFormal.NearV3.Candidates.ProcPriorIdLimbs
import ZkFormal.NearV3.Candidates.ProcPriorIdRows
namespace ZkFormal.NearV3.Candidates.ProcPriorIdRanges
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched ProcPriorIds

theorem event_key (ids : List Nat) (rs : List LinkAllowance)
    (hi:∀id∈ids,id<2^64) (hr:∀r∈rs,LinkOk r) (e : Event) (he:e∈events ids rs) : e.key<2^64 := by
  rcases List.mem_append.mp ((events_perm ids rs).mem_iff.mp he) with hp|hq
  · exact hi e.key (List.mem_of_getElem? (public_source ids e hp).1)
  · obtain ⟨r,j,hj,_,_,hs|hs⟩:=request_source ids rs e hq
    · rw [hs.1]; exact (hr r (List.mem_of_getElem? hj)).1
    · rw [hs.1]; exact (hr r (List.mem_of_getElem? hj)).2.1

theorem event_ordinal (ids : List Nat) (rs : List LinkAllowance) (e : Event) (he:e∈events ids rs) :
    e.ordinal<ids.length+2*rs.length := by
  rcases List.mem_append.mp ((events_perm ids rs).mem_iff.mp he) with hp|hq
  · have hn:=(List.getElem?_eq_some_iff.mp (public_source ids e hp).1).1
    omega
  · obtain ⟨r,j,hj,_,_,hs|hs⟩:=request_source ids rs e hq
    all_goals have hn:=(List.getElem?_eq_some_iff.mp hj).1
    all_goals omega

theorem decoded_ranges (ids : List Nat) (bytes : Bytes) (st : State)
    (hd:State.decode bytes=some st) (hi:∀id∈ids,id<2^64) (hn:ids.length≤64)
    (hb:bytes.length≤2000000) (e : Event) (he:e∈events ids st.links) :
    ProcPriorIdLimbs.lo e.key<16777216 ∧ ProcPriorIdLimbs.mid e.key<16777216 ∧
    ProcPriorIdLimbs.hi e.key<65536 ∧ e.ordinal<16777216 := by
  have hk:=event_key ids st.links hi (ProcPriorDecode.decode_exact bytes st hd).2.1 e he
  obtain ⟨hl,hm,hh⟩:=ProcPriorIdLimbs.bounds e.key hk
  have ho:=event_ordinal ids st.links e he
  have hc:=ProcPriorDecode.decode_length bytes st hd
  exact ⟨hl,hm,hh,by omega⟩

end ZkFormal.NearV3.Candidates.ProcPriorIdRanges

import ZkFormal.NearV3.Candidates.ProcDistGridBridge
namespace ZkFormal.NearV3.Candidates.ProcDistGeneratorSuccess
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistGeneratorFactor ProcDistGridBridge ProcDistEventRow

theorem outer (I:Input)(R:Run) (hnd:(receivers I R).Nodup) :
    ∀(ss:List Nat)(ri:Array Endpoint)(g:Array Nat),
      (∀s∈ss,cntS R.n I.allowed s=((receivers I R).filter (fun r=>I.allowed[s*R.n+r]!)).length) →
      (∀r∈receivers I R,(ri[r]!).1=(ss.filter (fun s=>I.allowed[s*R.n+r]!)).length) →
      ∃out,eventOuter I R ss (ri,g)=.ok out
  | [],ri,g,_,_=>⟨(ri,g),rfl⟩
  | s::ss,ri,g,hcs,hri=>by
    have hp:∀r∈receivers I R,I.allowed[s*R.n+r]! = true →1≤(ri[r]!).1 := by
      intro r hr ha
      rw [hri r hr]
      simp [ha]
    have he:=row_eq_grid R.n I.allowed s (receivers I R) ri g
      (cntS R.n I.allowed s,R.fin.sb[s]!) hnd (hcs s (by simp)) hp
    let out:=grid R.n I.allowed s (receivers I R) (ri,g,(cntS R.n I.allowed s,R.fin.sb[s]!))
    have hi:∀r∈receivers I R,(out.1[r]!).1=(ss.filter (fun s=>I.allowed[s*R.n+r]!)).length := by
      intro r hr
      rw [grid_receiver_count R.n I.allowed s (receivers I R) _ ri g hnd r,hri r hr]
      cases ha:I.allowed[s*R.n+r]! <;> simp [hr,ha]
    obtain ⟨last,hl⟩:=outer I R hnd ss out.1 out.2.1 (fun s hs=>hcs s (by simp [hs])) hi
    exact ⟨last,by simpa only [eventOuter,List.forIn_cons,eventStep,he,bind,Except.bind,pure,Except.pure] using hl⟩

theorem grid_success (I:Input)(R:Run)(rows:Array (Array Nat))(cmps:List Cmp) :
    ∃out,forIn (List.range R.n)
      (rows,cmps,Array.replicate (R.n*R.n) 0,
        (List.range R.n).toArray.map (fun r=>(cntR R.n I.allowed r,R.fin.rb[r]!)))
      (gridStep I R)=.ok out := by
  have hsp:(senders I R).Perm (List.range R.n):=sortByKey_perm _ _
  have hrp:(receivers I R).Perm (List.range R.n):=sortByKey_perm _ _
  have hc:∀s∈senders I R,cntS R.n I.allowed s=((receivers I R).filter (fun r=>I.allowed[s*R.n+r]!)).length := by
    intro s hs
    exact (filter_length_perm _ hrp).symm
  have hi:∀r∈receivers I R,
      (((List.range R.n).toArray.map (fun r=>(cntR R.n I.allowed r,R.fin.rb[r]!)))[r]!).1=
        ((senders I R).filter (fun s=>I.allowed[s*R.n+r]!)).length := by
    intro r hr
    have hlt:=List.mem_range.mp (hrp.mem_iff.mp hr)
    rw [List.map_toArray,getElem!_toArray_map_range R.n _ hlt]
    exact (filter_length_perm _ hsp).symm
  obtain ⟨e,he⟩:=outer I R (hrp.nodup_iff.2 List.nodup_range) (senders I R) _
    (Array.replicate (R.n*R.n) 0) hc hi
  obtain ⟨out,ho,_⟩:=ProcDistGridBridge.loop I R (List.range R.n)
    (rows,cmps,Array.replicate (R.n*R.n) 0,
      (List.range R.n).toArray.map (fun r=>(cntR R.n I.allowed r,R.fin.rb[r]!))) e
    (by simpa only [sender_list,event] using he)
  exact ⟨out,ho⟩

theorem generated (I:Input)(R:Run)(hn:R.n≤64) : ∃d,distRows I R=.ok d := by
  obtain ⟨a,ha⟩:=ProcDistShardSuccess.side I R 0 (#[],[]) hn
  obtain ⟨b,hb⟩:=ProcDistShardSuccess.side I R 1 a hn
  obtain ⟨g,hg⟩:=grid_success I R b.1 b.2
  rw [native_eq]
  refine ⟨⟨g.1,g.2.2.1,g.2.1⟩,?_⟩
  simp only [build,List.forIn_cons,List.forIn_nil,ha,hb,bind,Except.bind,pure,Except.pure,hg]
end ZkFormal.NearV3.Candidates.ProcDistGeneratorSuccess

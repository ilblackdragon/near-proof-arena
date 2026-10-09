import ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
import ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
namespace ZkFormal.NearV3.Candidates.ProcActualComparisonCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcCodecComparisonCost
abbrev Cmps := ProcActualMemoryScan.Cmps
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem memory_step (o:Gen.MOp)(s:Cmps×Nat)(out:ForInStep (Cmps×Nat))
    (h:ProcActualMemoryScan.actualStep o s=.ok out) :
    ∃u,out=.yield u ∧ u.1.size≤s.1.size+2 := by
  unfold ProcActualMemoryScan.actualStep at h
  obtain ⟨_,_,h⟩:=bind_ok h
  simp only [pure,Except.pure] at h
  split at h <;> refine ⟨_,(Except.ok.inj h).symm,?_⟩ <;> simp

theorem memory_segment (g:Gen.Seg)(cs:Cmps)(out:ForInStep Cmps)
    (h:ProcActualMemoryScan.segmentStep g cs=.ok out) :
    ∃u,out=.yield u ∧ u.size≤cs.size+2*g.ops.length := by
  rw [ProcActualMemoryScan.segment_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  refine ⟨_,rfl,?_⟩
  have hc:=loop_cost _ _ (fun s:Cmps×Nat=>s.1.size) (fun _=>2)
    (fun o _ s u=>memory_step o s u) _ _ hs
  simpa [List.map_const',List.sum_replicate_nat,Nat.mul_comm] using hc

theorem memory_list (gs:List Gen.Seg)(cs out:Cmps)
    (h:forIn gs cs ProcActualMemoryScan.segmentStep=.ok out) :
    out.size≤cs.size+2*(gs.map (fun g=>g.ops.length)).sum := by
  have hc:=loop_cost _ _ (fun s:Cmps=>s.size) (fun g:Gen.Seg=>2*g.ops.length)
    (fun g _ s u=>memory_segment g s u) _ _ h
  have he : (gs.map (fun g=>2*g.ops.length)).sum=2*(gs.map (fun g=>g.ops.length)).sum := by
    clear h hc
    induction gs with
    | nil=>simp
    | cons g gs ih=>simp [ih,Nat.mul_add]
  simpa only [he] using hc

theorem bucket_step (rd:Gen.RoundD)(i:Nat)(cs:Cmps)(out:ForInStep Cmps)
    (h:ProcActualBucketComparisons.step rd i cs=.ok out) :
    ∃u,out=.yield u ∧ u.size≤cs.size+1 := by
  unfold ProcActualBucketComparisons.step at h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok h
  exact ⟨_,(Except.ok.inj h).symm,by simp⟩

theorem round_step (rd:Gen.RoundD)(cs:Cmps)(out:ForInStep Cmps)
    (h:ProcActualComparisonFactor.roundStep rd cs=.ok out) :
    ∃u,out=.yield u ∧ u.size≤cs.size+1+rd.entries.length := by
  unfold ProcActualComparisonFactor.roundStep at h
  split at h
  · obtain ⟨_,_,h⟩:=bind_ok h
    obtain ⟨s,hs,h⟩:=bind_ok h
    refine ⟨s,(Except.ok.inj h).symm,?_⟩
    have hc:=loop_cost _ _ (fun s:Cmps=>s.size) (fun _=>1)
      (fun i _ s u=>bucket_step rd i s u) _ _ hs
    simpa [List.map_const',List.sum_replicate_nat] using hc
  · obtain ⟨s,hs,h⟩:=bind_ok h
    refine ⟨s,(Except.ok.inj h).symm,?_⟩
    have hc:=loop_cost _ _ (fun s:Cmps=>s.size) (fun _=>1)
      (fun i _ s u=>bucket_step rd i s u) _ _ hs
    simp only [List.map_const',List.length_range,List.size_toArray,List.sum_replicate_nat,Nat.mul_one] at hc
    omega

theorem rounds (rs:List Gen.RoundD)(cs out:Cmps)
    (h:forIn rs cs ProcActualComparisonFactor.roundStep=.ok out) :
    out.size≤cs.size+rs.length+(rs.map (fun r=>r.entries.length)).sum := by
  have hc:=loop_cost _ _ (fun s:Cmps=>s.size) (fun r:Gen.RoundD=>1+r.entries.length)
    (fun r _ s u h=>by
      obtain ⟨v,hv,hb⟩:=round_step r s u h
      exact ⟨v,hv,by omega⟩) _ _ h
  have he : (rs.map (fun r=>1+r.entries.length)).sum=rs.length+(rs.map (fun r=>r.entries.length)).sum := by
    clear h hc
    induction rs with
    | nil=>simp
    | cons r rs ih=>simp only [List.map_cons,List.sum_cons,List.length_cons];omega
  rw [he] at hc
  omega
end ZkFormal.NearV3.Candidates.ProcActualComparisonCost

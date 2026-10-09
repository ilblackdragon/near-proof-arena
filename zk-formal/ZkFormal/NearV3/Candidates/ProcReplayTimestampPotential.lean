import ZkFormal.NearV3.Candidates.ProcModelPointers
import ZkFormal.NearV3.Candidates.ProcModelClock
namespace ZkFormal.NearV3.Candidates.ProcReplayTimestampPotential
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers

def weight (v : Nat) : Nat := 64-v%64
def charge (ps : List Push) : Nat := (ps.map (fun p=>weight p.v)).sum

theorem weight_pos (v : Nat) : 0<weight v := by unfold weight; omega

theorem next_weight (reqs : List Req) (v : Nat) (hs:Small reqs) (hv:Valid reqs v)
    (hn:(v%64+1==reqs.toArray[v/64]!.incs.length)=false) : weight (v+1)+1=weight v := by
  have hh:=next_valid reqs v hs hv hn
  have hm:reqs.toArray[v/64]!∈reqs := by
    rw [getElem!_pos reqs.toArray (v/64) (by simpa using hv.1)]
    exact List.mem_iff_getElem.mpr ⟨v/64,hv.1,by simp⟩
  have hb:=hs _ hm
  have hne:v%64+1≠reqs.toArray[v/64]!.incs.length := by simpa using hn
  have hmod:(v+1)%64=v%64+1 := by have:=hv.2; omega
  simp only [weight,hmod]
  omega

/-- Each model entry pays for its timestamp increment from the consumed pointer. -/
theorem entry_charge (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (hs:Small reqs) (hv:Valid reqs v)
    (h:ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ∃next,out=.yield next ∧ charge next.1+next.2.2.1≤charge s.1+s.2.2.1+weight v := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals refine ⟨_,rfl,?_⟩
  all_goals simp only [charge,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
  all_goals first
    | have hp:=weight_pos v; omega
    | have hn:(v%64+1==reqs.toArray[v/64]!.incs.length)=false := by
        simp_all only [Bool.and_eq_true,Bool.not_eq_true']
      have hw:=next_weight reqs v hs hv hn
      omega
theorem entries_charge (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs:Small reqs) (hv:∀v∈vs,Valid reqs v)
    (h:forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    charge out.1+out.2.2.1≤charge s.1+s.2.2.1+(vs.map weight).sum := by
  induction vs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons v vs ih =>
    rw [List.forIn_cons] at h
    cases he:ProcModelStep.entryStep n allowed reqs K z v s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,hc⟩:=entry_charge n allowed reqs K z v s next hs (hv v (by simp)) he
      simp only [he,bind,Except.bind] at h
      have hh:=ih next (fun x hx=>hv x (by simp [hx])) h
      simp only [List.map_cons,List.sum_cons]
      omega

end ZkFormal.NearV3.Candidates.ProcReplayTimestampPotential

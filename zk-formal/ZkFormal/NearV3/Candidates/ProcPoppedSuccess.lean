import ZkFormal.NearV3.Candidates.ProcInitialLinks
namespace ZkFormal.NearV3.Candidates.ProcPoppedSuccess
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcPendingCurrent ProcRequestPointers

def GoodRequests (reqs : List Req) : Prop :=
  ∀q∈reqs,q.incs.length<64 ∧ ∀inc∈q.incs,0<inc

theorem valid_increase (reqs : List Req) (hr : GoodRequests reqs) (v : Nat) (hv : Valid reqs v) :
    v%64+1<64 ∧ 0<reqs.toArray[v/64]!.incs.getD (v%64) 0 := by
  have hm : reqs.toArray[v/64]!∈reqs := by
    rw [getElem!_pos reqs.toArray (v/64) (by simpa using hv.1)]
    exact List.mem_iff_getElem.mpr ⟨v/64,hv.1,by simp⟩
  have hh := hr _ hm
  refine ⟨by have := hv.2; omega,?_⟩
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hv.2,Option.getD_some]
  exact hh.2 _ (List.getElem_mem hv.2)

/-- Given a successful native shuffle, the entire selected model bucket is
constructively executable from ordinary pending invariants. -/
theorem popped_success (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hr : GoodRequests reqs) (ps : List Push) (st : PState) (K z t : Nat)
    (hc : Current reqs st.al ps)
    (hd : (ps.map (fun p=>link reqs p.v)).Nodup)
    (hv : ∀p∈ps,Valid reqs p.v) (sh : List Nat) (rng : NearSpecV3.Rng)
    (hsh : NearSpecV3.shuffle ((sortTs (ps.filter (fun p=>p.key==K))).map (·.v)) st.rng=some (sh,rng)) :
    ∃out,forIn sh (ps.filter (fun p=>p.key != K),{st with rng:=rng},t,[])
      (ProcModelStep.entryStep n allowed reqs K z)=.ok out ∧
      Current reqs out.2.1.al out.1 ∧ (out.1.map (fun p=>link reqs p.v)).Nodup := by
  have hmem : ∀v∈sh,∃p∈ps,p.v=v ∧ p.key=K := by
    intro v hv
    have hm := (shuffle_perm hsh).mem_iff.mp hv
    obtain ⟨p,hp,hpv⟩ := List.mem_map.mp hm
    have hp' := (ProcPushPerm.sort_perm _).mem_iff.mp hp
    exact ⟨p,(List.mem_filter.mp hp').1,hpv,by simpa using (List.mem_filter.mp hp').2⟩
  have hvalid : ∀v∈sh,Valid reqs v := by
    intro v hm
    obtain ⟨p,hp,rfl,hk⟩ := hmem v hm
    exact hv p hp
  have hsel : ProcBatchSuccess.Selected reqs st.al K sh := by
    intro v hm
    obtain ⟨p,hp,rfl,hk⟩ := hmem v hm
    have hh := hc p hp
    exact ⟨hh.1,hh.2.symm.trans hk⟩
  have hperm := (List.Perm.refl ((ps.filter (fun p=>p.key != K)).map (fun p=>link reqs p.v))).append
    ((shuffle_perm hsh).map (link reqs))
  have hpop := (ProcPushPerm.pop_perm ps K).map (fun p=>link reqs p.v)
  simp only [List.map_append,List.map_map,Function.comp_def] at hperm hpop
  have hnd : (ProcLiveLinks.live reqs (ps.filter (fun p=>p.key != K)) sh).Nodup :=
    (hperm.trans hpop).nodup_iff.mpr hd
  obtain ⟨out,ho,hc',hd'⟩ := ProcBatchSuccess.entries_success n allowed reqs K z sh
    (ps.filter (fun p=>p.key != K),{st with rng:=rng},t,[])
    (filter_current reqs st.al ps hc _) hsel hnd
    (fun v hm=>(valid_increase reqs hr v (hvalid v hm)).1)
    (fun v hm=>(valid_increase reqs hr v (hvalid v hm)).2)
  exact ⟨out,ho,hc',by simpa [ProcLiveLinks.live] using hd'⟩
end ZkFormal.NearV3.Candidates.ProcPoppedSuccess

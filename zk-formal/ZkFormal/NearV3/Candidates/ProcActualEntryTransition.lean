import ZkFormal.NearV3.Candidates.ProcActualReplayEntry
namespace ZkFormal.NearV3.Candidates.ProcActualEntryTransition
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayEntry

def cursor (s : Acc) : Nat := s.2.2.2.2.2.2.2.2.2.1
def entries (s : Acc) : Array Entry := s.2.2.2.2.2.2.2.2.2.2

set_option maxHeartbeats 800000 in
/-- Exact state/cursor/entry-count effect of the actual replay body. -/
theorem step_effect (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (s : Acc) (out : ForInStep Acc) (rng : NearSpecV3.Rng)
    (h : step I cv rd sh T x s=.ok out) :
    ∃next,out=.yield next ∧
      state next rng=ProcActualStateReplay.stateStep I cv (state s rng) sh[x]! ∧
      cursor next=cursor s+1 ∧ (entries next).size=(entries s).size+1 := by
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals exact ⟨_,rfl,rfl,rfl,by simp [entries]⟩

/-- The actual entry loop projects to sequential replay, preserving all side
accumulators while exposing its exact state and cursor evolution. -/
theorem loop_effect (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T : Nat) (xs : List Nat) (s out : Acc) (rng : NearSpecV3.Rng)
    (h : forIn xs s (step I cv rd sh T)=.ok out) :
    state out rng=(xs.map (fun x=>sh[x]!)).foldl (ProcActualStateReplay.stateStep I cv) (state s rng) ∧
    cursor out=cursor s+xs.length ∧ (entries out).size=(entries s).size+xs.length := by
  induction xs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact ⟨rfl,by simp,by simp⟩
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv rd sh T x s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,hstate,hcursor,hentries⟩ := step_effect I cv rd sh T x s next rng he
      simp only [he,bind,Except.bind] at h
      obtain ⟨hfinal,hcount,hsize⟩ := ih next h
      refine ⟨?_,?_,?_⟩
      · simpa only [List.map_cons,List.foldl_cons,hstate] using hfinal
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
/-- Matching sequential model events and valid pointers make the actual entry
loop succeed, including all memory/used-bit/push side effects. -/
theorem loop_success (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T : Nat) (xs : List Nat) (s : Acc) (rng : NearSpecV3.Rng)
    (hv : ∀x∈xs,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) sh[x]!)
    (he : xs.map (fun x=>rd.steps[x]!)=
      ProcActualStateReplay.events I cv (xs.map (fun x=>sh[x]!)) (cv.size+cursor s) (state s rng)) :
    ∃out,forIn xs s (step I cv rd sh T)=.ok out ∧
      state out rng=(xs.map (fun x=>sh[x]!)).foldl (ProcActualStateReplay.stateStep I cv) (state s rng) ∧
      cursor out=cursor s+xs.length ∧ (entries out).size=(entries s).size+xs.length := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl,rfl,by simp,by simp⟩
  | cons x xs ih =>
    simp only [List.map_cons,ProcActualStateReplay.events,List.cons.injEq] at he
    obtain ⟨next,hnext⟩ := step_success I cv rd sh T x s rng (hv x (by simp)) he.1
    obtain ⟨next',hy,hstate,hcursor,hentries⟩ := step_effect I cv rd sh T x s (.yield next) rng hnext
    cases hy
    have htail : xs.map (fun x=>rd.steps[x]!)=
        ProcActualStateReplay.events I cv (xs.map (fun x=>sh[x]!))
          (cv.size+cursor next) (state next rng) := by
      rw [hstate,hcursor]
      simpa only [Nat.add_assoc] using he.2
    obtain ⟨out,hout,_,_,_⟩ := ih next (fun x hx=>hv x (by simp [hx])) htail
    have hall : forIn (x::xs) s (step I cv rd sh T)=.ok out := by
      simpa only [List.forIn_cons,hnext,bind,Except.bind] using hout
    exact ⟨out,hall,loop_effect I cv rd sh T (x::xs) s out rng hall⟩

theorem map_indices {α : Type} [Inhabited α] (xs : List α) :
    (List.range xs.length).map (fun i=>xs[i]!)=xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [hj]

theorem events_length (I : Input) (cv : Array CReq) (vs : List Nat) (t : Nat) (st : PState) :
    (ProcActualStateReplay.events I cv vs t st).length=vs.length := by
  induction vs generalizing t st with
  | nil => rfl
  | cons v vs ih => simp [ProcActualStateReplay.events,ih]

/-- A successful model batch produces success of the actual indexed replay loop,
with arbitrary side accumulators and identical final state. -/
theorem model_batch_success (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (rd : Round) (sh : List Nat) (T : Nat) (s : Acc) (rng : NearSpecV3.Rng)
    (pending : List Push) (modelOut : ProcModelStep.EntryAcc)
    (hv : ∀v∈sh,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hs : ProcActualAllowanceShape.Shape I.ids.length (state s rng))
    (hmodel : forIn sh (pending,state s rng,cv.size+cursor s,[])
      (ProcModelStep.entryStep I.ids.length I.allowed (ProcActualConversionExact.view cv) rd.key rd.z)=.ok modelOut)
    (hsteps : rd.steps=modelOut.2.2.2) (hlen : rd.bucket.length=sh.length) :
    ∃out,forIn (List.range rd.bucket.length) s (step I cv rd sh T)=.ok out ∧
      state out rng=modelOut.2.1 ∧ cursor out=cursor s+rd.bucket.length ∧
      (entries out).size=(entries s).size+rd.bucket.length := by
  have he := ProcActualStateReplay.entries_events I cv hcv rd.key rd.z sh
    (pending,state s rng,cv.size+cursor s,[]) modelOut hv hs hmodel
  simp only [List.nil_append] at he
  have hslen : rd.steps.length=sh.length := by rw [hsteps,he,events_length]
  have hindices : (List.range rd.bucket.length).map (fun x=>sh[x]!)=sh := by rw [hlen,map_indices]
  have hevents : (List.range rd.bucket.length).map (fun x=>rd.steps[x]!)=
      ProcActualStateReplay.events I cv ((List.range rd.bucket.length).map (fun x=>sh[x]!))
        (cv.size+cursor s) (state s rng) := by
    rw [hindices,hlen,←hslen,map_indices,hsteps,he]
  have hp : ∀x∈List.range rd.bucket.length,
      ProcRequestPointers.Valid (ProcActualConversionExact.view cv) sh[x]! := by
    intro x hx
    have hlt : x<sh.length := by simpa [hlen] using List.mem_range.mp hx
    apply hv
    rw [getElem!_pos sh x hlt]
    exact List.getElem_mem hlt
  obtain ⟨out,ho,hstate,hcursor,hentries⟩ := loop_success I cv rd sh T _ s rng hp hevents
  refine ⟨out,ho,?_,by simpa using hcursor,by simpa using hentries⟩
  rw [hindices] at hstate
  rw [hstate]
  exact (ProcActualStateReplay.entries_state I cv hcv rd.key rd.z sh
    (pending,state s rng,cv.size+cursor s,[]) modelOut hv hmodel).symm

end ZkFormal.NearV3.Candidates.ProcActualEntryTransition

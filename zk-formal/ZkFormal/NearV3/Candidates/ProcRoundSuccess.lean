import ZkFormal.NearV3.Candidates.ProcTagTransition
namespace ZkFormal.NearV3.Candidates.ProcRoundSuccess
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcPendingCurrent ProcRoundGuards

def Ready (reqs : List Req) (s : ProcModelStep.Acc) : Prop :=
  Current reqs s.2.1.al s.1 ∧ (s.1.map (fun p=>link reqs p.v)).Nodup ∧
  (∀p∈s.1,ProcRequestPointers.Valid reqs p.v) ∧ Tags s.2.2.2.2 s.1

theorem initial_ready (sp : SchedPub) (hs : SchedPubOk sp) (prev : NearSpec.Bandwidth.State) :
    let I := ProcPreparedSequence.input sp prev
    let reqs := convRaw I.p I.ids.length I.raw
    Ready reqs (ProcModelStep.initial reqs (ProcCoreReplay.initial I)) := by
  have hh := ProcPreparedRequestGood.prepared_initial sp hs prev
  exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1,ProcRoundGuards.initial _ _⟩

set_option maxHeartbeats 800000 in
theorem step_success (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hr : ProcPoppedSuccess.GoodRequests reqs) (i : Nat) (s : ProcModelStep.Acc)
    (hs : Ready reqs s) (hn : s.1≠[]) (sh : List Nat) (rng : NearSpecV3.Rng)
    (hsh : NearSpecV3.shuffle
      ((sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).map (·.v)) s.2.1.rng=some (sh,rng)) :
    ∃out,ProcModelStep.step n allowed reqs i s=.ok (.yield out) ∧ Ready reqs out := by
  let K := ProcMaxBucket.maxKey s.1
  let b := sortTs (s.1.filter (fun p=>p.key==K))
  let z := (b.headD default).z
  have hg := guards s.2.2.2.2 s.1 hn hs.2.2.2
  change b.all (fun p=>p.z==z)=true ∧ ProcModelValid.Valid K z ∧ ProcZeroTransition.Ordered s.2.2.2.2 K z at hg
  obtain ⟨next,he,hc,hd⟩ := ProcPoppedSuccess.popped_success n allowed reqs hr s.1 s.2.1 K z
    s.2.2.1 hs.1 hs.2.1 hs.2.2.1 sh rng hsh
  have ht := ProcTagTransition.entries_tags n allowed reqs K z sh _ next
    (ProcTagTransition.filtered s.1 s.2.2.2.2 z hs.2.2.2 hg.2.2) he
  have hvalid : ∀v∈sh,ProcRequestPointers.Valid reqs v := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ((shuffle_perm hsh).mem_iff.mp hv)
    exact hs.2.2.1 p (List.mem_filter.mp ((ProcPushPerm.sort_perm _).mem_iff.mp hp)).1
  have hp := ProcEntryPointers.entries_inv n allowed reqs K z sh (fun q hq=>Nat.le_of_lt (hr q hq).1)
    hvalid _ next ⟨fun p hp=>hs.2.2.1 p (List.mem_filter.mp hp).1,by simp⟩ he
  let out : ProcModelStep.Acc :=
    (next.1,next.2.1,next.2.2.1,s.2.2.2.1++[⟨K,z,b,sh,s.2.2.1,next.2.2.2⟩],some (K,z))
  refine ⟨out,?_,hc,hd,hp.1,ht⟩
  have hempty : s.1.isEmpty=false := by simpa using hn
  have hzero : (decide (K=0) && decide (z=0))=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    have hh := hg.2.1
    simp only [ProcModelValid.Valid,h.1,ite_true] at hh
    omega
  have hpos : (decide (K>0) && (z != 0))=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at h
    have hh := hg.2.1
    have hK : K≠0 := by omega
    simp only [ProcModelValid.Valid,hK,ite_false] at hh
    exact h.2 hh
  have hmix := hg.1
  dsimp only [K,b,z,ProcMaxBucket.maxKey] at hzero hpos hmix he hsh ⊢
  cases hl : s.2.2.2.2 with
  | none =>
    simp only [ProcModelStep.step,hempty,Bool.false_eq_true,ite_false,hmix,Bool.not_true,
      hl,pure,Except.pure,bind,Except.bind,hsh,he]
    split
    · rename_i hz
      exact False.elim (Bool.false_ne_true (hzero.symm.trans hz))
    · split
      · rename_i hz
        exact False.elim (Bool.false_ne_true (hpos.symm.trans hz))
      · rfl
  | some pair =>
    rcases pair with ⟨prev,zprev⟩
    have ho := hg.2.2
    rw [hl] at ho
    have ho' : ((K<prev)||(K==0 && prev==0 && z==zprev+1))=true := by
      simpa only [ProcZeroTransition.Ordered,Bool.or_eq_true,decide_eq_true_eq,
        Bool.and_eq_true,beq_iff_eq,and_assoc] using ho
    dsimp only [K,b,z,ProcMaxBucket.maxKey] at ho'
    simp only [ProcModelStep.step,hempty,Bool.false_eq_true,ite_false,hmix,Bool.not_true,
      hl,pure,Except.pure,bind,Except.bind,hsh,he]
    split
    · rename_i hz
      exact False.elim (Bool.false_ne_true (hzero.symm.trans hz))
    · split
      · rename_i hz
        exact False.elim (Bool.false_ne_true (hpos.symm.trans hz))
      · split
        · rename_i hord
          exact False.elim (Bool.false_ne_true ((congrArg Bool.not ho').symm.trans hord))
        · rfl
end ZkFormal.NearV3.Candidates.ProcRoundSuccess

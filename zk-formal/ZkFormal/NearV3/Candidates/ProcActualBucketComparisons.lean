import ZkFormal.NearV3.Candidates.ProcActualRoundTimes
namespace ZkFormal.NearV3.Candidates.ProcActualBucketComparisons
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev Cmps := ProcActualMemoryScan.Cmps

def step (rd : Gen.RoundD) (i : Nat) (cs : Cmps) : Except String (ForInStep Cmps) := do
  let es := rd.entries.toArray
  let e := es[i]!
  let cx := if i+1=es.size then rd.T else es[i+1]!.ts
  check (e.ts<cx) "bucket ts order"
  pure (.yield (cs.push (cx,e.ts+1,if e.ts+1≤cx then 1 else 0)))

theorem step_success (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (i : Nat) (hi : i<rd.entries.length) (cs : Cmps) :
    ∃out,step rd i cs=.ok (.yield out) := by
  unfold step
  dsimp only
  rw [ProcActualRoundTimes.good_checks rd hg i hi]
  exact ⟨_,rfl⟩

theorem loop_success (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd)
    (xs : List Nat) (hx : ∀i∈xs,i<rd.entries.length) (cs : Cmps) :
    ∃out,forIn xs cs (step rd)=.ok out := by
  induction xs generalizing cs with
  | nil => exact ⟨cs,rfl⟩
  | cons i xs ih =>
    obtain ⟨mid,hm⟩ := step_success rd hg i (hx i (by simp)) cs
    obtain ⟨out,ho⟩ := ih (fun j hj=>hx j (by simp [hj])) mid
    refine ⟨out,?_⟩
    simpa only [List.forIn_cons,hm,bind,Except.bind] using ho

theorem bucket_success (rd : Gen.RoundD) (hg : ProcActualRoundTimes.Good rd) (cs : Cmps) :
    ∃out,forIn (List.range rd.entries.toArray.size) cs (step rd)=.ok out := by
  apply loop_success rd hg
  simpa only [List.size_toArray,List.mem_range] using
    (fun (i : Nat) (hi : i<rd.entries.length)=>hi)
theorem actual_loop_eq (rd : Gen.RoundD) (cs : Cmps) :
    (do
      let es := rd.entries.toArray
      let mut cmps := cs
      for i in List.range es.size do
        let e := es[i]!
        let cx := if i+1=es.size then rd.T else es[i+1]!.ts
        check (e.ts<cx) "bucket ts order"
        cmps := cmps.push (cx,e.ts+1,if e.ts+1≤cx then 1 else 0)
      pure cmps : Except String Cmps) =
    forIn (List.range rd.entries.toArray.size) cs (step rd) := by
  change (forIn (List.range rd.entries.toArray.size) cs (step rd) >>= fun out => pure out) = _
  cases forIn (List.range rd.entries.toArray.size) cs (step rd) <;> rfl
end ZkFormal.NearV3.Candidates.ProcActualBucketComparisons

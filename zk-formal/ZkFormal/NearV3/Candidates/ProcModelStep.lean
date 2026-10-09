import ZkFormal.NearV3.Candidates.ProcModelRounds
namespace ZkFormal.NearV3.Candidates.ProcModelStep
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3 NearSpecV3.Scheduler
abbrev Acc := List Push × PState × Nat × List Round × Option (Nat×Nat)

abbrev EntryAcc := List Push × PState × Nat × List Step

def entryStep (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (K z : Nat) (v : Nat) (acc : EntryAcc) : Except String (ForInStep EntryAcc) := do
  let reqA := reqs.toArray
  let mut pend := acc.1
  let mut st := acc.2.1
  let mut t := acc.2.2.1
  let mut steps := acc.2.2.2
  let rid := v / 64
  let j := v % 64
  let q : Req := reqA[rid]!
  let inc := q.incs.getD j 0
  let last := j + 1 == q.incs.length
  let s := q.link / n
  let r := q.link % n
  let ok := allowed[q.link]! && decide (inc ≤ st.sb[s]!) && decide (inc ≤ st.rb[r]!)
  if ok then
    st := { st with sb := st.sb.set! s (st.sb[s]! - inc), rb := st.rb.set! r (st.rb[r]! - inc),
                    al := st.al.set! q.link (st.al[q.link]! - inc),
                    g := st.g.set! q.link (st.g[q.link]! + inc) }
  let aOut := st.al[q.link]!
  if ok && !last then
    if !(aOut < K || (K == 0 && aOut == 0)) then throw "re-push to a key ≥ the popped key"
    let z' := if aOut = 0 then (if K = 0 then z + 1 else 1) else 0
    pend := pend ++ [⟨t, aOut, z', v + 1⟩]
  steps := steps ++ [⟨t, v, q.link, inc, last, ok, aOut⟩]
  t := t + 1
  return .yield (pend,st,t,steps)

/-- Definitional factoring of the existing native event-loop body. -/
def step (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (_ : Nat) (acc : Acc) : Except String (ForInStep Acc) := do
  let reqA := reqs.toArray
  let mut pend := acc.1
  let mut st := acc.2.1
  let mut t := acc.2.2.1
  let mut rounds := acc.2.2.2.1
  let mut lastKey := acc.2.2.2.2
  if pend.isEmpty then return .done acc
  let K := pend.foldl (fun m p => Nat.max m p.key) 0
  let bucket := sortTs (pend.filter (·.key == K))
  let z := (bucket.headD default).z
  if !(bucket.all (·.z == z)) then throw "bucket with mixed z"
  if K = 0 && z = 0 then throw "0-round with z = 0"
  if K > 0 && z != 0 then throw "positive round with z ≠ 0"
  match lastKey with
  | some (K', z') =>
    if !(K < K' || (K == 0 && K' == 0 && z == z' + 1)) then throw s!"round order: {K'},{z'} then {K},{z}"
  | none => pure ()
  lastKey := some (K, z)
  pend := pend.filter (·.key != K)
  let vs := bucket.map (·.v)
  let ks := t  -- informational
  match shuffle vs st.rng with
  | none => throw "shuffle fuel"
  | some (sh, rng) =>
    st := { st with rng := rng }
    let mut steps : List Step := []
    let result ← forIn sh (pend,st,t,steps) (entryStep n allowed reqs K z)
    pend := result.1
    st := result.2.1
    t := result.2.2.1
    steps := result.2.2.2
    rounds := rounds ++ [⟨K, z, bucket, sh, ks, steps⟩]
  return .yield (pend,st,t,rounds,lastKey)

def initial (reqs : List Scheduler.Req) (st0 : PState) : Acc :=
  let init := (List.range reqs.length).filterMap fun i =>
    let q := reqs.toArray[i]!
    if q.incs.isEmpty then none else
      let k := st0.al[q.link]!
      some ⟨i,k,if k=0 then 1 else 0,i*64⟩
  (init,st0,reqs.length,[],none)

theorem process_eq (n : Nat) (allowed : Array Bool) (reqs : List Scheduler.Req)
    (st0 : PState) (fuel : Nat) : processEv n allowed reqs st0 fuel = (do
      let out ← forIn (List.range fuel) (initial reqs st0) (step n allowed reqs)
      if !out.1.isEmpty then throw "out of fuel"
      return (out.2.1,out.2.2.2.1)) := rfl
end ZkFormal.NearV3.Candidates.ProcModelStep

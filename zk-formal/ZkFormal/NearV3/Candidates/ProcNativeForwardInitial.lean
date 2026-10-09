import ZkFormal.NearV3.Candidates.ProcNativeForwardSize
namespace ZkFormal.NearV3.Candidates.ProcNativeForwardInitial
open NearSpec NearSpecV3

def limits (prims : Prims) (ctx : ApplyCtx) (so : SchedOut) : List Limit :=
  ctx.statuses.map fun (s,ci,missed)=>
    ⟨s,if s==ctx.own then GASMAX else prims.outGas ci missed ctx.own,so.grant ctx.own s⟩

/-- Deduplicating the status shard inventory preserves exactly its membership;
no uniqueness of native chunk slots is assumed. -/
theorem status_fold_mem (xs : List (Nat×Congestion×Nat)) (acc : List Nat) (s : Nat) :
    s∈xs.foldl (fun acc (s,_,_)=>if acc.contains s then acc else acc++[s]) acc ↔
      s∈acc ∨ s∈xs.map Prod.fst := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,List.map_cons,List.mem_cons]
    by_cases hx : x.1∈acc
    · by_cases he : s=x.1 <;> simp_all
    · simp [hx,or_assoc]

theorem status_mem (ctx : ApplyCtx) (s : Nat) :
    s∈statusShards ctx ↔ s∈ctx.statuses.map Prod.fst := by
  simpa only [statusShards,List.not_mem_nil,false_or] using status_fold_mem ctx.statuses [] s

/-- Every duplicate destination has the same scheduler size grant. Therefore
the first-match lookup is independent of the duplicate statuses' gas data. -/
theorem mapped_size (xs : List (Nat×Congestion×Nat)) (gas : Nat → Congestion → Nat → Nat)
    (grant : Nat → Nat) (s : Nat) (hs : s∈xs.map Prod.fst) :
    (Limit.get (xs.map fun (sh,ci,missed)=>⟨sh,gas sh ci missed,grant sh⟩) s).size=grant s := by
  induction xs with
  | nil => simp at hs
  | cons x xs ih =>
    simp only [List.map_cons,List.mem_cons] at hs
    by_cases hx : x.1=s
    · simp [Limit.get,hx]
    · have ht : s∈xs.map Prod.fst := hs.resolve_left (Ne.symm hx)
      simpa [Limit.get,List.find?_cons,hx] using ih ht

theorem initial_size (prims : Prims) (ctx : ApplyCtx) (so : SchedOut) (s : Nat)
    (hs : s∈statusShards ctx) : (Limit.get (limits prims ctx so) s).size=so.grant ctx.own s :=
  mapped_size ctx.statuses (fun sh ci missed=>if sh==ctx.own then GASMAX else prims.outGas ci missed ctx.own)
    (so.grant ctx.own) s ((status_mem ctx s).mp hs)

/-- Native forwarding cannot exceed the scheduler's initial destination grant. -/
theorem demand_grant (prims : Prims) (ctx : ApplyCtx) (so : SchedOut)
    (rs : List Receipt) (out : List Limit)
    (h : ProcNativeForwardSize.forwardAll ctx (limits prims ctx so) rs=some out)
    (d : Nat×Nat) (hd : d∈fwdSizes ctx rs) : d.2≤so.grant ctx.own d.1 := by
  have hb := ProcNativeForwardSize.demand_bound ctx rs (limits prims ctx so) out h d hd
  have hm : d.1∈statusShards ctx := by
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hd
    exact hs
  rwa [initial_size prims ctx so d.1 hm] at hb
end ZkFormal.NearV3.Candidates.ProcNativeForwardInitial

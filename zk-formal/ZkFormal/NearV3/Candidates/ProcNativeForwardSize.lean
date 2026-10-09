import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardBound
namespace ZkFormal.NearV3.Candidates.ProcNativeForwardSize
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open NearSpec NearSpecV3

theorem get_map (ls : List Limit) (l : Limit) (s : Nat)
    (h : s≠l.shard ∨ ls.any (·.shard == l.shard)=true) :
    (Limit.get (ls.map (fun x=>if x.shard==l.shard then l else x)) s).size =
      if s=l.shard then l.size else (Limit.get ls s).size := by
  induction ls with
  | nil => simp_all [Limit.get]
  | cons x xs ih =>
    by_cases hx : x.shard=l.shard <;> by_cases hs : s=l.shard <;>
      by_cases hxs : x.shard=s <;>
      simp_all [Limit.get,List.find?_cons]
    obtain ⟨y,hy,he⟩ := h
    exact ih y hy he

theorem get_put (ls : List Limit) (l : Limit) (s : Nat) :
    (Limit.get (Limit.put ls l) s).size =
      if s=l.shard then l.size else (Limit.get ls s).size := by
  unfold Limit.put
  split
  · rename_i h; exact get_map ls l s (Or.inr h)
  · rename_i h
    have hn : ∀x∈ls,x.shard≠l.shard := by simpa using h
    induction ls with
    | nil =>
      by_cases hs : s=l.shard
      · simp [Limit.get,hs]
      · simp [Limit.get,hs,Ne.symm hs]
    | cons x xs ih =>
      have hx := hn x (by simp)
      have ht : ∀y∈xs,y.shard≠l.shard := fun y hy=>hn y (by simp [hy])
      have hh : ¬xs.any (·.shard==l.shard)=true := by simpa using ht
      have hi := ih hh ht
      by_cases hs : x.shard=s <;> simp_all [Limit.get,List.find?_cons]

/-- A successful native forwarding step spends exactly the capped encoded size
at its destination and preserves every other destination's size budget. -/
theorem step_size (ctx : ApplyCtx) (ls out : List Limit) (r : Receipt)
    (h : tryForward ctx ls r=some out) (s : Nat) :
    (Limit.get out s).size +
      (if ctx.layout.shardOf r.receiverId=s then min r.encode.length maxReceiptSize else 0) =
    (Limit.get ls s).size := by
  unfold tryForward at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst out
    rw [get_put]
    have hb : min r.encode.length maxReceiptSize ≤
        (Limit.get ls (ctx.layout.shardOf r.receiverId)).size := by
      have hh : (Limit.get ls (ctx.layout.shardOf r.receiverId)).gas ≥ min (refundCongestionGas r.receiverId) allowedShardOutgoingGas ∧ (Limit.get ls (ctx.layout.shardOf r.receiverId)).size ≥ min r.encode.length maxReceiptSize := by simpa using hc
      exact hh.2
    by_cases hs : s=ctx.layout.shardOf r.receiverId
    · subst s; simp only [ite_true]; omega
    · simp [hs,Ne.symm hs]
  · cases h
def forwardAll (ctx : ApplyCtx) (ls : List Limit) : List Receipt → Option (List Limit)
  | [] => some ls
  | r::rs => (tryForward ctx ls r).bind (fun next=>forwardAll ctx next rs)

theorem all_sizes (ctx : ApplyCtx) (rs : List Receipt) (ls out : List Limit)
    (h : forwardAll ctx ls rs=some out) (s : Nat) :
    (Limit.get out s).size +
      ((rs.filter fun r=>ctx.layout.shardOf r.receiverId==s).map
        fun r=>min r.encode.length maxReceiptSize).sum = (Limit.get ls s).size := by
  induction rs generalizing ls with
  | nil => simp only [forwardAll,Option.some.injEq] at h; subst out; simp
  | cons r rs ih =>
    simp only [forwardAll] at h
    cases he : tryForward ctx ls r with
    | none => simp [he] at h
    | some next =>
      simp only [he,Option.bind_some] at h
      have ht := ih next h
      have hs := step_size ctx ls next r he s
      by_cases hr : ctx.layout.shardOf r.receiverId=s
      · simp [List.filter_cons,hr] at *; omega
      · simp [List.filter_cons,hr] at *; omega

theorem demand_bound (ctx : ApplyCtx) (rs : List Receipt) (ls out : List Limit)
    (h : forwardAll ctx ls rs=some out) (d : Nat×Nat) (hd : d∈fwdSizes ctx rs) :
    d.2≤(Limit.get ls d.1).size := by
  obtain ⟨s,_,he⟩ := List.mem_map.mp hd
  subst d
  have hh := all_sizes ctx rs ls out h s
  dsimp only
  omega
end ZkFormal.NearV3.Candidates.ProcNativeForwardSize

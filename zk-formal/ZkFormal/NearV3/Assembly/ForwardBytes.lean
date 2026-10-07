import ZkFormal.NearV3.Assembly.Forward

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

private theorem get_updated_same (ls : List Limit) (l : Limit)
    (hex : ∃ x ∈ ls, x.shard = l.shard) :
    Limit.get (ls.map (fun x => if x.shard == l.shard then l else x)) l.shard = l := by
  induction ls with
  | nil => simp at hex
  | cons a rest ih =>
    by_cases ha : a.shard = l.shard
    · simp [Limit.get,ha]
    · have ht : ∃ x ∈ rest, x.shard = l.shard := by
        obtain ⟨x,hx,he⟩ := hex
        rcases List.mem_cons.mp hx with rfl | hx
        · exact False.elim (ha he)
        · exact ⟨x,hx,he⟩
      simpa [Limit.get,ha] using ih ht

private theorem get_updated_other (ls : List Limit) (l : Limit) (s : Nat) (hne : s ≠ l.shard) :
    Limit.get (ls.map (fun x => if x.shard == l.shard then l else x)) s = Limit.get ls s := by
  induction ls with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : a.shard = l.shard
    · simp [Limit.get,ha,Ne.symm hne] at *
      exact ih
    · by_cases hs : a.shard = s
      · simp [Limit.get,hs,hne]
      · simpa [Limit.get,ha,hs] using ih

theorem tryForward_size_balance {ctx : ApplyCtx} {ls ls' : List Limit} {r : Receipt}
    (h : tryForward ctx ls r = some ls') (s : Nat) :
    (Limit.get ls' s).size + (if ctx.layout.shardOf r.receiverId == s then
      min r.encode.length maxReceiptSize else 0) = (Limit.get ls s).size := by
  have hex := tryForward_has_limit h
  unfold tryForward at h
  dsimp only at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hg
    cases h
    have ha : ls.any (·.shard == ctx.layout.shardOf r.receiverId) = true := by
      obtain ⟨l,hl,he⟩ := hex
      exact List.any_eq_true.mpr ⟨l,hl,beq_iff_eq.mpr he⟩
    unfold Limit.put
    simp only [ha,↓reduceIte]
    by_cases hs : s = ctx.layout.shardOf r.receiverId
    · subst s
      rw [get_updated_same ls ⟨ctx.layout.shardOf r.receiverId,
        (Limit.get ls (ctx.layout.shardOf r.receiverId)).gas - refundCongestionGas r.receiverId,
        (Limit.get ls (ctx.layout.shardOf r.receiverId)).size - min r.encode.length maxReceiptSize⟩ hex]
      simp only [beq_self_eq_true,↓reduceIte]
      omega
    · rw [get_updated_other ls ⟨ctx.layout.shardOf r.receiverId,
        (Limit.get ls (ctx.layout.shardOf r.receiverId)).gas - refundCongestionGas r.receiverId,
        (Limit.get ls (ctx.layout.shardOf r.receiverId)).size - min r.encode.length maxReceiptSize⟩ s hs]
      simp [Ne.symm hs]
  · cases h

def forwardedSize (ctx : ApplyCtx) (rs : List Receipt) (s : Nat) : Nat :=
  ((rs.filter fun r => ctx.layout.shardOf r.receiverId == s).map
    fun r => min r.encode.length maxReceiptSize).sum

theorem forwardRun_size_balance (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (ls ls' : List Limit), forwardRun ctx ls rs = .ok ls' →
      ∀ s, (Limit.get ls' s).size + forwardedSize ctx rs s = (Limit.get ls s).size
  | [], ls, ls', h, s => by cases h; simp [forwardedSize]
  | r :: rs, ls, ls', h, s => by
    unfold forwardRun at h
    simp only [List.foldlM_cons] at h
    cases hs : tryForward ctx ls r with
    | none => simp [hs,bind,Except.bind] at h
    | some next =>
      simp only [hs,bind,Except.bind] at h
      have hi := forwardRun_size_balance ctx rs next ls' h s
      have hh := tryForward_size_balance hs s
      unfold forwardedSize at *
      simp only [List.filter_cons]
      split <;> simp_all only [List.map_cons,List.sum_cons,Bool.false_eq_true,↓reduceIte] <;> omega

theorem limit_get_size_bound {ls : List Limit} {bound : Nat}
    (h : ∀ l ∈ ls, l.size ≤ bound) (s : Nat) : (Limit.get ls s).size ≤ bound := by
  unfold Limit.get
  cases he : ls.find? (·.shard == s) with
  | none => simp
  | some l => exact h l (List.mem_of_find?_eq_some he)

theorem forwardRun_demand_guard {ctx : ApplyCtx} {rs : List Receipt} {ls ls' : List Limit}
    (h : forwardRun ctx ls rs = .ok ls') (hb : ∀ l ∈ ls, l.size ≤ 4500000) :
    ((fwdLinks ctx rs).all fun (_,d) => decide (d < fwdDemandMax)) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  unfold fwdLinks at hp
  dsimp only at hp
  split at hp
  · simp at hp
  · obtain ⟨z,hz,he⟩ := List.mem_filterMap.mp hp
    obtain ⟨s,_,hz⟩ := List.mem_map.mp hz
    subst z
    cases hi : Scheduler.indexOf ctx.layout.shardIds s with
    | none => simp [hi] at he
    | some i =>
      simp only [hi,Option.map_some,Option.some.injEq] at he
      subst p
      have hg := forwardRun_size_balance ctx rs ls ls' h s
      have hb := limit_get_size_bound hb s
      change decide (forwardedSize ctx rs s < fwdDemandMax) = true
      apply decide_eq_true
      unfold forwardedSize fwdDemandMax
      unfold forwardedSize at hg
      omega

end ZkFormal.NearV3.Assembly

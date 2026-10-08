import ZkFormal.NearV3.Candidates.ProcPriorCellBits
namespace ZkFormal.NearV3.Candidates.ProcPriorIndexed
open NearSpec NearSpec.Bandwidth ProcPriorRows ProcPriorEvents

theorem pair_split {α : Type} (xs : List α) (j : Nat) (a b : α)
    (ha:xs[j]?=some a) (hb:xs[j+1]?=some b) : ∃ pre post,xs=pre++a::b::post := by
  induction xs generalizing j with
  | nil => simp at ha
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at ha
      subst x
      cases xs with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hb
        subst y
        exact ⟨[],ys,rfl⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at ha hb
      obtain ⟨pre,post,he⟩:=ih j ha hb
      exact ⟨x::pre,post,by simp [he]⟩

theorem first_zero (ids : List Nat) (rs : List LinkAllowance) (a : Row)
    (h:(rows ids rs)[0]?=some a) : a.before=ProcPriorCarry.zero := by
  unfold rows at h
  cases he:events ids rs with
  | nil => simp [he,rowsFrom] at h
  | cons e es =>
    simp only [he,rowsFrom,List.getElem?_cons_zero,Option.some.injEq] at h
    subst a
    rfl

theorem row_bound (ids : List Nat) (rs : List LinkAllowance) (hn:ids.length≤64)
    (a : Row) (ha:a∈rows ids rs) : a.event.link<4096 := by
  have hm:a.event∈events ids rs := by
    rw [←rowsFrom_events ⟨none,ProcPriorCarry.zero⟩ (events ids rs)]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have hb:ids.length*ids.length≤64*64:=Nat.mul_le_mul hn hn
  have he:=(event_bounds ids rs a.event hm).1
  omega

theorem pair_native (ids : List Nat) (rs : List LinkAllowance) (pre post : List Row) (a b : Row)
    (h:rows ids rs=pre++a::b::post) :
    b.before=(if a.event.link=b.event.link then ProcPriorValues.value a.event else ProcPriorCarry.zero) ∧
    (a.event.query=true → a.event.link≠b.event.link) := by
  refine ⟨ProcPriorRowNext.rows_next ids rs pre post a b h,?_⟩
  have hm:=congrArg (List.map Row.event) h
  have he:events ids rs=pre.map Row.event++a.event::b.event::post.map Row.event := by
    simpa only [rows,rowsFrom_events,List.map_append,List.map_cons] using hm
  exact ProcPriorEventNext.query_final ids rs _ _ _ _ he

end ZkFormal.NearV3.Candidates.ProcPriorIndexed

import ZkFormal.NearV3.Candidates.ProcPriorIdRows
namespace ZkFormal.NearV3.Candidates.ProcPriorIdNext
open NearSpec NearSpec.Bandwidth ProcPriorIds ProcPriorIdCarry ProcPriorIdRows

theorem rowsFrom_next (s : ProcPriorIdCarry.State) (es : List Event)
    (pre post : List Row) (a b : Row) (h:rowsFrom s es=pre++a::b::post) :
    b.before=if a.event.key=b.event.key then update a.before a.event else zero := by
  induction pre generalizing s es with
  | nil =>
    cases es with
    | nil => simp [rowsFrom] at h
    | cons e es =>
      cases es with
      | nil => simp [rowsFrom] at h
      | cons f fs =>
        simp only [List.nil_append,rowsFrom,List.cons.injEq] at h
        obtain ⟨ha,hb,_⟩:=h
        subst a; subst b
        simp [atKey,ProcPriorIdCarry.step]
  | cons x pre ih =>
    cases es with
    | nil => simp [rowsFrom] at h
    | cons e es =>
      simp only [rowsFrom,List.cons_append,List.cons.injEq] at h
      exact ih (ProcPriorIdCarry.step s e) es h.2

theorem rows_next (ids : List Nat) (rs : List LinkAllowance)
    (pre post : List Row) (a b : Row) (h:rows ids rs=pre++a::b::post) :
    b.before=if a.event.key=b.event.key then update a.before a.event else zero :=
  rowsFrom_next ⟨none,zero⟩ (events ids rs) pre post a b h

theorem first_zero (ids : List Nat) (rs : List LinkAllowance) (a : Row)
    (ha:(rows ids rs)[0]?=some a) : a.before=zero := by
  unfold rows at ha
  cases hs:events ids rs with
  | nil => simp [hs,rowsFrom] at ha
  | cons e es =>
    simp only [hs,rowsFrom,List.getElem?_cons_zero,Option.some.injEq] at ha
    subst a
    rfl

theorem pair_order (ids : List Nat) (rs : List LinkAllowance)
    (pre post : List Row) (a b : Row) (h:rows ids rs=pre++a::b::post) :
    precedes a.event b.event=true := by
  have hs:=events_sorted ids rs
  have hm:=rowsFrom_events ⟨none,zero⟩ (events ids rs)
  change (rows ids rs).map (·.event)=events ids rs at hm
  rw [←hm,h,List.map_append] at hs
  have ht:=(List.pairwise_append.mp hs).2.1
  simp only [List.map_cons,List.pairwise_cons] at ht
  exact ht.1 b.event (by simp)

end ZkFormal.NearV3.Candidates.ProcPriorIdNext

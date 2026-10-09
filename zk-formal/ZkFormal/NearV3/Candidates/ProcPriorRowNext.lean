import ZkFormal.NearV3.Candidates.ProcPriorRows
namespace ZkFormal.NearV3.Candidates.ProcPriorRowNext
open NearSpec NearSpec.Bandwidth ProcPriorEvents ProcPriorValues ProcPriorCarry ProcPriorRows

theorem rowsFrom_next (s : ProcPriorCarry.State) (es : List Event) (pre post : List Row) (a b : Row)
    (h:rowsFrom s es=pre++a::b::post) :
    b.before=if a.event.link=b.event.link then update a.before a.event else zero := by
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
        simp [atKey,ProcPriorCarry.step]
  | cons x pre ih =>
    cases es with
    | nil => simp [rowsFrom] at h
    | cons e es =>
      simp only [rowsFrom,List.cons_append,List.cons.injEq] at h
      exact ih (ProcPriorCarry.step s e) es h.2

theorem rows_next (ids : List Nat) (rs : List LinkAllowance) (pre post : List Row) (a b : Row)
    (h:rows ids rs=pre++a::b::post) :
    b.before=if a.event.link=b.event.link then value a.event else zero := by
  have hn:=rowsFrom_next ⟨none,zero⟩ (events ids rs) pre post a b h
  have ha:a∈rows ids rs := by rw [h]; simp
  have hu:update a.before a.event=value a.event := by
    cases hq:a.event.query with
    | false => simp [update,hq]
    | true => simp [update,hq,query_row ids rs a ha hq]
  simpa only [hu] using hn

end ZkFormal.NearV3.Candidates.ProcPriorRowNext

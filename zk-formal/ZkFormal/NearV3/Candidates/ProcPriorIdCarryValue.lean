import ZkFormal.NearV3.Candidates.ProcPriorIdCarry
namespace ZkFormal.NearV3.Candidates.ProcPriorIdCarryValue
open NearSpec NearSpec.Bandwidth ProcPriorIds ProcPriorIdCarry ProcPriorIdValue

theorem fold_some (es : List Event) (v : Nat) : es.foldl update (some v)=some v := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

theorem fold_public (es : List Event) (h:∀e∈es,e.isPublic=true) :
    es.foldl update none=es.head?.map (·.ordinal) := by
  cases es with
  | nil => rfl
  | cons e es =>
    have he:=h e (by simp)
    simp only [List.foldl_cons,update,he,ite_true]
    exact fold_some es e.ordinal

theorem ignored_fold (es : List Event) (v : Value) (h:∀e∈es,e.isPublic=false) :
    es.foldl update v=v := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    have he:=h e (by simp)
    have ht:=ih v (fun x hx=>h x (by simp [hx]))
    cases v <;> simpa [List.foldl_cons,update,he] using ht

theorem ignored_tail (pre post : List Event) (key : Nat)
    (h:∀e∈post,e.key=key→e.isPublic=false) :
    foldKey (pre++post) key=foldKey pre key := by
  simp only [foldKey,List.filter_append,List.foldl_append]
  apply ignored_fold
  intro e he
  obtain ⟨hm,hk⟩:=List.mem_filter.mp he
  exact h e hm (by simpa using hk)

theorem full_query (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (he:e∈requestEvents ids rs) : foldKey (events ids rs) e.key=e.result := by
  rw [foldKey,ProcPriorIdOrder.per_id_order,List.filter_append,List.foldl_append]
  have hr:∀x∈((requestEvents ids rs).filter fun x=>x.key==e.key),x.isPublic=false := by
    intro x hx
    obtain ⟨_,_,_,hp,_,_⟩:=request_source ids rs x (List.mem_filter.mp hx).1
    exact hp
  rw [ignored_fold _ _ hr]
  have hp:∀x∈((publicEvents ids).filter fun x=>x.key==e.key),x.isPublic=true := by
    intro x hx
    exact (public_source ids x (List.mem_filter.mp hx).1).2.1
  rw [show zero=none from rfl,fold_public _ hp]
  exact (query_first_public ids rs e he).symm

end ZkFormal.NearV3.Candidates.ProcPriorIdCarryValue

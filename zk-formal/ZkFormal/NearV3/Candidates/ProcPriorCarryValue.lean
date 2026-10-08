import ZkFormal.NearV3.Candidates.ProcPriorCarry
namespace ZkFormal.NearV3.Candidates.ProcPriorCarryValue
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched ProcPriorEvents ProcPriorValues ProcPriorCarry

theorem fold_update (es : List Event) (v : Value) :
    es.foldl update v=(((es.filter fun e=>!e.query).map value).getLast?).getD v := by
  induction es using snoc_induction with
  | h0 => rfl
  | hs es e ih =>
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    cases he:e.query <;> simp [update,he,List.filter_append,List.getLast?_append]

theorem foldKey_values (es : List Event) (k : Nat) :
    foldKey es k=((((es.filter fun e=>e.link==k).filter fun e=>!e.query).map value).getLast?).getD zero :=
  fold_update _ _

theorem all_writes (ids : List Nat) (rs : List LinkAllowance) :
    (writeEvents ids rs).filter (fun e=>!e.query)=writeEvents ids rs := by
  apply List.filter_eq_self.mpr
  intro e he
  obtain ⟨_,_,_,hq,_,_⟩:=write_source ids rs e he
  simp [hq]

theorem no_queries (ids : List Nat) (rs : List LinkAllowance) :
    (queryEvents ids rs).filter (fun e=>!e.query)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  have hq:= (query_source ids rs e he).2.2.1
  simp [hq]

theorem full_query (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈queryEvents ids rs) : foldKey (events ids rs) e.link=value e := by
  rw [foldKey_values,ProcPriorEventOrder.per_link_order,List.filter_filter]
  have hf:((writeEvents ids rs++queryEvents ids rs).filter (fun x=>!x.query)).filter (fun x=>x.link==e.link)=
      (writeEvents ids rs).filter (fun x=>x.link==e.link) := by
    rw [List.filter_append,all_writes,no_queries,List.append_nil]
  have hswap : ((writeEvents ids rs++queryEvents ids rs).filter (fun x=>!x.query && x.link==e.link))=
      (writeEvents ids rs).filter (fun x=>x.link==e.link) := by
    simpa only [List.filter_filter,Bool.and_comm] using hf
  rw [hswap]
  exact (query_last_write ids rs e h).symm

theorem ignored_fold (es : List Event) (v : Value) (h:∀ e∈es,e.query=true) : es.foldl update v=v := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons,ih _ (fun x hx=>h x (by simp [hx]))]
    simp [update,h e (by simp)]

theorem ignored_tail (pre post : List Event) (k : Nat)
    (h:∀ e∈post,e.link=k→e.query=true) : foldKey (pre++post) k=foldKey pre k := by
  unfold foldKey
  rw [List.filter_append,List.foldl_append]
  apply ignored_fold
  intro e he
  obtain ⟨hm,hk⟩:=List.mem_filter.mp he
  exact h e hm (of_decide_eq_true hk)

end ZkFormal.NearV3.Candidates.ProcPriorCarryValue

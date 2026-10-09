import ZkFormal.NearV3.Candidates.ProcPriorSummary
namespace ZkFormal.NearV3.Candidates.ProcPriorEvents
open NearSpec NearSpec.Bandwidth ProcPriorLookup ProcPriorWinner ProcPriorSummary

structure Event where
  link : Nat
  stamp : Nat
  query : Bool
  lo : Nat
  hi : Bool
  deriving DecidableEq, Repr

def writeEvents (ids : List Nat) (rs : List LinkAllowance) : List Event :=
  rs.zipIdx.filterMap fun (r,j)=>(target ids r).map fun l=>⟨l,j,false,low r.allowance,big r.allowance⟩

def queryEvents (ids : List Nat) (rs : List LinkAllowance) : List Event :=
  (List.range (ids.length*ids.length)).map fun l=>
    let v:=((winner ids rs l).map (·.allowance)).getD 0
    ⟨l,rs.length,true,low v,big v⟩

def precedes (a b : Event) : Bool := decide (a.link<b.link ∨ a.link=b.link ∧ a.stamp≤b.stamp)

def events (ids : List Nat) (rs : List LinkAllowance) : List Event :=
  (writeEvents ids rs++queryEvents ids rs).mergeSort precedes

theorem precedes_trans (a b c : Event) (h1:precedes a b) (h2:precedes b c) : precedes a c := by
  simp only [precedes,decide_eq_true_eq] at *
  omega

theorem precedes_total (a b : Event) : precedes a b || precedes b a := by
  simp only [precedes,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem events_perm (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).Perm (writeEvents ids rs++queryEvents ids rs) := List.mergeSort_perm _ _

theorem events_sorted (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).Pairwise (fun a b=>precedes a b=true) :=
  List.pairwise_mergeSort precedes_trans precedes_total _

theorem writes_length (ids : List Nat) (rs : List LinkAllowance) :
    (writeEvents ids rs).length≤rs.length := by
  simpa only [writeEvents,List.length_zipIdx] using (List.length_filterMap_le
    (fun (r,j)=>(target ids r).map fun l=>Event.mk l j false (low r.allowance) (big r.allowance)) rs.zipIdx)

theorem events_length (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).length≤rs.length+ids.length*ids.length := by
  rw [(events_perm ids rs).length_eq,List.length_append]
  have h:=writes_length ids rs
  simp only [queryEvents,List.length_map,List.length_range]
  omega

theorem write_source (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈writeEvents ids rs) :
    ∃ r,rs[e.stamp]?=some r ∧ target ids r=some e.link ∧ e.query=false ∧
      e.lo=low r.allowance ∧ e.hi=big r.allowance := by
  obtain ⟨⟨r,j⟩,hj,he⟩:=List.mem_filterMap.mp h
  have hr:=List.mk_mem_zipIdx_iff_getElem?.mp hj
  cases ht:target ids r with
  | none => simp [ht] at he
  | some l =>
    simp only [ht,Option.map_some,Option.some.injEq] at he
    subst e
    exact ⟨r,hr,ht,rfl,rfl,rfl⟩

theorem write_before_queries (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈writeEvents ids rs) : e.stamp<rs.length := by
  obtain ⟨r,hr,-⟩:=write_source ids rs e h
  exact List.getElem?_eq_some_iff.mp hr |>.1

theorem query_source (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈queryEvents ids rs) :
    e.link<ids.length*ids.length ∧ e.stamp=rs.length ∧ e.query=true ∧
    e.lo=low (((winner ids rs e.link).map (·.allowance)).getD 0) ∧
    e.hi=big (((winner ids rs e.link).map (·.allowance)).getD 0) := by
  obtain ⟨l,hl,rfl⟩:=List.mem_map.mp h
  exact ⟨List.mem_range.mp hl,rfl,rfl,rfl,rfl⟩

theorem query_native (ids : List Nat) (st : State) (e : Event)
    (h:e∈queryEvents ids st.links) :
    e.lo=low ((ProcActualInput.allowances ids st)[e.link]!) ∧
    e.hi=big ((ProcActualInput.allowances ids st)[e.link]!) := by
  obtain ⟨hl,_,_,hlo,hhi⟩:=query_source ids st.links e h
  have hs:e.link<(ProcActualInput.allowances ids st).size := by
    rw [ProcActualInput.allowances_size]; exact hl
  have hv:=allowance_winner ids st e.link hl
  rw [Array.getElem?_eq_getElem hs] at hv
  have hv':=Option.some.inj hv
  rw [getElem!_pos (ProcActualInput.allowances ids st) e.link hs,hv']
  exact ⟨hlo,hhi⟩

theorem event_bounds (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈events ids rs) : e.link<ids.length*ids.length ∧ e.stamp≤rs.length ∧ e.lo<16777216 := by
  have hm: e∈writeEvents ids rs++queryEvents ids rs := (events_perm ids rs).mem_iff.mp h
  rcases List.mem_append.mp hm with hw|hq
  · obtain ⟨r,_,ht,_,hl,_⟩:=write_source ids rs e hw
    exact ⟨target_lt ids r e.link ht,Nat.le_of_lt (write_before_queries ids rs e hw),hl ▸ low_bound _⟩
  · obtain ⟨hk,hs,_,hl,_⟩:=query_source ids rs e hq
    exact ⟨hk,by omega,hl ▸ low_bound _⟩

end ZkFormal.NearV3.Candidates.ProcPriorEvents

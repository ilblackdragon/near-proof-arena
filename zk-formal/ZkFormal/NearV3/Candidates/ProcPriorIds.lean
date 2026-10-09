import ZkFormal.NearV3.Candidates.ProcPriorBudget
namespace ZkFormal.NearV3.Candidates.ProcPriorIds
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler ProcPriorLookup

structure Event where
  key : Nat
  isPublic : Bool
  ordinal : Nat
  result : Option Nat
  deriving DecidableEq, Repr

def publicEvents (ids : List Nat) : List Event :=
  ids.zipIdx.map fun (id,j)=>⟨id,true,j,some j⟩

def requestEvents (ids : List Nat) (rs : List LinkAllowance) : List Event :=
  rs.zipIdx.flatMap fun (r,j)=>
    [⟨r.sender,false,2*j,indexOf ids r.sender⟩,⟨r.receiver,false,2*j+1,indexOf ids r.receiver⟩]

def rank (e : Event) : Nat := if e.isPublic then 0 else 1

def precedes (a b : Event) : Bool := decide
  (a.key<b.key ∨ a.key=b.key ∧ (rank a<rank b ∨ rank a=rank b ∧ a.ordinal≤b.ordinal))

def events (ids : List Nat) (rs : List LinkAllowance) : List Event :=
  (publicEvents ids++requestEvents ids rs).mergeSort precedes

theorem precedes_trans (a b c : Event) (h1:precedes a b) (h2:precedes b c) : precedes a c := by
  simp only [precedes,decide_eq_true_eq] at *
  omega

theorem precedes_total (a b : Event) : precedes a b || precedes b a := by
  simp only [precedes,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem events_perm (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).Perm (publicEvents ids++requestEvents ids rs) := List.mergeSort_perm _ _

theorem events_sorted (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).Pairwise (fun a b=>precedes a b=true) :=
  List.pairwise_mergeSort precedes_trans precedes_total _

theorem request_length (ids : List Nat) (rs : List LinkAllowance) :
    (requestEvents ids rs).length=2*rs.length := by
  simp only [requestEvents,List.length_flatMap,List.length_cons,List.length_nil]
  simp [List.map_const',List.sum_replicate_nat,Nat.mul_comm]

theorem events_length (ids : List Nat) (rs : List LinkAllowance) :
    (events ids rs).length=ids.length+2*rs.length := by
  rw [(events_perm ids rs).length_eq,List.length_append,request_length]
  simp [publicEvents]

theorem public_source (ids : List Nat) (e : Event) (h:e∈publicEvents ids) :
    ids[e.ordinal]?=some e.key ∧ e.isPublic=true ∧ e.result=some e.ordinal := by
  obtain ⟨⟨id,j⟩,hj,rfl⟩:=List.mem_map.mp h
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.mp hj,rfl,rfl⟩

theorem request_source (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈requestEvents ids rs) :
    ∃ r j,rs[j]?=some r ∧ e.isPublic=false ∧ e.result=indexOf ids e.key ∧
      ((e.key=r.sender ∧ e.ordinal=2*j) ∨ (e.key=r.receiver ∧ e.ordinal=2*j+1)) := by
  obtain ⟨⟨r,j⟩,hj,he⟩:=List.mem_flatMap.mp h
  have hr:=List.mk_mem_zipIdx_iff_getElem?.mp hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> exact ⟨r,j,hr,rfl,rfl,by simp⟩

theorem known_request_first (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈requestEvents ids rs) (j : Nat) (hj:e.result=some j) :
    ∃ before after,ids=before++e.key::after ∧ j=before.length ∧ e.key∉before := by
  obtain ⟨_,_,_,_,hr,_⟩:=request_source ids rs e h
  rw [hr] at hj
  exact index_first ids e.key j hj

theorem unknown_request_absent (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈requestEvents ids rs) (hj:e.result=none) : e.key∉ids := by
  obtain ⟨_,_,_,_,hr,_⟩:=request_source ids rs e h
  rw [hr] at hj
  intro hm
  obtain ⟨j,he,_⟩:=ZkFormal.NearV3.Sched.indexOf_some_lt hm
  rw [hj] at he
  cases he

end ZkFormal.NearV3.Candidates.ProcPriorIds

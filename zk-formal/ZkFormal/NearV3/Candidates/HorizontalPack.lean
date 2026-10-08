import ZkFormal.NearV3.Candidates.HorizontalFamily

namespace ZkFormal.NearV3.Candidates.HorizontalPack
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra HorizontalFamily

abbrev Component := Air.Table×Trace Fp

def fallback : Component := (MerkleEmpty.table,{log:=fun _=>1,cell:=fun _ _ _=>0})

/-- Stack separate physical tables. Each component is evaluated at index zero;
its own clock is preserved, so lower-height tables are never padded. -/
def stack (xs : List Component) : Trace Fp :=
  {log:=fun t=>(xs.getD t fallback).2.log 0,
   cell:=fun t r c=>(xs.getD t fallback).2.cell 0 r c}

theorem focus_stack (xs : List Component) (t : Nat) :
    focus (stack xs) t=focus (xs.getD t fallback).2 0 := rfl

theorem stack_local (xs : List Component) (t : Nat) (x : Component) (pub : List Fp)
    (hx : xs.getD t fallback=x) (h : TableLocal x.1 x.2 0 pub) :
    TableLocal x.1 (stack xs) t pub := by
  have he := focus_stack xs t
  rw [hx] at he
  have hh := focus_local h
  rw [←he] at hh
  exact ⟨hh.log_ge,hh.log_le,hh.constr,hh.bits⟩

theorem stack_count (xs : List Component) (t : Nat) (x : Component) (pub : List Fp)
    (hx : xs.getD t fallback=x) (b : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount x.1.interactions (stack xs) t pub b sd m=
      tableBusCount x.1.interactions x.2 0 pub b sd m := by
  rw [←focus_count (stack xs) t pub x.1.interactions b sd m,focus_stack,hx,focus_count]

theorem bus_indexed (ts : List Air.Table) (tr : Trace Fp) (pub : List Fp)
    (b : Nat) (sd : Bool) (m : List Fp) (t : Nat) :
    busCount.go tr pub b sd m ts t=
      ((ts.zipIdx t).map (fun x=>tableBusCount x.1.interactions tr x.2 pub b sd m)).sum := by
  induction ts generalizing t with
  | nil => rfl
  | cons T ts ih => simp [busCount.go,List.zipIdx_cons,ih]

/-- Stacking does not alter any global bus multiplicity. -/
theorem stack_bus_count (xs : List Component) (pub : List Fp) (nb np b : Nat)
    (sd : Bool) (m : List Fp) :
    busCount (⟨xs.map Prod.fst,nb,np⟩ : Air) (stack xs) pub b sd m=count xs pub b sd m := by
  unfold busCount
  rw [bus_indexed]
  simp only [List.zipIdx_map,List.map_map]
  have hmap : (xs.zipIdx.map (fun p=>tableBusCount p.1.1.interactions (stack xs) p.2 pub b sd m))=
      xs.zipIdx.map (fun p=>tableBusCount p.1.1.interactions p.1.2 0 pub b sd m) := by
    apply List.map_congr_left
    intro p hp
    have hx := List.mem_zipIdx_iff_getElem?.mp hp
    have hd : xs.getD p.2 fallback=p.1 := by rw [List.getD_eq_getElem?_getD,hx]; rfl
    exact stack_count xs p.2 p.1 pub hd b sd m
  change (xs.zipIdx.map (fun p=>tableBusCount p.1.1.interactions (stack xs) p.2 pub b sd m)).sum=_
  rw [hmap]
  have hfst := List.zipIdx_map_fst 0 xs
  have h := congrArg (fun ys : List Component=>(ys.map (fun x=>tableBusCount x.1.interactions x.2 0 pub b sd m)).sum) hfst
  simpa only [List.map_map,count,Function.comp_def] using h

/-- Executable AIR witness assembly from component local proofs and their
joint natural-multiplicity balance. No common height is required here. -/
theorem stack_holds (xs : List Component) (pub : List Fp) (nb np : Nat)
    (hl : ∀x∈xs,TableLocal x.1 x.2 0 pub)
    (hb : ∀b m,count xs pub b true m=count xs pub b false m) :
    Holds (⟨xs.map Prod.fst,nb,np⟩ : Air) pub (stack xs) := by
  have hloc : ∀t (ht : t<xs.length),TableLocal xs[t].1 (stack xs) t pub := by
    intro t ht
    apply stack_local xs t xs[t] pub
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht]; rfl
    · exact hl xs[t] (List.getElem_mem ht)
  constructor
  · intro t ht
    have hh := hloc t (by simpa using ht)
    simpa only [List.getElem_map] using And.intro hh.log_ge hh.log_le
  · intro t ht r hr e he
    exact (hloc t (by simpa using ht)).constr r hr e (by simpa only [List.getElem_map] using he)
  · intro t ht r hr i hi e he
    exact (hloc t (by simpa using ht)).bits r hr i (by simpa only [List.getElem_map] using hi) e he
  · intro b m
    rw [stack_bus_count,stack_bus_count]
    exact hb b m

/-- Fuse the shared-clock components, then retain the separately clocked rest. -/
def packed (clock : Nat→Nat) (xs ys : List Component) : List Component :=
  (HorizontalTables.fuse (xs.map Prod.fst),HorizontalAssembly.trace clock xs)::ys

theorem packed_count (clock : Nat→Nat) (xs ys : List Component) (pub : List Fp)
    (b : Nat) (sd : Bool) (m : List Fp)
    (hc : ∀x∈xs,x.2.log 0=clock 0)
    (hcap : ∀x∈xs,x.1.maxLog≤22)
    (hcols : ∀x∈xs,∀e∈x.1.exprs,e.colBound≤x.1.width) :
    count (packed clock xs ys) pub b sd m=count (xs++ys) pub b sd m := by
  simp only [packed,count,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
  rw [HorizontalTraffic.trace_count clock xs 0 pub b sd m hc hcap hcols]

/-- Forward whole-family witness assembly, with the shared clock and native
component facts exposed explicitly rather than hidden as padding assumptions. -/
theorem packed_holds (clock : Nat→Nat) (xs ys : List Component) (pub : List Fp) (nb np : Nat)
    (hclock : 1≤clock 0 ∧ clock 0≤22)
    (hc : ∀x∈xs,x.2.log 0=clock 0)
    (hcap : ∀x∈xs,x.1.maxLog≤22)
    (hcols : ∀x∈xs,∀e∈x.1.exprs,e.colBound≤x.1.width)
    (hl : ∀x∈xs++ys,TableLocal x.1 x.2 0 pub)
    (hb : ∀b m,count (xs++ys) pub b true m=count (xs++ys) pub b false m) :
    Holds (⟨(packed clock xs ys).map Prod.fst,nb,np⟩ : Air) pub (stack (packed clock xs ys)) := by
  apply stack_holds
  · intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact HorizontalAssembly.trace_local clock xs 0 pub hclock hc hcap
        (fun x hx=>hl x (List.mem_append_left _ hx)) hcols
    · exact hl x (List.mem_append_right _ hx)
  · intro b m
    rw [packed_count clock xs ys pub b true m hc hcap hcols,
      packed_count clock xs ys pub b false m hc hcap hcols]
    exact hb b m

/-- The forward assembler targets the exact family with the certified8MiB
bound, rather than a shape-compatible surrogate. -/
theorem candidate_holds_with_bounds (clock : Nat→Nat) (xs ys : List Component) (pub : List Fp)
    (hx : xs.map Prod.fst=HorizontalTables.selected)
    (hy : ys.map Prod.fst=HorizontalAccounts.rest)
    (hclock : 1≤clock 0 ∧ clock 0≤22)
    (hc : ∀x∈xs,x.2.log 0=clock 0)
    (hcap : ∀x∈xs,x.1.maxLog≤22)
    (hcols : ∀x∈xs,∀e∈x.1.exprs,e.colBound≤x.1.width)
    (hl : ∀x∈xs++ys,TableLocal x.1 x.2 0 pub)
    (hb : ∀b m,count (xs++ys) pub b true m=count (xs++ys) pub b false m) :
    Holds HorizontalAccounts.air pub (stack (packed clock xs ys)) := by
  have h := packed_holds clock xs ys pub 67 202 hclock hc hcap hcols hl hb
  simpa only [packed,List.map_cons,hx,hy,HorizontalAccounts.air,HorizontalAccounts.tables] using h

/-- Static column and height bounds follow from the certified inventory,
leaving only honest runtime component facts to the native constructor. -/
theorem candidate_holds (clock : Nat→Nat) (xs ys : List Component) (pub : List Fp)
    (hx : xs.map Prod.fst=HorizontalTables.selected)
    (hy : ys.map Prod.fst=HorizontalAccounts.rest)
    (hclock : 1≤clock 0 ∧ clock 0≤22)
    (hc : ∀x∈xs,x.2.log 0=clock 0)
    (hl : ∀x∈xs++ys,TableLocal x.1 x.2 0 pub)
    (hb : ∀b m,count (xs++ys) pub b true m=count (xs++ys) pub b false m) :
    Holds HorizontalAccounts.air pub (stack (packed clock xs ys)) := by
  have hmem : ∀x∈xs,x.1∈HorizontalTables.selected := by
    intro x hx'
    rw [←hx]
    exact List.mem_map.mpr ⟨x,hx',rfl⟩
  apply candidate_holds_with_bounds clock xs ys pub hx hy hclock hc _ _ hl hb
  · intro x hx'
    have hh := of_decide_eq_true (List.mem_filter.mp (hmem x hx')).2
    omega
  · intro x hx' e he
    have hw := List.all_eq_true.mp PackedMerkleFamily.four_wf x.1
      (List.mem_filter.mp (hmem x hx')).1
    simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hw
    exact (hw.1.1.1.1 e he).1

end ZkFormal.NearV3.Candidates.HorizontalPack

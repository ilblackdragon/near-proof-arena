import ZkFormal.NearV3.Candidates.ProcPriorRecordRows
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordSemantics
open NearSpecV3.Scheduler NearSpec NearSpec.Bandwidth ProcPriorLookup ProcPriorRecordRows

def request (ids : List Nat) (r : Row) : Option ProcPriorIds.Event:=
  if r.limb=2 ∧ r.word<2 then
    some ⟨value r,false,2*r.index+r.word,indexOf ids (value r)⟩
  else none

def write (ids : List Nat) (r : Row) : Option ProcPriorEvents.Event:=
  if r.limb=2 ∧ r.word=2 then
    (target ids r.source).map fun l=>
      ⟨l,r.index,false,ProcPriorSummary.low r.source.allowance,ProcPriorSummary.big r.source.allowance⟩
  else none

theorem requestsFor (ids : List Nat) (r : LinkAllowance) (j : Nat) :
    (rowsFor r j).filterMap (request ids)=
      [⟨r.sender,false,2*j,indexOf ids r.sender⟩,
       ⟨r.receiver,false,2*j+1,indexOf ids r.receiver⟩] := by
  simp [rowsFor,request,value]

theorem writesFor (ids : List Nat) (r : LinkAllowance) (j : Nat) :
    (rowsFor r j).filterMap (write ids)=
      ((target ids r).map fun l=>ProcPriorEvents.Event.mk l j false
        (ProcPriorSummary.low r.allowance) (ProcPriorSummary.big r.allowance)).toList := by
  simp [rowsFor,write]
  cases ht:target ids r <;> simp [write,ht]

/-- Both ID queries survive unknown IDs and duplicate records. -/
theorem requests_exact (ids : List Nat) (rs : List LinkAllowance) :
    (rows rs).filterMap (request ids)=ProcPriorIds.requestEvents ids rs := by
  simp only [rows,List.filterMap_flatMap,requestsFor,ProcPriorIds.requestEvents]

/-- A write is emitted exactly when the native lookup selects both endpoints;
its original ordinal and full-u64 allowance summary are retained. -/
theorem writes_exact (ids : List Nat) (rs : List LinkAllowance) :
    (rows rs).filterMap (write ids)=ProcPriorEvents.writeEvents ids rs := by
  simp only [rows,List.filterMap_flatMap,writesFor,ProcPriorEvents.writeEvents]
  have eqv {α β : Type} (xs : List α) (f : α→Option β) :
      xs.flatMap (fun x=>(f x).toList)=xs.filterMap f := by
    induction xs with
    | nil => rfl
    | cons x xs ih => cases hx:f x <;> simp [hx,ih]
  exact eqv _ _

/-- Coarse aggregate join-stage capacity from the original source-byte budget.
This is a semantic resource bound, not a new accepted-domain requirement. -/
theorem aggregate_capacity (states : List State) (hn:states.length≤33)
    (hb:(states.map fun s=>37+24*s.links.length).sum≤2000000) :
    (states.map fun s=>1+(rows s.links).length).sum<2^22 := by
  have hbound : (states.map fun s=>1+(rows s.links).length).sum ≤
      (states.map fun s=>37+24*s.links.length).sum := by
    induction states with
    | nil => exact Nat.le_refl _
    | cons s ss ih =>
      simp only [List.map_cons,List.sum_cons,rows_length]
      simp only [List.length_cons] at hn
      have hbn:(ss.map fun s=>37+24*s.links.length).sum≤2000000 := by
        simp only [List.map_cons,List.sum_cons] at hb
        omega
      have hh:=ih (by omega) hbn
      simp only [rows_length] at hh
      omega
  omega

end ZkFormal.NearV3.Candidates.ProcPriorRecordSemantics

import ZkFormal.NearV3.Candidates.ProcPriorEvents
namespace ZkFormal.NearV3.Candidates.ProcPriorBudget
open NearSpec NearSpec.Bandwidth ProcPriorDecode ProcPriorEvents

structure Input where
  ids : List Nat
  bytes : Bytes
  state : State

def Valid (x : Input) : Prop := State.decode x.bytes=some x.state ∧ x.ids.length≤64

def byteRows (xs : List Input) : Nat := (xs.map (fun x=>x.bytes.length)).sum
def records (xs : List Input) : Nat := (xs.map (fun x=>x.state.links.length)).sum
def writeRows (xs : List Input) : Nat := (xs.map (fun x=>(events x.ids x.state.links).length)).sum
/-- Two original-ID queries per record, plus the current layout IDs. -/
def idRows (xs : List Input) : Nat := (xs.map (fun x=>2*x.state.links.length+x.ids.length)).sum

theorem original_charge (xs : List Input) (h:∀ x∈xs,Valid x) :
    byteRows xs=37*xs.length+24*records xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx:=decode_length x.bytes x.state (h x (by simp)).1
    have hi:=ih (fun y hy=>h y (by simp [hy]))
    simp only [byteRows,records,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem write_bound (xs : List Input) (h:∀ x∈xs,Valid x) :
    writeRows xs≤records xs+4096*xs.length := by
  induction xs with
  | nil => simp [writeRows,records]
  | cons x xs ih =>
    have hn: x.ids.length*x.ids.length≤4096 := by
      have hl: x.ids.length≤64 := (h x (by simp)).2
      exact Nat.mul_le_mul hl hl
    have hx:=events_length x.ids x.state.links
    have hi:=ih (fun y hy=>h y (by simp [hy]))
    simp only [writeRows,records,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem id_bound (xs : List Input) (h:∀ x∈xs,Valid x) :
    idRows xs≤2*records xs+64*xs.length := by
  induction xs with
  | nil => simp [idRows,records]
  | cons x xs ih =>
    have hn:= (h x (by simp)).2
    have hi:=ih (fun y hy=>h y (by simp [hy]))
    simp only [idRows,records,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

/-- Concrete row feasibility of the isolated streams; this is not a width,
constraint, whole-family admission, or accepted byte-charge theorem. -/
theorem capacities (xs : List Input) (h:∀ x∈xs,Valid x)
    (hk:xs.length≤33) (hb:byteRows xs≤2000000) :
    records xs≤83333 ∧ writeRows xs≤218501 ∧ idRows xs≤168778 ∧
    byteRows xs+xs.length+1≤2^22 ∧ writeRows xs+xs.length+1≤2^22 ∧ idRows xs+1≤2^22 := by
  have hc:=original_charge xs h
  have hw:=write_bound xs h
  have hi:=id_bound xs h
  omega

end ZkFormal.NearV3.Candidates.ProcPriorBudget

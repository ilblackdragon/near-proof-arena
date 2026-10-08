import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecAssignmentReads
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBase
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecExtraColumns SchedSetAll

/-- All six base fields are final assignments in the actual executable record. -/
theorem base_fields (I : Input) (present : Bool) (n k f g p bpo bpr a b : Nat)
    (inst tail : List (Nat×Nat)) (ht:Tail tail) (c : Nat)
    (hc:c∈[rs,al,gb,srcC,hasC,useC]) :
    (recordRow I present n k f g p bpo bpr inst (baseExtra n k f g a b++tail))[c]! =
      lookup (baseExtra n k f g a b) c 0 := by
  have hp:c∈protectedColumns := by simp only [protectedColumns,List.mem_append]; exact Or.inl (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at *; grind)
  have hw:c<Codec.width := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ hw,SchedSetAll.append,SchedSetAll.append,tail_preserves _ ht _ _ hp]
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [baseExtra,lookup,List.foldl_cons,rs,al,gb,srcC,hasC,useC]
theorem sender_register (I : Input) (present : Bool) (n k g p bpo bpr a b : Nat)
    (inst tail : List (Nat×Nat)) (ht:Tail tail) (i : Nat) (hi:i<8) :
    (recordRow I present n k 0 g p bpo bpr inst (baseExtra n k 0 g a b++tail))[prbit i]! =
      (bytesLE (I.ids.getD (k/n) 0) 8).getD (g+i) 0 := by
  apply ProcPriorCodecAssignmentReads.record_id _ _ _ _ _ _ _ _ _ _ _ hi
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Prod.fst,rs,al,gb,srcC,hasC,useC,prbit] <;> omega
  · intro he
    apply disjoint q.1 (ht q hq)
    rw [he]
    apply List.mem_append_right
    exact List.mem_map_of_mem (f:=prbit) (List.mem_range.mpr hi)

theorem counters (I : Input) (present : Bool) (n k f g p bpo bpr a b : Nat)
    (inst tail : List (Nat×Nat)) (ht:Tail tail) :
    let row := recordRow I present n k f g p bpo bpr inst (baseExtra n k f g a b++tail)
    row[srcC]! = k/n ∧ row[useC]! = k%n ∧ row[hasC]! = (if k%n+1=n then 1 else 0) ∧
      row[rs]! = (if f=0 ∧ g=0 then 1 else 0) ∧ row[al]! = a ∧ row[gb]! = b := by
  dsimp only
  have h:=base_fields I present n k f g p bpo bpr a b inst tail ht
  rw [h srcC (by simp),h useC (by simp),h hasC (by simp),
    h rs (by simp),h al (by simp),h gb (by simp)]
  simp [baseExtra,lookup,List.foldl_cons,rs,al,gb,srcC,hasC,useC]

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBase

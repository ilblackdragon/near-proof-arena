import ZkFormal.NearV3.Candidates.ProcReplayChain
import ZkFormal.NearV3.Candidates.ExceptRange
namespace ZkFormal.NearV3.Candidates.ProcReplayShape
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcReplayChain

def Indexed (es : Array Entry) (n : Nat) : Prop :=
  es.size=n ∧ ∀i,i<es.size → es[i]!.x=i

theorem indexed_push (es : Array Entry) (n : Nat) (h : Indexed es n) (e : Entry)
    (he : e.x=n) : Indexed (es.push e) (n+1) := by
  refine ⟨by simp [h.1],?_⟩
  intro i hi
  by_cases hl : i<es.size
  · rw [getElem!_pos (es.push e) _ hi,Array.getElem_push_lt hl,←getElem!_pos es i hl]
    exact h.2 i hl
  · have hei : i=es.size := by simp only [Array.size_push] at hi; omega
    subst i
    rw [getElem!_pos (es.push e) _ hi,Array.getElem_push_eq,he,h.1]

abbrev EntryAcc := Array Nat × Array Nat × Array Nat × Array Nat ×
  Array (Array MOp) × Array (Array MOp) × Array (Array MOp) ×
  Array (Nat×Nat×Nat×Nat) × Array (Array Bool) × Nat × Array Entry

def EntryInv (n : Nat) (s : EntryAcc) : Prop := Indexed s.2.2.2.2.2.2.2.2.2.2 n

def Shape (rd : RoundD) : Prop :=
  0<rd.Lr ∧ Indexed rd.entries.toArray rd.Lr

def Shapes (s : ReplayAcc) : Prop := ∀rd∈s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList,Shape rd

theorem check_true (b : Bool) (msg : String) (h : check b msg=.ok ()) : b=true := by
  unfold check at h
  split at h
  · assumption
  · cases h

set_option maxHeartbeats 1000000 in
/-- Successful native replay produces nonempty rounds with exact entry counts
and entry indices, by invariants of both actual nested loops. -/
theorem run_shapes (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∀rd∈R.rounds,Shape rd := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    change Shapes _
    refine ExceptLoop.invariant (α := Round) (ε := String) ?xs ?f Shapes ?step ?b _ ?init ?loop
    case loop => assumption
    case init => simp [Shapes]
    case step =>
      intro rd hrd s hs out ho
      repeat first | cases ho | split at ho
      all_goals
        rename_i entryOut hentry
        have hc : check (rd.bucket.length≥1 && rd.bucket.length<16384) "bucket size"=.ok () := by assumption
        have hc' : 0<rd.bucket.length := by
          have hh := check_true _ _ hc
          simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
          omega
        have hi : EntryInv rd.bucket.length entryOut := by
          refine ExceptRange.range_invariant (ε := String) ?ef EntryInv _ ?estep ?eb _ ?einit ?eloop
          case eloop => exact hentry
          case einit => simp [EntryInv,Indexed]
          case estep =>
            intro i hil st hst eo heo
            repeat first | cases heo | split at heo
            all_goals repeat first | cases heo | split at heo
            all_goals
              refine ⟨_,rfl,?_⟩
              exact indexed_push _ _ hst _ rfl
        simp only [ExceptLoop.StepInv,Shapes,Array.toList_push,List.mem_append,List.mem_singleton]
        intro r hr
        rcases hr with hr|rfl
        · exact hs r hr
        · exact ⟨hc',by simpa [EntryInv] using hi⟩
end ZkFormal.NearV3.Candidates.ProcReplayShape

import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
import ZkFormal.NearV3.Candidates.ProcPriorCodecExtraColumns
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecExtraColumns

def record (I : Input) (R : Run) (present : Bool) (inst extra : List (Nat×Nat))
    (kk f gg : Nat) : Array Nat :=
  let afinF (k : Nat) := (R.segs.getD k default).vfin
  let p := 5+24*kk+8*f+gg
  let bpo := if f<2 then idByte I.ids kk (8*f+gg) else if gg<3 then afinF kk/256^gg%256 else 0
  let bpr := if ¬present then 0 else if f<2 then bpo else (Array.replicate (R.n*R.n) 0)[kk]!/256^gg%256
  ProcPriorCodecAssignments.recordRow I present R.n kk f gg p bpo bpr inst extra

/-- Every successful executable record step appends exactly its native record;
all later assignments stay within the checked tail column inventory. -/
theorem successful_row (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd : List (Nat×Nat)) (inst : List (Nat×Nat)) (kk f gg : Nat) (st out : State) (hf:f<3) (hg:gg<8)
    (h:step I R present gbA fwd inst kk f gg st=.ok (.yield out)) :
    ∃tail,Tail tail ∧ out.1=st.1.push
      (record I R present inst (baseExtra R.n kk f gg (b2n I.allowed[kk]!) gbA[kk]!++tail) kk f gg) := by
  have hcf:f=0∨f=1∨f=2 := by omega
  have hcg:gg=0∨gg=1∨gg=2∨gg=3∨gg=4∨gg=5∨gg=6∨gg=7 := by omega
  rcases hcf with rfl|rfl|rfl
  all_goals rcases hcg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,bind,Except.bind,pure,Except.pure] at h
  iterate 4
    all_goals repeat (first | contradiction | subst out | simp only [Except.ok.injEq,ForInStep.yield.injEq] at h | simp [Gen.check,bind,Except.bind,pure,Except.pure] at h | split at h)
  all_goals try subst out
  all_goals try (simp [record,List.append_assoc, *]; refine ⟨_,?_,rfl⟩)
  all_goals try (repeat (first | apply tail_append | exact start_tail _ _ | exact prior_tail _ _ | exact allowance_tail _ _ _ _ _ _ _ _ | exact wrap_tail _ _ | exact compare_tail _ _ | exact carry_tail _ | exact end_tail _ _ _ _ _ _ _ _ | exact forward_tail _ _ _ _))
  all_goals try simp [Tail]

/-- The executable iteration never terminates its enclosing loop early. -/
theorem not_done (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd : List (Nat×Nat)) (inst : List (Nat×Nat)) (kk f gg : Nat) (st out : State)
    (hf:f<3) (hg:gg<8) :
    step I R present gbA fwd inst kk f gg st ≠ .ok (.done out) := by
  intro h
  have hcf:f=0∨f=1∨f=2 := by omega
  have hcg:gg=0∨gg=1∨gg=2∨gg=3∨gg=4∨gg=5∨gg=6∨gg=7 := by omega
  rcases hcf with rfl|rfl|rfl
  all_goals rcases hcg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,bind,Except.bind,pure,Except.pure] at h
  iterate 4
    all_goals repeat (first | contradiction | simp [Gen.check,bind,Except.bind,pure,Except.pure] at h | split at h)

theorem successful (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd : List (Nat×Nat)) (inst : List (Nat×Nat)) (kk f gg : Nat) (st : State)
    (result : ForInStep State) (hf:f<3) (hg:gg<8)
    (h:step I R present gbA fwd inst kk f gg st=.ok result) :
    ∃out, result=.yield out ∧ ∃tail,Tail tail ∧ out.1=st.1.push
      (record I R present inst (baseExtra R.n kk f gg (b2n I.allowed[kk]!) gbA[kk]!++tail) kk f gg) := by
  cases result with
  | done out => exact False.elim (not_done I R present gbA fwd inst kk f gg st out hf hg h)
  | yield out => exact ⟨out,rfl,successful_row I R present gbA fwd inst kk f gg st out hf hg h⟩

end ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows

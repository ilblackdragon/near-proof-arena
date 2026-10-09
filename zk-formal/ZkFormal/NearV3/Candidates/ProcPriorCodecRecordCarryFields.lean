import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordCarryFields
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecExtraColumns SchedSetAll
open ProcPriorCodecNativeHash

def columns : List Nat := [rs,al,gb,srcC,hasC,useC]
def carryColumns : List Nat := [al,gb,srcC,hasC,useC]

theorem base_overwrites (n k f g a b c v : Nat) (hc:c∈columns) :
    lookup (baseExtra n k f g a b) c v=lookup (baseExtra n k f g a b) c 0 := by
  simp only [columns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [baseExtra,lookup,rs,al,gb,srcC,hasC,useC]

theorem row (I : Input) (present : Bool) (n k f g p bpo bpr a b : Nat)
    (inst tail : List (Nat×Nat)) (ht:Tail tail) (c : Nat) (hc:c∈columns) :
    (recordRow I present n k f g p bpo bpr inst (baseExtra n k f g a b++tail))[c]! =
      lookup (baseExtra n k f g a b) c 0 := by
  have hw:c<Codec.width := (by decide +kernel : ∀c∈columns,c<Codec.width) c hc
  have hp:c∈protectedColumns := (by decide +kernel : ∀c∈columns,c∈protectedColumns) c hc
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ hw,append,append,tail_preserves tail ht c _ hp,base_overwrites _ _ _ _ _ _ _ _ hc]

theorem actual (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : ProcPriorCodecRecordStep.State)
    (hf:f<3) (hg:g<8)
    (h:ProcPriorCodecRecordStep.step I R present gbA fwd (instanceCells I R present vidV) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ ∀c∈columns,
      a[c]! = lookup (baseExtra R.n k f g (b2n I.allowed[k]!) gbA[k]!) c 0 := by
  obtain ⟨tail,ht,ha⟩:=ProcPriorCodecStepRows.successful_row I R present gbA fwd
    (instanceCells I R present vidV) k f g s out hf hg h
  refine ⟨_,ha,?_⟩
  intro c hc
  unfold ProcPriorCodecStepRows.record
  exact row _ _ _ _ _ _ _ _ _ _ _ _ _ ht c hc

theorem position (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀c∈columns,out.rows[5+24*k+8*f+g]![c]! =
      lookup (baseExtra R.n k f g (b2n I.allowed[k]!) gbA[k]!) c 0 := by
  apply ProcCodecGeneratedRecordPosition.property I R present vidV gbA fwd out h k f g hk hf hg
    (fun a=>∀c∈columns,a[c]! = lookup (baseExtra R.n k f g (b2n I.allowed[k]!) gbA[k]!) c 0)
  intro before after hs
  exact actual I R present gbA fwd vidV k f g before after hf hg hs

theorem carry_same (n k f g f' g' a b c : Nat) (hc:c∈carryColumns) :
    lookup (baseExtra n k f g a b) c 0=lookup (baseExtra n k f' g' a b) c 0 := by
  simp only [carryColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  all_goals simp [baseExtra,lookup,rs,al,gb,srcC,hasC,useC]

theorem start (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gbA fwd=.ok out)
    (k : Nat) (hk:k<R.n*R.n) : out.rows[5+24*k]![rs]! = 1 := by
  have hh:=position I R present vidV gbA fwd out h k 0 0 hk (by decide) (by decide) rs (by simp [columns])
  simpa [baseExtra,lookup,rs,al,gb,srcC,hasC,useC] using hh

theorem actual_gates (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : ProcPriorCodecRecordStep.State)
    (hk:k<R.n*R.n) (hf:f<3) (hg:g<8)
    (h:ProcPriorCodecRecordStep.step I R present gbA fwd (instanceCells I R present vidV) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[kR]! = 1 ∧ a[rend]! = (if f=2 ∧ g=7 then 1 else 0) ∧
      a[ekl]! = (if k+1=R.n*R.n then 1 else 0) := by
  obtain ⟨a,ha,hact,hR,hH,hZ,hA,hFA,hgval,hig,he7,hkval,hNN,hik,hekl,hhp,hsj,htau,hit,hzt⟩:=
    ProcPriorCodecRecordZeroRows.actual I R present gbA fwd vidV k f g s out hf hg h
  obtain ⟨b,hb,hki,hlo,hhi,hend,hstart,hzero⟩:=
    ProcPriorCodecRecordIndexRows.actual I R present gbA fwd vidV k f g s out hk hf hg h
  have heq:b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  refine ⟨a,ha,hR,?_,hekl⟩
  rw [hend,hFA,he7]
  by_cases hf2:f=2 <;> by_cases hg7:g=7 <;> simp [hf2,hg7]

theorem gates (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    out.rows[5+24*k+8*f+g]![kR]! = 1 ∧
    out.rows[5+24*k+8*f+g]![rend]! = (if f=2 ∧ g=7 then 1 else 0) ∧
    out.rows[5+24*k+8*f+g]![ekl]! = (if k+1=R.n*R.n then 1 else 0) := by
  apply ProcCodecGeneratedRecordPosition.property I R present vidV gbA fwd out h k f g hk hf hg
    (fun a=>a[kR]! = 1 ∧ a[rend]! = (if f=2 ∧ g=7 then 1 else 0) ∧
      a[ekl]! = (if k+1=R.n*R.n then 1 else 0))
  intro before after hs
  exact actual_gates I R present gbA fwd vidV k f g before after hk hf hg hs

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordCarryFields

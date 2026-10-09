import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalAdditionGroups
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedPriorZero
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

def equations : List Expr := (ProcPriorCodecActual.additions.drop 10).take 1

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State)
    (hk:k<R.n*R.n) (hf:f<3) (hg:g<8)
    (h:step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈equations,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  have heq : equations=[.mul (ZkFormal.Chacha.Table.E.c fA) (ZkFormal.Chacha.Table.E.c bpre)] := by decide +kernel
  by_cases hf2:f=2
  · subst f
    obtain ⟨a,ha,hzero,_⟩:=ProcPriorCodecAllowanceData.cells I R present gb fwd (instanceCells I R present vidV) k g s out hg hk h
    refine ⟨a,ha,?_⟩
    rw [heq]
    intro e he
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
    subst e
    change Fp.ofNat a[fA]!*Fp.ofNat a[bpre]! =0
    rw [hzero]; change _*(0:Fp)=0; grind only
  · obtain ⟨a,ha,_,_,_,_,_,hfa,_⟩:=ProcPriorCodecRecordZeroRows.actual I R present gb fwd vidV k f g s out hf hg h
    have hz:a[fA]! =0 := by simpa only [if_neg hf2] using hfa
    refine ⟨a,ha,?_⟩
    rw [heq]
    intro e he
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
    subst e
    change Fp.ofNat a[fA]!*Fp.ofNat a[bpre]! =0
    rw [hz]; change (0:Fp)*_=0; grind only

theorem record (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  unfold ProcCodecPhysicalRows.rowEnvAt
  apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h k f g hk hf hg
    (fun a=>∀e∈equations,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!)
      (if 5+24*k+8*f+g+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*f+g+1]![c]! else fun _=>0)
      (if 5+24*k+8*f+g=0 then 1 else 0) 0 1)=0)
  intro before after hs
  exact actual I R present gb fwd vidV k f g before after hk hf hg hs _ _ _ _

theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn:0<R.n)
    (r : Nat) (hr:r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  exact ProcCodecPhysicalAdditionGroups.active_of_records I R present vidV gb fwd out h hn equations
    (fun _ he=>List.mem_of_mem_drop (List.mem_of_mem_take he))
    (fun k f g hk hf hg=>record I R present vidV gb fwd out h k f g hk hf hg) r hr

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn1:0<R.n) (hn:R.n≤64)
    (t r : Nat) (hr:r<2^22) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  obtain ⟨hne,hcap⟩:=ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn
  intro e he
  by_cases ha:r<out.rows.size
  · have hp:e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
    rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r ha pub e hp]
    exact active I R present vidV gb fwd out h hn1 r ha e he
  · apply (ProcCodecPhysicalPadding.physical_local out.rows hne t r (by omega) hr pub).1 e
    unfold ProcPriorCodecActual.table ProcPriorCodecActual.constraints
    exact List.mem_append_right _ (List.mem_of_mem_drop (List.mem_of_mem_take he))
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedPriorZero

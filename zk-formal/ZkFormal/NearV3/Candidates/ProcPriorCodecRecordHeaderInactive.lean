import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordPhase
import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInactive
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordHeaderInactive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecStepRows ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f g : Nat) (s out : State)
    (hf : f<3) (hg : g<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f g s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈ProcPriorCodecHeaderInactive.headerGroup,
      e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨tail,ht,hr⟩ := successful_row I R present gb fwd (instanceCells I R present vid) k f g s out hf hg h
  let a := record I R present (instanceCells I R present vid)
    (baseExtra R.n k f g (b2n I.allowed[k]!) gb[k]!++tail) k f g
  have hh : a[act]! =1 ∧ a[kR]! =1 ∧ a[kH]! =0 ∧ a[kZ]! =0 ∧ a[kA]! =0 ∧
      a[kF]! =0 ∧ a[ehp]! =0 ∧ a[fS]! =(if f=0 then 1 else 0) ∧
      a[fR]! =(if f=1 then 1 else 0) ∧ a[fA]! =(if f=2 then 1 else 0) := by
    exact ProcPriorCodecRecordKind.flags I R present vid k f g _ _ _ _ _ tail ht
  obtain ⟨ha,hR,hH,hZ,hA,hF,hE,hS,hFR,hFA⟩ := hh
  refine ⟨a,hr,ProcPriorCodecHeaderInactive.inactive _ nxt first last trans ?_ ?_ ?_⟩
  · rw [hF]; rfl
  · rw [hH]; rfl
  · rw [hE]; rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordHeaderInactive

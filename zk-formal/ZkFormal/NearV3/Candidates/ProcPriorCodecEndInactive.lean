import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecEndInactive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp) (hr : cur rend=0) :
    ∀e∈(cRec.drop 54).take 5,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.forall_mem_cons]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,hr]
  grind

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f g : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) (hnot : f≠2 ∨ g≠7)
    (h : step I R present gb fwd (instanceCells I R present vid) k f g s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cRec.drop 54).take 5,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,ha,_,_,_,hr,_⟩ := ProcPriorCodecRecordIndexRows.actual I R present gb fwd vid k f g s out hk hf hg h
  obtain ⟨b,hb,_,_,_,_,_,hfa,_,_,he7,_⟩ := ProcPriorCodecRecordZeroRows.actual I R present gb fwd vid k f g s out hf hg h
  have he : b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  have hz : a[rend]! =0 := by
    rw [hr,hfa,he7]
    rcases hnot with hnot|hnot
    · simp only [if_neg hnot,Nat.zero_mul]
    · simp only [if_neg hnot,Nat.mul_zero]
  refine ⟨a,ha,inactive _ nxt first last trans ?_⟩
  rw [hz]; rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecEndInactive

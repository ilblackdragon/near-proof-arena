import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeControls
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecControlLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecEndArithmetic

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cRec.drop 59).take 1 ++ (cRec.drop 63).take 1,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,har,hfw,hcg⟩ := ProcPriorCodecNativeControls.actual I R present gb fwd vidV k f gg s out hk hf hg h
  have hfwe : Fp.ofNat a[fwg]! =Fp.ofNat a[rend]!*Fp.ofNat a[zt]! := by rw [hfw,cast_mul]
  have hcge : Fp.ofNat a[cg]! =Fp.ofNat a[fA]!*Fp.ofNat a[e2]!+Fp.ofNat a[fwg]! := by rw [hcg,cast_add,cast_mul]
  refine ⟨a,har,?_⟩
  simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl
  all_goals simp only [ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    Expr.evalWith,ProcPriorCells.env,hfwe,hcge]
  all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecControlLocal

import ZkFormal.NearV3.Candidates.ProcPriorCodecCompareRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecCompareLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecEndArithmetic

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k gg : Nat) (s out : State) (hk : k<R.n*R.n) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k 2 gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cRec.drop 49).take 3,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  by_cases hg2 : gg=2
  · subst gg
    obtain ⟨a,har,hx,hy,hb⟩ := ProcPriorCodecCompareRows.cells I R present gb fwd vidV k s out hk h
    refine ⟨a,har,?_⟩
    simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
      List.mem_cons,List.mem_nil_iff,or_false]
    intro e heq
    rcases heq with rfl|rfl|rfl
    all_goals simp only [mul3,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hx,hy,hb,cast_add]
    all_goals grind only
  · obtain ⟨a,har,_,_,_,_,_,he⟩ := ProcPriorCodecAllowanceData.cells I R present gb fwd
      (instanceCells I R present vidV) k gg s out hg hk h
    have hz : a[e2]! =0 := by simpa only [if_neg hg2] using he
    refine ⟨a,har,?_⟩
    simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
      List.mem_cons,List.mem_nil_iff,or_false]
    intro e heq
    rcases heq with rfl|rfl|rfl
    all_goals simp only [mul3,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hz,show Fp.ofNat 0=(0:Fp) from rfl]
    all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecCompareLocal

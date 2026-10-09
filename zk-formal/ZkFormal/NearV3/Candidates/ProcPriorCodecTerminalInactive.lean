import ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalGates
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalInactive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

def equations : List Expr := (cRec.drop 25).take 5 ++ (cRec.drop 44).take 4 ++ (cRec.drop 52).take 2

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp)
    (hf : cur fA=1) (hr : cur rend=1) (he : cur e2=0) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [equations,cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.forall_mem_append,List.forall_mem_cons]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,hf,hr,he,mul3,notE,ZkFormal.Chacha.Table.E.k]
  grind

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k : Nat) (s out : State) (hk : k<R.n*R.n)
    (h : step I R present gb fwd (instanceCells I R present vid) k 2 7 s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈equations,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,ha,hf,hr,he⟩ := ProcPriorCodecTerminalGates.actual I R present gb fwd vid k s out hk h
  refine ⟨a,ha,inactive _ nxt first last trans ?_ ?_ ?_⟩
  · rw [hf]; rfl
  · rw [hr]; rfl
  · rw [he]; rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalInactive

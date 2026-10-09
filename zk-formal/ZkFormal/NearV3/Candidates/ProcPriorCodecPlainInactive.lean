import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainAdjacent
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPlainInactive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecPlainStep

def equations : List Expr := (cRec.drop 25).take 8 ++ (cRec.drop 44).take 4 ++ (cRec.drop 49).take 10

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp)
    (hf : cur fA=0) (hr : cur rend=0) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [equations,cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.forall_mem_append,List.forall_mem_cons]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,hf,hr,mul3,notE,ZkFormal.Chacha.Table.E.k]
  grind

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State) (hf : f<2)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈equations,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  rw [step_eq I R present gb fwd _ k f gg s hf] at h
  cases h
  refine ⟨_,rfl,?_⟩
  obtain ⟨_,_,_,_,_,hA,_,hR⟩ := ProcPriorCodecPlainAdjacent.cells I R present gb vidV k f gg hf
  apply inactive
  · rw [hA]; rfl
  · rw [hR]; rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecPlainInactive

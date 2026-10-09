import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardRows
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cTrl.drop 13).take 2,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,ha,hw⟩ := ProcPriorCodecForwardRows.actual I R present gb fwd vidV k f gg s out hk hf hg h
  refine ⟨a,ha,?_⟩
  have he : (cTrl.drop 13).take 2 = [
    .mul (ZkFormal.Chacha.Table.E.c fwg) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c pm0) (ZkFormal.Chacha.Table.E.c klo)),
    .mul (ZkFormal.Chacha.Table.E.c fwg) (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.c pm1) (ZkFormal.Chacha.Table.E.c khi))] := by decide +kernel
  rw [he]
  simp only [List.forall_mem_cons,List.forall_mem_nil,List.not_mem_nil,false_implies,forall_const,Expr.evalWith,ProcPriorCells.env,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub]
  rcases hw with hz|⟨h0,h1⟩
  · simp only [hz,show Fp.ofNat 0=(0:Fp) from rfl]
    grind only
  · simp only [h0,h1]
    grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardLocal

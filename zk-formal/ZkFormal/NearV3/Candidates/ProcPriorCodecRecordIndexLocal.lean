import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecEndArithmetic

def equations : List Expr := cRec.take 1 ++ (cRec.drop 11).take 1 ++ (cRec.drop 33).take 2

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈equations,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,har,hidx,hlo,hhi,hend,hstart,hgzero⟩ :=
    ProcPriorCodecRecordIndexRows.actual I R present gb fwd vidV k f gg s out hk hf hg h
  have hidxN : a[kidx]! =a[klo]!+256*a[khi]! := by rw [hidx,hlo,hhi]; omega
  have hidxF : Fp.ofNat a[kidx]! =Fp.ofNat a[klo]!+256*Fp.ofNat a[khi]! := by
    rw [hidxN,cast_add,cast_mul]; rfl
  have hendF : Fp.ofNat a[rend]! =Fp.ofNat a[fA]!*Fp.ofNat a[e7]! := by rw [hend,cast_mul]
  have hgF : Fp.ofNat a[rs]!*Fp.ofNat a[Codec.g]! =0 := by
    rw [←cast_mul,hgzero]; rfl
  refine ⟨a,har,?_⟩
  simp only [equations,cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl
  all_goals simp only [notE,mul3,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,show Fp.ofNat 256=(256:Fp) from rfl]
  · rw [hidxF]; grind only
  · rw [hendF]; grind only
  · rcases hstart with hs|hs
    all_goals simp only [hs,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
    all_goals grind only
  · grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexLocal

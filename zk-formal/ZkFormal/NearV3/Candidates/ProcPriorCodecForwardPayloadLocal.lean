import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLoop
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecEndArithmetic ProcPriorCodecForwardPayloadRows

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (hbound : f=2→gg=7→R.tau=0→demand fwd k<16777216)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈(cRec.drop 60).take 3,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,har,hd⟩ := ProcPriorCodecForwardPayloadRows.actual I R present gb fwd vidV k f gg s out hk hf hg h
  refine ⟨a,har,?_⟩
  rcases hd with hz|⟨hf2,hg7,ht,hx,hy,hbit,h0,h1,h2⟩
  · simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
      List.mem_cons,List.mem_nil_iff,or_false]
    intro e heq
    rcases heq with rfl|rfl|rfl
    all_goals simp only [ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hz,show Fp.ofNat 0=(0:Fp) from rfl]
    all_goals grind only
  · have hybytes : a[cy]! =a[fb 0]! +256*a[fb 1]! +65536*a[fb 2]! := by
      rw [hy,h0,h1,h2]
      have he := ProcPriorCodecAccumulatorLoop.low24_digits (demand fwd k)
      rw [Nat.mod_eq_of_lt (hbound hf2 hg7 ht)] at he
      exact he.symm
    have hcx : Fp.ofNat a[cx]! =Fp.ofNat a[gfin]! +Fp.ofNat a[Codec.gb]! := by rw [hx,cast_add]
    have hcy : Fp.ofNat a[cy]! =Fp.ofNat a[fb 0]! +(256:Fp)*Fp.ofNat a[fb 1]! +(65536:Fp)*Fp.ofNat a[fb 2]! := by
      rw [hybytes,cast_add,cast_add,cast_mul,cast_mul]
      rfl
    simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
      List.mem_cons,List.mem_nil_iff,or_false]
    intro e heq
    rcases heq with rfl|rfl|rfl
    all_goals simp only [ftE,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,hcx,hcy,hbit,
      show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 256=(256:Fp) from rfl,
      show Fp.ofNat 65536=(65536:Fp) from rfl]
    all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadLocal

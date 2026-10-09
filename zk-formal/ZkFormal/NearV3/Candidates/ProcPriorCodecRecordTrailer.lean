import ZkFormal.NearV3.Candidates.ProcPriorCodecForwardRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTrailer
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecStepRows

theorem record_trailer (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz : cur kZ=0) (ha : cur kA=0)
    (hw : cur fwg=0 ∨ (cur pm0=cur klo ∧ cur pm1=cur khi)) :
    ∀e∈cTrl,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [cTrl,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_map]
  rcases hw with hf|⟨h0,h1⟩
  all_goals simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.sub,hz,ha, *, mul3,notE,ZkFormal.Chacha.Table.E.k]
  all_goals grind

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈cTrl,
      e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨tail,ht,hr⟩ := successful_row I R present gb fwd (instanceCells I R present vidV) k f gg s out hf hg h
  let r := record I R present (instanceCells I R present vidV)
    (baseExtra R.n k f gg (b2n I.allowed[k]!) gb[k]!++tail) k f gg
  have hr' : out.1=s.1.push r := hr
  obtain ⟨a,har,hbits⟩ := ProcPriorCodecForwardRows.actual I R present gb fwd vidV k f gg s out hk hf hg h
  have he : a=r := Array.push_inj_right.mp (har.symm.trans hr')
  subst a
  have hflags : r[act]! =1 ∧ r[kR]! =1 ∧ r[kH]! =0 ∧ r[kZ]! =0 ∧ r[kA]! =0 ∧
      r[kF]! =0 ∧ r[ehp]! =0 ∧ r[fS]! =(if f=0 then 1 else 0) ∧
      r[fR]! =(if f=1 then 1 else 0) ∧ r[fA]! =(if f=2 then 1 else 0) := by
    dsimp only [r,record]
    exact ProcPriorCodecRecordKind.flags I R present vidV k f gg _ _ _ _ _ tail ht
  obtain ⟨_,hR,hH,hZ,hA,hF,_,hS,hRc,hFA⟩ := hflags
  refine ⟨r,hr',record_trailer _ nxt first last trans ?_ ?_ ?_⟩
  · rw [hZ]; rfl
  · rw [hA]; rfl
  · rcases hbits with hz|⟨h0,h1⟩
    · left; rw [hz]; rfl
    · right; exact ⟨congrArg Fp.ofNat h0,congrArg Fp.ofNat h1⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTrailer

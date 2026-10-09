import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolean
open ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecRecordBoolCells

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f gg : Nat) (s out : State)
    (hcb:s.2.2.2.2.2≤1) (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vid) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ ∀c∈columns,a[c]! ≤1 := by
  have hff : f=0 ∨ f=1 ∨ f=2 := by omega
  have hgg : gg=0 ∨ gg=1 ∨ gg=2 ∨ gg=3 ∨ gg=4 ∨ gg=5 ∨ gg=6 ∨ gg=7 := by omega
  rcases hff with rfl|rfl|rfl
  all_goals rcases hgg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure,getElem!_pos,hk] at h
  iterate 4
    all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals try (simp only [Except.ok.injEq,ForInStep.yield.injEq] at h; subst out)
  all_goals refine ⟨_,rfl,?_⟩
  all_goals intro c hc
  all_goals apply ProcPriorCodecRecordBoolCells.row I R present vid _ _ _ _ _ _ _ ?_ c hc
  all_goals simp [Gates,columns,ProcPriorCodecSideKind.scalarBits,recBoolCols,baseExtra,startExtra,allowanceExtra,priorExtra,
    wrapExtra,compareExtra,carryExtra,endExtra,forwardExtra,
    ap,apost,big,lowf,wt,nzb,ib,ig2,e2,cb,rend,bF,a1,a2,g2,al,afin,gfin,u0g,
    fwg,cx,cy,cbit,cg,pm0,pm1,fb,apR,bigR,a0g,rs,Codec.gb,srcC,hasC,useC,fA,act,kH,kR,kZ,kA,kF,pres,fS,fR,e7,ekl,ehp,esj,zt,vbg,dgg]
  all_goals repeat first | split | omega
  all_goals cases I.allowed[k]! <;> simp [b2n]
  all_goals repeat' first | omega | split
theorem group (a : Array Nat)
    (hc:∀c∈columns,a[c]!≤1) (hb:∀i,i<8→a[pbit i]!≤1)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈ProcPriorCodecSideKind.booleanGroup,e.evalWith
      (ProcPriorCells.env (fun c=>ZkFormal.Algebra.Fp.ofNat a[c]!) nxt first last trans)=0 := by
  have hbit (c : Nat) (hh:a[c]!≤1) : a[c]! = 0 ∨ a[c]! = 1 := by omega
  rw [ProcPriorCodecSideKind.boolean_group_eq]
  simp only [List.forall_mem_append,List.forall_mem_map]
  constructor
  · intro c hm
    have hle:a[c]!≤1 := by
      rcases List.mem_append.mp hm with hm|hm
      · exact hc c (List.mem_append_left _ hm)
      · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
        exact hb i (List.mem_range.mp hi)
    rcases hbit c hle with hh|hh
    all_goals simp only [ZkFormal.Chacha.Table.boolC,ZkFormal.Chacha.Table.E.sub,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Air.Expr.evalWith,ProcPriorCells.env,
      ite_false,Bool.false_eq_true,hh]
    all_goals decide +kernel
  · intro c hm
    rcases hbit c (hc c (List.mem_append_right _ hm)) with hh|hh
    all_goals simp only [ZkFormal.Chacha.Table.boolC,ZkFormal.Chacha.Table.E.sub,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Air.Expr.evalWith,ProcPriorCells.env,
      ite_false,Bool.false_eq_true,hh]
    all_goals try simp only [←ZkFormal.Algebra.Fp.ofNat_def]
    all_goals grind only

theorem actual_group (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f gg : Nat) (s out : State)
    (hcb:s.2.2.2.2.2≤1) (hk:k<R.n*R.n) (hf:f<3) (hg:gg<8)
    (h:step I R present gb fwd (instanceCells I R present vid) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ ∀(nxt : Nat→ZkFormal.Algebra.Fp) (first last trans : ZkFormal.Algebra.Fp),
      ∀e∈ProcPriorCodecSideKind.booleanGroup,e.evalWith
        (ProcPriorCells.env (fun c=>ZkFormal.Algebra.Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,ha,hc⟩:=actual I R present gb fwd vid k f gg s out hcb hk hf hg h
  obtain ⟨b,hb,hbits⟩:=actual_post_bits I R present gb fwd (instanceCells I R present vid) k f gg s out hf hg h
  have heq:b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  exact ⟨a,ha,group a hc hbits⟩

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolean

import ZkFormal.NearV3.Candidates.ProcDistQuietCells
import ZkFormal.NearV3.Candidates.ProcDistShardSuccess
namespace ZkFormal.NearV3.Candidates.ProcDistQuietRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor
open SchedSetAll ProcDistQuietCells
private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩
private theorem check_true (b:Bool)(msg:String)(u:Unit)
    (h:check b msg=.ok u) : b=true := by
  unfold check at h
  split at h
  · assumption
  · cases h
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem shard (I:Input)(R:Run)(sd i:Nat)(s out:ShardAcc)
    (h:shardStep I R sd i s=.ok (.yield out)) :
    ∃row,out.1=s.1.push row ∧
      ∀col,col=6 ∨col=7 ∨(115≤col ∧col≤118) →row[col]! =0 := by
  unfold shardStep at h
  obtain ⟨u,hcheck,h⟩:=bind_ok h
  have hc:=check_true _ _ _ hcheck
  have hc':=of_decide_eq_true hc
  simp only [hc',ite_true,pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
  subst out
  refine ⟨_,rfl,?_⟩
  intro col hc
  have hcol:col=6 ∨col=7 ∨col=115 ∨col=116 ∨col=117 ∨col=118:=by omega
  rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    rw [shard_tail _ _ _ _ _ _ (by decide)]
    simp only [lookup,List.foldl_cons,List.foldl_nil,Dist.cx,Dist.cy,Dist.cb,Dist.cg,
      Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,
      Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,
      Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1,Nat.reduceEqDiff,ite_true,ite_false]

theorem cell (I:Input)(R:Run)(i j:Nat)(s out:CellAcc)
    (h:cellStep I R i j s=.ok (.yield out)) :
    ∃row,out.1=s.1.push row ∧
      ∀col,col=6 ∨col=7 ∨(115≤col ∧col≤118) →row[col]! =0 := by
  unfold cellStep at h
  dsimp only at h
  split at h
  · rename_i ha
    simp only [ha,ite_true,Bool.true_eq,Bool.true_and] at h
    obtain ⟨u,hcheck,h⟩:=bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    refine ⟨_,rfl,?_⟩
    intro col hc
    rw [SchedSetAll.cell _ _ col (by unfold Dist.width;omega)]
    simp only [SchedSetAll.append,bits1 _ col _ hc,bits2 _ col _ hc,
      qbits1 _ col _ hc,qbits2 _ col _ hc,rbits1 _ col _ hc,rbits2 _ col _ hc]
    have hcol:col=6 ∨col=7 ∨col=115 ∨col=116 ∨col=117 ∨col=118:=by omega
    rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp [lookup,List.foldl_cons,List.foldl_nil,Dist.cx,Dist.cy,Dist.cb,Dist.cg,
        Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,
        Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,
        Dist.by0,Dist.gb,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.e2,Dist.ig1,Dist.ig2,Dist.eI,b2n]
  · rename_i ha
    simp only [ha,ite_false,Bool.false_eq_true,Bool.false_and,pure,Except.pure,
      Except.ok.injEq,ForInStep.yield.injEq] at h
    subst out
    refine ⟨_,rfl,?_⟩
    intro col hc
    rw [SchedSetAll.cell _ _ col (by unfold Dist.width;omega)]
    simp only [SchedSetAll.append,bits1 _ col _ hc,bits2 _ col _ hc,
      qbits1 _ col _ hc,qbits2 _ col _ hc,rbits1 _ col _ hc,rbits2 _ col _ hc]
    have hcol:col=6 ∨col=7 ∨col=115 ∨col=116 ∨col=117 ∨col=118:=by omega
    rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      simp [lookup,List.foldl_cons,List.foldl_nil,Dist.cx,Dist.cy,Dist.cb,Dist.cg,
        Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,
        Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,
        Dist.by0,Dist.gb,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.e2,Dist.ig1,Dist.ig2,Dist.eI,b2n]

end ZkFormal.NearV3.Candidates.ProcDistQuietRows

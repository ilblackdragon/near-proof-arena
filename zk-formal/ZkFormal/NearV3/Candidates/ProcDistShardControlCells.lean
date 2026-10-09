import ZkFormal.NearV3.Candidates.ProcDistShardOutput
namespace ZkFormal.NearV3.Candidates.ProcDistShardControlCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
open ProcDistShardRow ProcDistShardCells
attribute [local irreducible] ProcDistShardRow.row finv fsub
set_option maxRecDepth 32768
theorem fields (tv n sd i x count left budget kpV:Nat) :
    (row tv n sd i x count left budget kpV)[Dist.act]! =(1) ∧
    (row tv n sd i x count left budget kpV)[Dist.kP]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.kS]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.kSh]! =(1) ∧
    (row tv n sd i x count left budget kpV)[Dist.kGH]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.kC]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.al]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.cg]! =(1) ∧
    (row tv n sd i x count left budget kpV)[Dist.dlsg]! =(1) ∧
    (row tv n sd i x count left budget kpV)[Dist.dlrg]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.eI]! =(0) ∧
    (row tv n sd i x count left budget kpV)[Dist.e1]! =(if i+1=n then 1 else 0) := by
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · rw [core_cell tv n sd i x count left budget kpV Dist.act (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.kP (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.kS (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.kSh (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.kGH (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.kC (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.al (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.cg (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.dlsg (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.dlrg (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.eI (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
  · rw [core_cell tv n sd i x count left budget kpV Dist.e1 (by decide) (by decide) (by decide) (by decide)]
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1]
end ZkFormal.NearV3.Candidates.ProcDistShardControlCells

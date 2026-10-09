import ZkFormal.NearV3.Candidates.ProcDistCellRange
namespace ZkFormal.NearV3.Candidates.ProcDistCellBools
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll SchedSetAllRange
open ProcDistCellRow ProcDistCellCells
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem kinds (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) :
    ∀col∈[Dist.act,Dist.kP,Dist.kS,Dist.kSh,Dist.kGH,Dist.kC,Dist.zc,Dist.al,
      Dist.e1,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.eI],
      (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]! ≤1 := by
  simp only [List.forall_mem_cons]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by simp⟩
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.act (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kP (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kS (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kSh (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kGH (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.kC (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.zc (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.al (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.e1 (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.cb (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.cg (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.dlsg (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.dlrg (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split
  · rw [core_cell ids tv n i j sv rr n1 l1 n2 l2 allowed Dist.eI (by decide) (by decide) (by decide) (by decide)]
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]
    try simp only [b2n]
    repeat' first | omega | split

private theorem low_core (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2 col:Nat)
    (hc:col=27∨col=28∨col=29∨col=30∨col=31∨col=32∨col=35∨col=36∨col=37∨col=38∨col=39∨col=40) :
    lookup (core ids tv n i j sv rr n1 l1 n2 l2 false) col 0=0 := by
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [core,lookup,List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,Dist.kP,Dist.kS,Dist.kGH,Dist.kSh,Dist.zc,Dist.act,Dist.kC,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.L1,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.q2,Dist.r2,Dist.llo,Dist.lhi,Dist.al,Dist.alc,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.gb,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.da,Dist.db,Dist.sL,Dist.dlsg,Dist.dlrg,Dist.e1,Dist.ig1,Dist.e2,Dist.ig2,Dist.eI]

theorem low_zero (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2 col:Nat)
    (hc:col=27∨col=28∨col=29∨col=30∨col=31∨col=32∨col=35∨col=36∨col=37∨col=38∨col=39∨col=40) :
    (row ids tv n i j sv rr n1 l1 n2 l2 false)[col]! =0 := by
  have hcol:col<41:=by omega
  unfold row
  rw [cell Dist.width _ col (by unfold Dist.width;omega)]
  have hmiss (base len value v:Nat)(hbase:41≤base) :
      lookup (bitsN (fun x=>base+x) len value) col v=v :=
    miss_block base len col v (fun x=>bit value x) (Or.inl (by omega))
  simp only [append,Bool.false_eq_true,ite_false,List.append_nil]
  rw [show lookup (bitsN Dist.rb2 6 (remn false n2 l2)) col _=_ from hmiss 109 6 _ _ (by decide),
    show lookup (bitsN Dist.rb1 6 (remn false n1 l1)) col _=_ from hmiss 103 6 _ _ (by decide),
    show lookup (bitsN Dist.qb2 23 (quot false n2 l2)) col _=_ from hmiss 80 23 _ _ (by decide),
    show lookup (bitsN Dist.qb1 23 (quot false n1 l1)) col _=_ from hmiss 57 23 _ _ (by decide)]
  exact low_core ids tv n i j sv rr n1 l1 n2 l2 col hc

theorem columns (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) :
    ∀col∈Dist.boolCols,(row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]! ≤1 := by
  simp only [Dist.boolCols,List.forall_mem_append,List.forall_mem_map,List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨kinds ids tv n i j sv rr n1 l1 n2 l2 allowed,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro k hk
    cases allowed
    · rw [low_zero ids tv n i j sv rr n1 l1 n2 l2 (Dist.bt1 k) (by unfold Dist.bt1;omega)];omega
    · rw [complement1 _ _ _ _ _ _ _ _ _ _ _ k hk];exact Complete.bit_le _ _
  · intro k hk
    cases allowed
    · rw [low_zero ids tv n i j sv rr n1 l1 n2 l2 (Dist.bt2 k) (by unfold Dist.bt2;omega)];omega
    · rw [complement2 _ _ _ _ _ _ _ _ _ _ _ k hk];exact Complete.bit_le _ _
  · intro k hk;rw [ProcDistCellBitCells.q1 _ _ _ _ _ _ _ _ _ _ _ _ k hk];exact Complete.bit_le _ _
  · intro k hk;rw [ProcDistCellBitCells.q2 _ _ _ _ _ _ _ _ _ _ _ _ k hk];exact Complete.bit_le _ _
  · intro k hk;rw [ProcDistCellBitCells.r1 _ _ _ _ _ _ _ _ _ _ _ _ k hk];exact Complete.bit_le _ _
  · intro k hk;rw [ProcDistCellBitCells.r2 _ _ _ _ _ _ _ _ _ _ _ _ k hk];exact Complete.bit_le _ _
end ZkFormal.NearV3.Candidates.ProcDistCellBools

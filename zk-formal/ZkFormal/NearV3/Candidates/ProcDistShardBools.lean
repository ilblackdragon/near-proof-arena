import ZkFormal.NearV3.Candidates.ProcDistShardInverseCell
namespace ZkFormal.NearV3.Candidates.ProcDistShardBools
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll SchedSetAllRange
open ProcDistShardRow ProcDistShardCells ProcDistShardScalarCells
attribute [local irreducible] ProcDistShardRow.row
set_option maxRecDepth 32768

private theorem low_core (tv n sd i x count left budget kpV col:Nat)
    (hc:col=27∨col=28∨col=29∨col=30∨col=31∨col=32∨col=35∨col=36∨col=37∨col=38∨col=39∨col=40) :
    lookup (core tv n sd i x count left budget kpV) col 0=0 := by
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [List.foldl_cons,List.foldl_nil,Prod.fst,Prod.snd,eq_self_iff_true,Nat.reduceEqDiff,ite_true,ite_false,and_self,core,lookup,Dist.kP,Dist.kS,Dist.kGH,Dist.kC,Dist.al,Dist.dlrg,Dist.eI,Dist.q1,Dist.r1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.act,Dist.kSh,Dist.tau,Dist.nn,Dist.side,Dist.a,Dist.r,Dist.N2,Dist.L2,Dist.by0,Dist.by1,Dist.by2,Dist.q2,Dist.r2,Dist.icnt,Dist.zc,Dist.kp,Dist.da,Dist.db,Dist.dlsg,Dist.sL,Dist.e1,Dist.shd,Dist.lnk,Dist.llo,Dist.adr,Dist.bv,Dist.ig1,Nat.reduceAdd]

theorem low1 (tv n sd i x count left budget kpV j:Nat)(hj:j<6) :
    (row tv n sd i x count left budget kpV)[Dist.bt1 j]! =0 := by
  rw [core_cell tv n sd i x count left budget kpV (Dist.bt1 j)
    (by unfold Dist.bt1;omega) (by unfold Dist.bt1;omega)
    (by unfold Dist.bt1;omega) (by unfold Dist.bt1;omega)]
  apply low_core
  unfold Dist.bt1;omega

theorem low2_zero (tv n sd i x left budget kpV j:Nat)(hj:j<6) :
    (row tv n sd i x 0 left budget kpV)[Dist.bt2 j]! =0 := by
  unfold row
  rw [cell Dist.width _ _ (by unfold Dist.width Dist.bt2;omega)]
  have hq(v:Nat):lookup (bitsN Dist.qb2 23 (average 0 left)) (Dist.bt2 j) v=v :=
    miss_block 80 23 (35+j) v (fun k=>bit (average 0 left) k) (Or.inl (by omega))
  have hr(v:Nat):lookup (bitsN Dist.rb2 6 (remainder 0 left)) (Dist.bt2 j) v=v :=
    miss_block 109 6 (35+j) v (fun k=>bit (remainder 0 left) k) (Or.inl (by omega))
  simp only [append,hq,hr,ite_true,List.append_nil]
  apply low_core
  unfold Dist.bt2;omega

theorem kinds (tv n sd i x count left budget kpV:Nat) :
    ∀col∈[Dist.act,Dist.kP,Dist.kS,Dist.kSh,Dist.kGH,Dist.kC,Dist.zc,Dist.al,
      Dist.e1,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.eI],
      (row tv n sd i x count left budget kpV)[col]! ≤1 := by
  rcases ProcDistShardControlCells.fields tv n sd i x count left budget kpV with
    ⟨ha,hp,hs,hsh,hgh,hc,hal,hcg,hsg,hrg,heI,he1⟩
  have hz:=(ProcDistShardAverageCells.fields tv n sd i x count left budget kpV).2.2.2.2
  have hb:=(ProcDistShardOutputCells.fields tv n sd i x count left budget kpV).2.2.1
  simp only [List.forall_mem_cons,ha,hp,hs,hsh,hgh,hc,hz,hal,he1,hb,hcg,hsg,hrg,heI]
  split <;> split <;> simp

theorem columns (tv n sd i x count left budget kpV:Nat) :
    ∀col∈Dist.boolCols,(row tv n sd i x count left budget kpV)[col]! ≤1 := by
  simp only [Dist.boolCols,List.forall_mem_append,List.forall_mem_map,List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨kinds tv n sd i x count left budget kpV,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro j hj;rw [low1 _ _ _ _ _ _ _ _ _ j hj];omega
  · intro j hj
    by_cases hc:count=0
    · subst count;rw [low2_zero _ _ _ _ _ _ _ _ j hj];omega
    · rw [complement_bits _ _ _ _ _ _ _ _ _ j hj hc];exact Complete.bit_le _ _
  · intro j hj;rw [unused_quotient_bits _ _ _ _ _ _ _ _ _ j hj];omega
  · intro j hj;rw [quotient_bits _ _ _ _ _ _ _ _ _ j hj];exact Complete.bit_le _ _
  · intro j hj;rw [unused_remainder_bits _ _ _ _ _ _ _ _ _ j hj];omega
  · intro j hj;rw [remainder_bits _ _ _ _ _ _ _ _ _ j hj];exact Complete.bit_le _ _
end ZkFormal.NearV3.Candidates.ProcDistShardBools

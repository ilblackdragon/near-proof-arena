import ZkFormal.NearV3.Candidates.ProcDistCellOutput
namespace ZkFormal.NearV3.Candidates.ProcDistCellCurrent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem header_frame (Z:ZEnv)(hg:Z.cur Dist.kGH=0) :
    ∀e∈Dist.cGrid.take 9,zev Z e=0 := by
  simp [Dist.cGrid,Dist.instCols,Dist.mul3,Dist.notE,zev,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,hg]

theorem shard_frame (Z:ZEnv)(hs:Z.cur Dist.kSh=0) :
    ∀e∈Dist.cShard,zev Z e=0 := by
  simp [Dist.cShard,Dist.instCols,Dist.mul3,Dist.notE,zev,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,hs]

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (h1:n1≤64)(h2:n2≤64)(hp:allowed=true→0<n1∧0<n2)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!) :
    (∀e∈Dist.cShard,e.eval tr t r pub=0) ∧
    (∀e∈Dist.cGrid.take 26,e.eval tr t r pub=0) := by
  have hf:=ProcDistCellOutputCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hh:(tenv tr t r pub).cur Dist.kGH=0 := by
    change (tr.cell t r Dist.kGH).toNat=0
    rw [hrow,hf.2.1];rfl
  have hs:(tenv tr t r pub).cur Dist.kSh=0 := by
    change (tr.cell t r Dist.kSh).toNat=0
    rw [hrow,hf.1];rfl
  constructor
  · intro e he
    exact eval_zero_of (shard_frame (tenv tr t r pub) hs e he)
  · have ho:=ProcDistCellOutput.physical ids tv n i j sv rr n1 l1 n2 l2 allowed tr t r pub hrow
    have hd:=ProcDistCellDivision.physical ids tv n i j sv rr n1 l1 n2 l2 allowed h1 h2 hp tr t r pub hrow
    rw [show Dist.cGrid.take 26=Dist.cGrid.take 9++(Dist.cGrid.drop 9).take 3++
        (Dist.cGrid.drop 12).take 4++(Dist.cGrid.drop 16).take 10 from rfl]
    simp only [List.forall_mem_append]
    refine ⟨⟨⟨?_,ho.1⟩,hd⟩,ho.2⟩
    intro e he
    exact eval_zero_of (header_frame (tenv tr t r pub) hh e he)
end ZkFormal.NearV3.Candidates.ProcDistCellCurrent

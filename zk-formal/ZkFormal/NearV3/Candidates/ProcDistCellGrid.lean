import ZkFormal.NearV3.Candidates.ProcDistCellBoundary
namespace ZkFormal.NearV3.Candidates.ProcDistCellGrid
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem terminal_frame (Z:ZEnv)(he:Z.cur Dist.e1=1) :
    ∀e∈(Dist.cGrid.drop 26).take 8,zev Z e=0 := by
  simp [Dist.cGrid,Dist.instCols,Dist.mul3,Dist.notE,zev,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,he]

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (hj:j<n)(h1:n1≤64)(h2:n2≤64)(hp:allowed=true→0<n1∧0<n2)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!)
    (hinner:j+1<n→∃rr' n2' l2' allowed',∀col,
      tr.cell t ((r+1)%tr.height t) col=Fp.ofNat
        (row ids tv n i (j+1) sv rr' (n1-b2n allowed) (l1-grant allowed n1 l1 n2 l2) n2' l2' allowed')[col]!)
    (hend:ProcDistCellBoundary.Next tv n i j tr t r) :
    ∀e∈Dist.cGrid,e.eval tr t r pub=0 := by
  have hc:=(ProcDistCellCurrent.physical ids tv n i j sv rr n1 l1 n2 l2 allowed h1 h2 hp tr t r pub hrow).2
  have hb:=ProcDistCellBoundary.physical ids tv n i j sv rr n1 l1 n2 l2 allowed tr t r pub hrow hend
  have hi:∀e∈(Dist.cGrid.drop 26).take 8,e.eval tr t r pub=0 := by
    by_cases he:j+1<n
    · obtain ⟨rr',n2',l2',allowed',hnext⟩:=hinner he
      exact ProcDistCellInterior.physical ids tv n i j sv rr n1 l1 n2 l2 rr' n2' l2' allowed allowed'
        he (fun h=>(hp h).1) tr t r pub hrow hnext
    · have hlast:j+1=n:=by omega
      have he1:(tenv tr t r pub).cur Dist.e1=1:=by
        change (tr.cell t r Dist.e1).toNat=1
        rw [hrow,(ProcDistCellPosition.fields ids tv n i j sv rr n1 l1 n2 l2 allowed).2,if_pos hlast]
        rfl
      intro e hem
      exact eval_zero_of (terminal_frame (tenv tr t r pub) he1 e hem)
  rw [show Dist.cGrid=Dist.cGrid.take 26++(Dist.cGrid.drop 26).take 8++Dist.cGrid.drop 34 from rfl]
  simp only [List.forall_mem_append]
  exact ⟨⟨hc,hi⟩,hb⟩
end ZkFormal.NearV3.Candidates.ProcDistCellGrid

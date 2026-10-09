import ZkFormal.NearV3.Candidates.ProcDistCellKind
import ZkFormal.NearV3.Candidates.ProcDistScanQuiet
namespace ZkFormal.NearV3.Candidates.ProcDistCellLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (hi:i<n)(hj:j<n)(hn:n≤64)(h1:n1≤64)(h2:n2≤64)(hl1:l1≤4500000)(hl2:l2≤4500000)
    (hp:allowed=true→0<n1∧0<n2)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!)
    (hf:r≠0)(hl:r+1<tr.height t)
    (hinner:j+1<n→∃rr' n2' l2' allowed',∀col,
      tr.cell t ((r+1)%tr.height t) col=Fp.ofNat
        (row ids tv n i (j+1) sv rr' (n1-b2n allowed) (l1-grant allowed n1 l1 n2 l2) n2' l2' allowed')[col]!)
    (hend:ProcDistCellBoundary.Next tv n i j tr t r) :
    ∀e∈ScanDist.constraints,e.eval tr t r pub=0 := by
  have hk:=ProcDistCellKind.physical ids tv n i j sv rr n1 l1 n2 l2 allowed hi hj hn tr t r pub hrow hf hl
  have hs:=(ProcDistCellCurrent.physical ids tv n i j sv rr n1 l1 n2 l2 allowed h1 h2 hp tr t r pub hrow).1
  have hg:=ProcDistCellGrid.physical ids tv n i j sv rr n1 l1 n2 l2 allowed hj h1 h2 hp tr t r pub hrow hinner hend
  have hr:=ProcDistCellRange.physical ids tv n i j sv rr n1 l1 n2 l2 allowed h1 h2 hl1 hl2 hp tr t r pub hrow
  have hc:=ProcDistCellControls.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have zcell (col:Nat)(h:(row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]! =0) :tr.cell t r col=0 := by
    rw [hrow,h];rfl
  have ho:=ProcDistScanQuiet.physical tr t r pub (zcell _ hc.2.1) (zcell _ hc.2.2.1)
    (zcell _ hc.2.2.2.1) (zcell _ hc.2.2.2.2.1) (zcell _ hc.2.2.2.2.2.1) (zcell _ hc.2.2.2.2.2.2)
  simp only [ScanDist.constraints,Dist.constraints,List.forall_mem_append]
  exact ⟨⟨⟨⟨hk,hs⟩,hg⟩,hr⟩,ho⟩
end ZkFormal.NearV3.Candidates.ProcDistCellLocal

import ZkFormal.NearV3.Candidates.ProcDistHeaderPhysical
namespace ZkFormal.NearV3.Candidates.ProcDistHeaderNext
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
attribute [local irreducible] ProcDistCellRow.row

theorem physical (ids:List Nat)(tv n i sv count left rr n2 l2:Nat)(allowed:Bool)
    (ht:tv<P)(hn:n<P)(hi:i<P)(hs:sv<P)(hN:count<P)(hL:left<P)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀c,tr.cell t r c=Fp.ofNat (ProcDistHeader.row tv n i sv count left)[c]!)
    (hf:r≠0)(hl:r+1<tr.height t)
    (hnext:∀c,tr.cell t ((r+1)%tr.height t) c=Fp.ofNat
      (ProcDistCellRow.row ids tv n i 0 sv rr count left n2 l2 allowed)[c]!) :
    ∀e∈ScanDist.constraints,e.eval tr t r pub=0 := by
  have ho:=ProcDistCellOutputCells.fields ids tv n i 0 sv rr count left n2 l2 allowed
  have hd:=ProcDistCellDivisionCells.fields ids tv n i 0 sv rr count left n2 l2 allowed
  have hp:=ProcDistCellPosition.fields ids tv n i 0 sv rr count left n2 l2 allowed
  apply ProcDistHeaderPhysical.physical tv n i sv count left ht hn hi hs hN hL tr t r pub hrow hf hl
  · rw [hnext,ho.2.2.1];rfl
  · rw [hnext,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1];rfl
  · rw [hnext,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hnext,ho.2.2.2.1]
  · rw [hnext,hd.2.1]
  · rw [hnext,hd.2.2.1]
  · rw [hnext,hp.1]
  · rw [hnext,ho.2.2.2.2.1]
end ZkFormal.NearV3.Candidates.ProcDistHeaderNext

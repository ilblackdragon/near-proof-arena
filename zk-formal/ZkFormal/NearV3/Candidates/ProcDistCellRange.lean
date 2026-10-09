import ZkFormal.NearV3.Candidates.ProcDistCellBitCells
namespace ZkFormal.NearV3.Candidates.ProcDistCellRange
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row

private theorem number (cols:Nat→Nat)(len value:Nat)(hv:value<2^len)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hcol:∀k,k<len→tr.cell t r (cols k)=Fp.ofNat (bit value k)) :
    (ZkFormal.Chacha.Rng.Table.num cols len).eval tr t r pub=Fp.ofNat value := by
  have hh:=ProcScanRequestRange.num_bits (tenv tr t r pub) cols len value hv (fun k hk=>by
    change (tr.cell t r (cols k)).toNat=_
    rw [hcol k hk,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have hb:=Complete.bit_le value k
    unfold P;omega)
  rw [eval_eq,hh]
  exact ZkFormal.Chacha.intCast_ofNat _

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (h1:n1≤64)(h2:n2≤64)(hl1:l1≤4500000)(hl2:l2≤4500000)
    (hp:allowed=true→0<n1∧0<n2)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!) :
    ∀e∈Dist.cRange,e.eval tr t r pub=0 := by
  have b1:=ProcDistCellArithmetic.range allowed n1 l1 h1 hl1 (fun h=>(hp h).1)
  have b2:=ProcDistCellArithmetic.range allowed n2 l2 h2 hl2 (fun h=>(hp h).2)
  have q1:=number Dist.qb1 23 (quot allowed n1 l1) b1.1 tr t r pub (fun k hk=>by
    rw [hrow,ProcDistCellBitCells.q1 _ _ _ _ _ _ _ _ _ _ _ _ k hk])
  have q2:=number Dist.qb2 23 (quot allowed n2 l2) b2.1 tr t r pub (fun k hk=>by
    rw [hrow,ProcDistCellBitCells.q2 _ _ _ _ _ _ _ _ _ _ _ _ k hk])
  have r1:=number Dist.rb1 6 (remn allowed n1 l1) b1.2 tr t r pub (fun k hk=>by
    rw [hrow,ProcDistCellBitCells.r1 _ _ _ _ _ _ _ _ _ _ _ _ k hk])
  have r2:=number Dist.rb2 6 (remn allowed n2 l2) b2.2 tr t r pub (fun k hk=>by
    rw [hrow,ProcDistCellBitCells.r2 _ _ _ _ _ _ _ _ _ _ _ _ k hk])
  have hd:=ProcDistCellDivisionCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have sq1:tr.cell t r Dist.q1=Fp.ofNat (quot allowed n1 l1):=by rw [hrow,hd.2.2.2.2.2.1]
  have sr1:tr.cell t r Dist.r1=Fp.ofNat (remn allowed n1 l1):=by rw [hrow,hd.2.2.2.2.2.2.1]
  have sq2:tr.cell t r Dist.q2=Fp.ofNat (quot allowed n2 l2):=by rw [hrow,hd.2.2.2.2.2.2.2.1]
  have sr2:tr.cell t r Dist.r2=Fp.ofNat (remn allowed n2 l2):=by rw [hrow,hd.2.2.2.2.2.2.2.2]
  clear hd hrow
  simp only [Dist.cRange,List.forall_mem_cons]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Dist.q1 + -(ZkFormal.Chacha.Rng.Table.num Dist.qb1 23).eval tr t r pub=0
    rw [sq1,q1];grind only
  · change tr.cell t r Dist.q2 + -(ZkFormal.Chacha.Rng.Table.num Dist.qb2 23).eval tr t r pub=0
    rw [sq2,q2];grind only
  · change tr.cell t r Dist.r1 + -(ZkFormal.Chacha.Rng.Table.num Dist.rb1 6).eval tr t r pub=0
    rw [sr1,r1];grind only
  · change tr.cell t r Dist.r2 + -(ZkFormal.Chacha.Rng.Table.num Dist.rb2 6).eval tr t r pub=0
    rw [sr2,r2];grind only
end ZkFormal.NearV3.Candidates.ProcDistCellRange

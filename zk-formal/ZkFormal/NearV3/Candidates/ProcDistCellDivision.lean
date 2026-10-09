import ZkFormal.NearV3.Candidates.ProcDistCellDivisionCells
namespace ZkFormal.NearV3.Candidates.ProcDistCellDivision
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row

theorem bits (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(h1:n1≤64)(h2:n2≤64)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 true)[col]!) :
    Dist.bits1E.eval tr t r pub=Fp.ofNat (n1-1-remn true n1 l1) ∧
    Dist.bits2E.eval tr t r pub=Fp.ofNat (n2-1-remn true n2 l2) := by
  constructor
  · have hx:n1-1-remn true n1 l1<2^6:=by omega
    have hh:=ProcScanRequestRange.num_bits (tenv tr t r pub) Dist.bt1 6 _ hx (fun k hk=>by
      change (tr.cell t r (Dist.bt1 k)).toNat=_
      rw [hrow,ProcDistCellCells.complement1 _ _ _ _ _ _ _ _ _ _ _ k hk,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
      have hb:=Complete.bit_le (n1-1-remn true n1 l1) k
      unfold P;omega)
    rw [Dist.bits1E,eval_eq,hh]
    exact ZkFormal.Chacha.intCast_ofNat _
  · have hx:n2-1-remn true n2 l2<2^6:=by omega
    have hh:=ProcScanRequestRange.num_bits (tenv tr t r pub) Dist.bt2 6 _ hx (fun k hk=>by
      change (tr.cell t r (Dist.bt2 k)).toNat=_
      rw [hrow,ProcDistCellCells.complement2 _ _ _ _ _ _ _ _ _ _ _ k hk,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
      have hb:=Complete.bit_le (n2-1-remn true n2 l2) k
      unfold P;omega)
    rw [Dist.bits2E,eval_eq,hh]
    exact ZkFormal.Chacha.intCast_ofNat _

set_option maxRecDepth 32768 in
theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (h1:n1≤64)(h2:n2≤64)(hp:allowed=true→0<n1∧0<n2)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!) :
    ∀e∈(Dist.cGrid.drop 12).take 4,e.eval tr t r pub=0 := by
  rcases ProcDistCellDivisionCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed with
    ⟨ha,hN1,hL1,hN2,hL2,hQ1,hR1,hQ2,hR2⟩
  have sa:tr.cell t r Dist.al=Fp.ofNat (b2n allowed):=by rw [hrow,ha]
  have sN1:tr.cell t r Dist.N1=Fp.ofNat n1:=by rw [hrow,hN1]
  have sL1:tr.cell t r Dist.L1=Fp.ofNat l1:=by rw [hrow,hL1]
  have sN2:tr.cell t r Dist.N2=Fp.ofNat n2:=by rw [hrow,hN2]
  have sL2:tr.cell t r Dist.L2=Fp.ofNat l2:=by rw [hrow,hL2]
  have sQ1:tr.cell t r Dist.q1=Fp.ofNat (quot allowed n1 l1):=by rw [hrow,hQ1]
  have sR1:tr.cell t r Dist.r1=Fp.ofNat (remn allowed n1 l1):=by rw [hrow,hR1]
  have sQ2:tr.cell t r Dist.q2=Fp.ofNat (quot allowed n2 l2):=by rw [hrow,hQ2]
  have sR2:tr.cell t r Dist.r2=Fp.ofNat (remn allowed n2 l2):=by rw [hrow,hR2]
  have hbits:allowed=true→Dist.bits1E.eval tr t r pub=Fp.ofNat (n1-1-remn true n1 l1) ∧
      Dist.bits2E.eval tr t r pub=Fp.ofNat (n2-1-remn true n2 l2):=by
    intro he;subst allowed;exact bits ids tv n i j sv rr n1 l1 n2 l2 h1 h2 tr t r pub hrow
  clear hrow ha hN1 hL1 hN2 hL2 hQ1 hR1 hQ2 hR2
  simp only [Dist.cGrid,Dist.instCols,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,List.forall_mem_cons]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Dist.al*(tr.cell t r Dist.L1 + -(tr.cell t r Dist.q1*tr.cell t r Dist.N1+tr.cell t r Dist.r1))=0
    rw [sa,sL1,sQ1,sN1,sR1]
    cases allowed
    · change (0:Fp)*_=0;grind only
    · change (1:Fp)*_=0
      rw [ProcDistCellArithmetic.division n1 l1];grind only
  · change tr.cell t r Dist.al*((tr.cell t r Dist.N1 + -(1:Fp)) + -tr.cell t r Dist.r1 + -Dist.bits1E.eval tr t r pub)=0
    rw [sa,sN1,sR1]
    cases allowed
    · change (0:Fp)*_=0;grind only
    · change (1:Fp)*_=0
      rw [(hbits rfl).1]
      have h:=ProcDistCellArithmetic.complement n1 l1 (hp rfl).1
      grind only
  · change tr.cell t r Dist.al*(tr.cell t r Dist.L2 + -(tr.cell t r Dist.q2*tr.cell t r Dist.N2+tr.cell t r Dist.r2))=0
    rw [sa,sL2,sQ2,sN2,sR2]
    cases allowed
    · change (0:Fp)*_=0;grind only
    · change (1:Fp)*_=0
      rw [ProcDistCellArithmetic.division n2 l2];grind only
  · change tr.cell t r Dist.al*((tr.cell t r Dist.N2 + -(1:Fp)) + -tr.cell t r Dist.r2 + -Dist.bits2E.eval tr t r pub)=0
    rw [sa,sN2,sR2]
    cases allowed
    · change (0:Fp)*_=0;grind only
    · change (1:Fp)*_=0
      rw [(hbits rfl).2]
      have h:=ProcDistCellArithmetic.complement n2 l2 (hp rfl).2
      grind only
end ZkFormal.NearV3.Candidates.ProcDistCellDivision

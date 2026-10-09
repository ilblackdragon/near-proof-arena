import ZkFormal.NearV3.Candidates.ProcDistShardScalarCells
import ZkFormal.NearV3.Candidates.ProcScanRequestRange
namespace ZkFormal.NearV3.Candidates.ProcDistShardRange
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistShardRow ProcDistShardCells ProcDistShardScalarCells
attribute [local irreducible] ProcDistShardRow.row

private theorem number (tr:Trace Fp)(t r:Nat)(pub:List Fp)(cols:Nat→Nat)(n x:Nat)(hx:x<2^n)
    (hc:∀j<n,tr.cell t r (cols j)=Fp.ofNat (bit x j)) :
    (ZkFormal.Chacha.Rng.Table.num cols n).eval tr t r pub=Fp.ofNat x := by
  have hh:=ProcScanRequestRange.num_bits (tenv tr t r pub) cols n x hx (fun j hj=>by
    change (tr.cell t r (cols j)).toNat=_
    rw [hc j hj,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have hb:=Complete.bit_le x j
    unfold P;omega)
  rw [eval_eq,hh]
  exact ZkFormal.Chacha.intCast_ofNat x

theorem bounds (count left:Nat)(hc:count≤64)(hl:left≤4500000) :
    average count left<2^23 ∧remainder count left<64 := by
  constructor
  · unfold average
    split
    · decide
    · have h:=Nat.div_le_self left count;omega
  · unfold remainder
    split
    · decide
    · have h:=Nat.mod_lt left (show 0<count by omega);omega

theorem physical (tv n sd i x count left budget kpV:Nat)(hc:count≤64)(hl:left≤4500000)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row tv n sd i x count left budget kpV)[col]!) :
    ∀e∈Dist.cRange,e.eval tr t r pub=0 := by
  have hq:=quotients tv n sd i x count left budget kpV
  have hb:=bounds count left hc hl
  have h0:=number tr t r pub Dist.qb1 23 0 (by decide) (fun j hj=>by
    rw [hrow,unused_quotient_bits _ _ _ _ _ _ _ _ _ j hj]
    simp only [bit,Nat.zero_div,Nat.zero_mod])
  have h1:=number tr t r pub Dist.qb2 23 (average count left) hb.1 (fun j hj=>by
    rw [hrow,quotient_bits _ _ _ _ _ _ _ _ _ j hj])
  have h2:=number tr t r pub Dist.rb1 6 0 (by decide) (fun j hj=>by
    rw [hrow,unused_remainder_bits _ _ _ _ _ _ _ _ _ j hj]
    simp only [bit,Nat.zero_div,Nat.zero_mod])
  have h3:=number tr t r pub Dist.rb2 6 (remainder count left) hb.2 (fun j hj=>by
    rw [hrow,remainder_bits _ _ _ _ _ _ _ _ _ j hj])
  simp only [Dist.cRange,List.forall_mem_cons,List.forall_mem_nil]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Dist.q1 + -(ZkFormal.Chacha.Rng.Table.num Dist.qb1 23).eval tr t r pub=0
    rw [h0,hrow,hq.1];grind only
  · change tr.cell t r Dist.q2 + -(ZkFormal.Chacha.Rng.Table.num Dist.qb2 23).eval tr t r pub=0
    rw [h1,hrow,hq.2.2.1];grind only
  · change tr.cell t r Dist.r1 + -(ZkFormal.Chacha.Rng.Table.num Dist.rb1 6).eval tr t r pub=0
    rw [h2,hrow,hq.2.1];grind only
  · change tr.cell t r Dist.r2 + -(ZkFormal.Chacha.Rng.Table.num Dist.rb2 6).eval tr t r pub=0
    rw [h3,hrow,hq.2.2.2];grind only
end ZkFormal.NearV3.Candidates.ProcDistShardRange

import ZkFormal.NearV3.Candidates.ProcDistShardAverageCells
import ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
namespace ZkFormal.NearV3.Candidates.ProcDistShardAverage
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistShardRow ProcDistShardCells ProcDistShardScalarCells
attribute [local irreducible] ProcDistShardRow.row

theorem division (count left:Nat)(hc:count≠0) :
    Fp.ofNat left=Fp.ofNat (average count left)*Fp.ofNat count+Fp.ofNat (remainder count left) := by
  rw [ofNat_mul',ofNat_add']
  apply congrArg Fp.ofNat
  simpa [average,remainder,hc,Nat.mul_comm] using (Nat.div_add_mod left count).symm

theorem complement (count left:Nat)(hc:count≠0) :
    Fp.ofNat count-1-Fp.ofNat (remainder count left)=Fp.ofNat (count-1-remainder count left) := by
  have hr:remainder count left<count:=by simp only [remainder,if_neg hc];exact Nat.mod_lt _ (by omega)
  have he:count=1+remainder count left+(count-1-remainder count left):=by omega
  have hf:=congrArg Fp.ofNat he
  simp only [←ofNat_add'] at hf
  change Fp.ofNat count=(1:Fp)+_+_ at hf
  clear he hr
  grind only

theorem bits (tv n sd i x count left budget kpV:Nat)(hc:count≠0)(hn:count≤64)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row tv n sd i x count left budget kpV)[col]!) :
    Dist.bits2E.eval tr t r pub=Fp.ofNat (count-1-remainder count left) := by
  have hx:count-1-remainder count left<2^6:=by omega
  have hh:=ProcScanRequestRange.num_bits (tenv tr t r pub) Dist.bt2 6 _ hx (fun j hj=>by
    change (tr.cell t r (Dist.bt2 j)).toNat=_
    rw [hrow,complement_bits _ _ _ _ _ _ _ _ _ j hj hc,Fp.toNat_ofNat,Nat.mod_eq_of_lt]
    have hb:=Complete.bit_le (count-1-remainder count left) j
    unfold P;omega)
  rw [Dist.bits2E,eval_eq,hh]
  exact ZkFormal.Chacha.intCast_ofNat _

set_option maxRecDepth 32768 in
theorem physical (tv n sd i x count left budget kpV:Nat)(hn:count≤64)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row tv n sd i x count left budget kpV)[col]!) :
    ∀e∈Dist.cShard.take 5,e.eval tr t r pub=0 := by
  have hf:=ProcDistShardAverageCells.fields tv n sd i x count left budget kpV
  have hq:=quotients tv n sd i x count left budget kpV
  have hs:tr.cell t r Dist.kSh=1:=by rw [hrow,hf.1];rfl
  have hN:tr.cell t r Dist.N2=Fp.ofNat count:=by rw [hrow,hf.2.1]
  have hL:tr.cell t r Dist.L2=Fp.ofNat left:=by rw [hrow,hf.2.2.1]
  have hi:tr.cell t r Dist.icnt=Fp.ofNat (finv count):=by rw [hrow,hf.2.2.2.1]
  have hz:tr.cell t r Dist.zc=if count=0 then 1 else 0:=by
    rw [hrow,hf.2.2.2.2];split <;> rfl
  have hQ:tr.cell t r Dist.q2=Fp.ofNat (average count left):=by rw [hrow,hq.2.2.1]
  have hR:tr.cell t r Dist.r2=Fp.ofNat (remainder count left):=by rw [hrow,hq.2.2.2]
  have hinv:=ProcScanRequestArithmetic.key_test count (by unfold P;omega)
  have hzero:=ProcScanRequestArithmetic.key_annihilate count
  have hbits:count≠0→Dist.bits2E.eval tr t r pub=Fp.ofNat (count-1-remainder count left):=
    fun hc=>bits tv n sd i x count left budget kpV hc hn tr t r pub hrow
  clear hf hq hrow
  simp only [Dist.cShard,List.cons_append,List.nil_append,List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  refine ⟨?_,?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Dist.kSh*(tr.cell t r Dist.zc + -(1 + -(tr.cell t r Dist.N2*tr.cell t r Dist.icnt)))=0
    rw [hs,hz,hN,hi];grind only
  · change tr.cell t r Dist.kSh*tr.cell t r Dist.N2*tr.cell t r Dist.zc=0
    rw [hs,hN,hz];grind only
  · change tr.cell t r Dist.kSh*(1 + -tr.cell t r Dist.zc)*
      (tr.cell t r Dist.L2 + -(tr.cell t r Dist.q2*tr.cell t r Dist.N2+tr.cell t r Dist.r2))=0
    rw [hs,hz,hL,hQ,hN,hR]
    by_cases hc:count=0
    · rw [if_pos hc];grind only
    · rw [if_neg hc,division count left hc];grind only
  · change tr.cell t r Dist.kSh*(1 + -tr.cell t r Dist.zc)*
      ((tr.cell t r Dist.N2 + -(1:Fp)) + -tr.cell t r Dist.r2 + -Dist.bits2E.eval tr t r pub)=0
    rw [hs,hz,hN,hR]
    by_cases hc:count=0
    · rw [if_pos hc];grind only
    · rw [if_neg hc,hbits hc]
      have hh:=complement count left hc
      grind only
  · change tr.cell t r Dist.kSh*tr.cell t r Dist.zc*tr.cell t r Dist.q2=0
    rw [hs,hz,hQ]
    by_cases hc:count=0
    · rw [if_pos hc];simp only [average,hc,ite_true]
      change (1:Fp)*1*0=0;grind only
    · rw [if_neg hc];grind only
end ZkFormal.NearV3.Candidates.ProcDistShardAverage

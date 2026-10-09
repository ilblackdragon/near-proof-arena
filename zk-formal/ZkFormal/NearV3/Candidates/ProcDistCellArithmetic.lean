import ZkFormal.NearV3.Candidates.ProcDistCellRow
namespace ZkFormal.NearV3.Candidates.ProcDistCellArithmetic
open ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow

theorem range (allowed:Bool)(count left:Nat)(hc:count≤64)(hl:left≤4500000)
    (hpos:allowed=true→0<count) :
    quot allowed count left<2^23 ∧remn allowed count left<64 := by
  cases allowed
  · simp [quot,remn]
  · have hd:=Nat.div_le_self left count
    have hm:=Nat.mod_lt left (hpos rfl)
    simp only [quot,remn,ite_true]
    omega

theorem division (count left:Nat) :
    Fp.ofNat left=Fp.ofNat (quot true count left)*Fp.ofNat count+Fp.ofNat (remn true count left) := by
  simp only [quot,remn,ite_true]
  rw [ofNat_mul',ofNat_add']
  exact congrArg Fp.ofNat (by simpa only [Nat.mul_comm] using (Nat.div_add_mod left count).symm)

theorem complement (count left:Nat)(hc:0<count) :
    Fp.ofNat count-1-Fp.ofNat (remn true count left)=Fp.ofNat (count-1-remn true count left) := by
  have h:=ProcDistShardAverage.complement count left (by omega)
  simpa only [remn,ProcDistShardRow.remainder,ite_true,if_neg (by omega:count≠0)] using h

theorem grant_le (allowed:Bool)(n1 l1 n2 l2:Nat) :
    grant allowed n1 l1 n2 l2≤l1 ∧grant allowed n1 l1 n2 l2≤l2 := by
  cases allowed
  · simp [grant]
  · simp only [grant,ite_true]
    exact ⟨Nat.le_trans (Nat.min_le_left _ _) (Nat.div_le_self _ _),
      Nat.le_trans (Nat.min_le_right _ _) (Nat.div_le_self _ _)⟩

theorem grant_selector (allowed:Bool)(n1 l1 n2 l2:Nat) :
    Fp.ofNat (grant allowed n1 l1 n2 l2)=
      Fp.ofNat (if allowed && quot allowed n2 l2≤quot allowed n1 l1 then 1 else 0)*Fp.ofNat (quot allowed n2 l2)+
      (1-Fp.ofNat (if allowed && quot allowed n2 l2≤quot allowed n1 l1 then 1 else 0))*Fp.ofNat (quot allowed n1 l1) := by
  cases allowed
  · simp only [grant,quot,ite_false,Bool.false_eq_true,Bool.false_and]
    change (0:Fp)=0*0+(1-0)*0
    grind only
  · simp only [grant,quot,ite_true,Bool.true_and,decide_eq_true_eq]
    by_cases h:l2/n2≤l1/n1
    · rw [if_pos h,Nat.min_eq_right h]
      change Fp.ofNat (l2/n2)=1*Fp.ofNat (l2/n2)+(1-1)*Fp.ofNat (l1/n1)
      grind only
    · rw [if_neg h,Nat.min_eq_left (by omega)]
      change Fp.ofNat (l1/n1)=0*Fp.ofNat (l2/n2)+(1-0)*Fp.ofNat (l1/n1)
      grind only

theorem remaining (allowed:Bool)(n1 l1 n2 l2:Nat) :
    Fp.ofNat (l2-grant allowed n1 l1 n2 l2)=Fp.ofNat l2-Fp.ofNat (grant allowed n1 l1 n2 l2) := by
  have h:=(grant_le allowed n1 l1 n2 l2).2
  have he:l2=(l2-grant allowed n1 l1 n2 l2)+grant allowed n1 l1 n2 l2:=by omega
  have hf:=congrArg Fp.ofNat he
  simp only [←ofNat_add'] at hf
  grind only
end ZkFormal.NearV3.Candidates.ProcDistCellArithmetic

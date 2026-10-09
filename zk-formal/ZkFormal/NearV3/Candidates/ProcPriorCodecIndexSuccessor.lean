import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecIndexSuccessor
open ZkFormal.Algebra

theorem natural (n k : Nat) (hn:0<n) :
    (k+1)/n=k/n+(if k%n+1=n then 1 else 0) ∧
    (k+1)%n=(if k%n+1=n then 0 else k%n+1) := by
  have hm:=Nat.mod_lt k hn
  have hd:=Nat.mod_add_div k n
  have he:k+1=(k%n+1)+n*(k/n) := by omega
  rw [he,Nat.add_mul_div_left _ _ hn,Nat.add_mul_mod_self_left]
  by_cases hw:k%n+1=n
  · simp only [if_pos hw,hw,Nat.div_self hn,Nat.mod_self,ite_true]
    simp [Nat.add_comm]
  · have hlt:k%n+1<n := by omega
    simp only [if_neg hw,Nat.div_eq_of_lt hlt,Nat.mod_eq_of_lt hlt,ite_false]
    simp [Nat.add_comm]

theorem field (n k : Nat) (hn:0<n) :
    Fp.ofNat ((k+1)/n)=Fp.ofNat (k/n)+Fp.ofNat (if k%n+1=n then 1 else 0) ∧
    Fp.ofNat ((k+1)%n)=(1-Fp.ofNat (if k%n+1=n then 1 else 0))*(Fp.ofNat (k%n)+1) := by
  obtain ⟨hq,hr⟩:=natural n k hn
  constructor
  · rw [hq,ProcPriorCodecEndArithmetic.cast_add]
  · rw [hr]
    by_cases hw:k%n+1=n
    · simp only [if_pos hw,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
      grind only
    · simp only [if_neg hw,ProcPriorCodecEndArithmetic.cast_add,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
      grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecIndexSuccessor

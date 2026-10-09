import ZkFormal.NearV3.Candidates.ProcPriorCodecGrid
import ZkFormal.NearV3.Candidates.ProcKeyInverse
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridField
open ZkFormal.Algebra ZkFormal.NearV3.Sched.Gen ProcPriorCodecGrid

def flag (p : Prop) [Decidable p] : Fp := if p then 1 else 0

theorem index_equation (n k : Nat) :
    Fp.ofNat k = Fp.ofNat (sender n k)*Fp.ofNat n+Fp.ofNat (receiver n k) := by
  have h:=congrArg Fp.ofNat (reconstruct n k)
  change ((sender n k*n+receiver n k : Nat) : Fp) = (k : Fp) at h
  change (k : Fp) = (sender n k : Fp)*(n : Fp)+(receiver n k : Fp)
  grind

theorem sender_equation (n k : Nat) (hn:0<n) :
    Fp.ofNat (sender n (k+1)) = Fp.ofNat (sender n k)+flag (receiver n k+1=n) := by
  rw [sender_next n k hn]
  unfold flag
  split
  · change ((sender n k+1 : Nat) : Fp) = (sender n k : Fp)+1; grind
  · change ((sender n k+0 : Nat) : Fp) = (sender n k : Fp)+0; grind

theorem receiver_equation (n k : Nat) (hn:0<n) :
    Fp.ofNat (receiver n (k+1)) =
      (1-flag (receiver n k+1=n))*(Fp.ofNat (receiver n k)+1) := by
  rw [receiver_next n k hn]
  unfold flag
  split
  · change (0 : Fp)=(1-1)*_; grind
  · change ((receiver n k+1 : Nat) : Fp)=(1-0)*((receiver n k : Fp)+1); grind

theorem receiver_test (n k : Nat) (hn:0<n) (hn64:n≤64) :
    Fp.ofNat (receiver n k)*Fp.ofNat (finv (receiver n k)) =
      1-flag (receiver n k=0) := by
  have hr:=Nat.mod_lt k hn
  have hp : receiver n k<P := by unfold receiver P; omega
  rw [SchedField.inverse_product,Nat.mod_eq_of_lt hp]
  unfold flag
  split <;> grind

theorem wrap_test (n k : Nat) (hn:0<n) (hn64:n≤64) :
    (Fp.ofNat (receiver n k)-Fp.ofNat (n-1))*Fp.ofNat (finv (fsub (receiver n k) (n-1))) =
      1-flag (receiver n k+1=n) := by
  have hr:=Nat.mod_lt k hn
  have hp : receiver n k<P := by unfold receiver P; omega
  have hp' : n-1<P := by unfold P; omega
  have he : receiver n k=n-1 ↔ receiver n k+1=n := by omega
  have hz:=ProcKeyInverse.difference_zero (receiver n k) (n-1) hp hp'
  rw [←SchedField.fsub_cast,SchedField.inverse_product]
  unfold flag
  by_cases h:receiver n k+1=n
  · rw [if_pos h,if_pos (hz.mpr (he.mpr h))]; grind
  · rw [if_neg h,if_neg (fun e=>h (he.mp (hz.mp e)))]; grind

theorem receiver_annihilates (n k : Nat) :
    Fp.ofNat (receiver n k)*flag (receiver n k=0)=0 := by
  unfold flag
  split
  · rw [‹receiver n k=0›]; change (0 : Fp)*1=0; grind
  · grind

theorem wrap_annihilates (n k : Nat) :
    (Fp.ofNat (receiver n k)-Fp.ofNat (n-1))*flag (receiver n k+1=n)=0 := by
  unfold flag
  split
  · have he : receiver n k=n-1 := by omega
    rw [he]; grind
  · grind

end ZkFormal.NearV3.Candidates.ProcPriorCodecGridField

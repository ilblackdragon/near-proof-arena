import ZkFormal.NearV3.Rcpt.Extract.V.Chars

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Integer squared distance represented without signed naturals. -/
def sqDistance (a b : Nat) : Nat := (a-b)*(a-b)+(b-a)*(b-a)

theorem sqDistance_cast (a b : Nat) :
    ((sqDistance a b : Nat) : Fp) = ((a: Fp)-(b:Fp))*((a:Fp)-(b:Fp)) := by
  unfold sqDistance
  by_cases h : b≤a
  · have hz : b-a=0 := by omega
    have he : a=b+(a-b) := by omega
    rw [hz,Nat.zero_mul,Nat.add_zero,natCast_mul]
    have hf : (a:Fp)=(b:Fp)+((a-b:Nat):Fp) := by rw [←natCast_add,←he]
    grind
  · have hz : a-b=0 := by omega
    have he : b=a+(b-a) := by omega
    rw [hz,Nat.zero_mul,Nat.zero_add,natCast_mul]
    have hf : (b:Fp)=(a:Fp)+((b-a:Nat):Fp) := by rw [←natCast_add,←he]
    grind

theorem sqDistance_lt {a b : Nat} (ha : a<128) (hb : b<128) : sqDistance a b < 32768 := by
  have h1 : a-b<128 := by omega
  have h2 : b-a<128 := by omega
  have x := Nat.mul_lt_mul_of_lt_of_lt h1 h1
  have y := Nat.mul_lt_mul_of_lt_of_lt h2 h2
  unfold sqDistance
  omega

theorem sqDistance_zero {a b : Nat} (h : sqDistance a b=0) : a=b := by
  unfold sqDistance at h
  have x : (a-b)*(a-b)=0 := by omega
  have y : (b-a)*(b-a)=0 := by omega
  have xx := Nat.mul_eq_zero.mp x
  have yy := Nat.mul_eq_zero.mp y
  omega

/-- A bounded natural prefix sum, used to rule out field wraparound. -/
def smallSum (f : Nat→Nat) : Nat→Nat
  | 0 => 0
  | n+1 => smallSum f n + f n

theorem smallSum_lt (f : Nat→Nat) (n : Nat) (h : ∀ k,k<n → f k<32768) :
    smallSum f n ≤ n*32768 := by
  induction n with
  | zero => simp [smallSum]
  | succ n ih =>
    have hi := ih (fun k hk => h k (by omega))
    have hn := h n (by omega)
    simp only [smallSum,Nat.add_mul,Nat.one_mul]
    omega

theorem smallSum_zero (f : Nat→Nat) (n : Nat) (h : smallSum f n=0) : ∀ k,k<n → f k=0 := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [smallSum] at h
    intro k hk
    by_cases he : k=n
    · subst k; omega
    · exact ih (by omega) k (by omega)

end ZkFormal.NearV3.RcptV3Proof

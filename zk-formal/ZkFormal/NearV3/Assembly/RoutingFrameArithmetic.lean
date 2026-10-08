import ZkFormal.NearV3.Assembly.RoutingFrame

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl

theorem frameBit_boolean (x j : Nat) : frameBit x j=0 ∨ frameBit x j=1 := by
  have hb : (x/2^j)%2=0 ∨ (x/2^j)%2=1 := by omega
  rcases hb with hb|hb <;> simp only [frameBit,hb] <;> (first | exact Or.inl rfl | exact Or.inr rfl)

/-- Same elementary bit-sum identity used by the existing receipt arithmetic
toolkit, specialized here without importing the old receipt renderer. -/
theorem frame_bitsVal (x : Nat) : ∀len,bitsVal (fun j=>(x/2^j)%2) 0 len=x%2^len
  | 0=>by simp [bitsVal, Nat.mod_one]
  | len+1=>by
    rw [bitsVal,frame_bitsVal x len,Nat.zero_add,Nat.pow_succ,Nat.mod_mul]

theorem frame_diff_bound (a b : UInt8) : a.toNat+255-b.toNat<512 := by
  have := a.toNat_lt
  have := b.toNat_lt
  omega

theorem frame_diff_cast (a b : UInt8) :
    Fp.ofNat (a.toNat+255-b.toNat)=(a.toNat:Fp)-(b.toNat:Fp)+255 := by
  have hb := b.toNat_lt
  have hnat : a.toNat+255-b.toNat+b.toNat=a.toNat+255 := by omega
  have h := congrArg (fun n : Nat=>(n:Fp)) hnat
  change ((a.toNat+255-b.toNat:Nat):Fp)=(a.toNat:Fp)-(b.toNat:Fp)+255
  grind

theorem frame_diff_high (a b : UInt8) (hle : b.toNat≤a.toNat) (hne : a≠b) :
    (a.toNat+255-b.toNat)/256%2=1 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hn : a.toNat≠b.toNat := by intro h; exact hne (UInt8.toNat_inj.mp h)
  omega

theorem frame_diff_inverse (a b : UInt8) :
    let d := (a.toNat:Fp)-(b.toNat:Fp)
    let e : Fp := if a=b then 1 else 0
    d*d⁻¹=1-e ∧ e*d=0 := by
  dsimp only
  by_cases he : a=b
  · subst b; simp only [ite_true]
    have hz : (a.toNat:Fp)-(a.toNat:Fp)=0 := by grind
    rw [hz]; constructor <;> grind
  · simp only [if_neg he]
    have hn : (a.toNat:Fp)-(b.toNat:Fp)≠0 := by
      intro h
      have hf : (a.toNat:Fp)=(b.toNat:Fp) := by grind
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      have heq : a.toNat=b.toNat := ofNat_inj (by unfold P;omega) (by unfold P;omega) hf
      exact he (UInt8.toNat_inj.mp heq)
    rw [Fp.mul_inv_cancel hn]
    constructor <;> grind

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout

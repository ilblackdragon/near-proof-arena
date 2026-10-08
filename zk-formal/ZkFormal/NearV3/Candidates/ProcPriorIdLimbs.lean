import ZkFormal.NearV3.Candidates.ProcPriorCanonical
namespace ZkFormal.NearV3.Candidates.ProcPriorIdLimbs
open ZkFormal.Algebra

def lo (n : Nat) : Nat:=n%16777216
def mid (n : Nat) : Nat:=n/16777216%16777216
def hi (n : Nat) : Nat:=n/281474976710656

theorem bounds (n : Nat) (h:n<18446744073709551616) :
    lo n<16777216 ∧ mid n<16777216 ∧ hi n<65536 := by
  simp only [lo,mid,hi]
  omega

theorem reconstruct (n : Nat) : lo n+16777216*mid n+281474976710656*hi n=n := by
  unfold lo mid hi
  omega

theorem injective (a b : Nat) (hl:lo a=lo b) (hm:mid a=mid b) (hh:hi a=hi b) : a=b := by
  have ha:=reconstruct a
  have hb:=reconstruct b
  omega

theorem lex (a b : Nat) : a<b ↔
    hi a<hi b ∨ hi a=hi b ∧ (mid a<mid b ∨ mid a=mid b ∧ lo a<lo b) := by
  have ha:=reconstruct a
  have hb:=reconstruct b
  have hal:lo a<16777216:=Nat.mod_lt _ (by decide +kernel)
  have hbl:lo b<16777216:=Nat.mod_lt _ (by decide +kernel)
  have ham:mid a<16777216:=Nat.mod_lt _ (by decide +kernel)
  have hbm:mid b<16777216:=Nat.mod_lt _ (by decide +kernel)
  omega

theorem field_injective (a b : Nat) (ha:a<18446744073709551616) (hb:b<18446744073709551616)
    (hl:Fp.ofNat (lo a)=Fp.ofNat (lo b)) (hm:Fp.ofNat (mid a)=Fp.ofNat (mid b))
    (hh:Fp.ofNat (hi a)=Fp.ofNat (hi b)) : a=b := by
  obtain ⟨hal,ham,hah⟩:=bounds a ha
  obtain ⟨hbl,hbm,hbh⟩:=bounds b hb
  have hp:P>16777216:=by decide +kernel
  have eq (x y : Nat) (hx:x<16777216) (hy:y<16777216) (he:Fp.ofNat x=Fp.ofNat y) : x=y := by
    have hn:=congrArg Fp.toNat he
    simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : x<P),Nat.mod_eq_of_lt (by omega : y<P)] using hn
  exact injective a b (eq _ _ hal hbl hl) (eq _ _ ham hbm hm) (eq _ _ (by omega) (by omega) hh)

theorem packed_top_injective (ta tb a b : Nat) (hta:ta<33) (htb:tb<33)
    (ha:a<18446744073709551616) (hb:b<18446744073709551616)
    (he:Fp.ofNat (65536*ta+hi a)=Fp.ofNat (65536*tb+hi b)) : ta=tb ∧ hi a=hi b := by
  have hha:=(bounds a ha).2.2
  have hhb:=(bounds b hb).2.2
  have hp:P>2162688:=by decide +kernel
  have hn:=congrArg Fp.toNat he
  simp only [Fp.toNat_ofNat] at hn
  rw [Nat.mod_eq_of_lt (by omega : 65536*ta+hi a<P),
    Nat.mod_eq_of_lt (by omega : 65536*tb+hi b<P)] at hn
  omega

end ZkFormal.NearV3.Candidates.ProcPriorIdLimbs

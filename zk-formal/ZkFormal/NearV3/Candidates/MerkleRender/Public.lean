import ZkFormal.NearV3.Candidates.MerkleLift

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- The prepared little-endian public count denotes exactly the native count. -/
theorem public_count (tr : Trace Fp) (tt r n : Nat) (pub : List Fp)
    (hn : n<256^4)
    (hp : ∀ i<4, pub.getD (PH_N+i) 0=Fp.ofNat (n/256^i%256)) :
    MerkleEmpty.countE.eval tr tt r pub=Fp.ofNat n := by
  change (Fp.ofNat 1 * pub.getD (PH_N+0) 0 +
    (Fp.ofNat 256 * pub.getD (PH_N+1) 0 +
    (Fp.ofNat 65536 * pub.getD (PH_N+2) 0 +
    (Fp.ofNat 16777216 * pub.getD (PH_N+3) 0 + Fp.ofNat 0))))=Fp.ofNat n
  rw [hp 0 (by omega),hp 1 (by omega),hp 2 (by omega),hp 3 (by omega)]
  simp only [ofNat_mul',ofNat_add']
  apply congrArg Fp.ofNat
  simp only [Nat.reducePow,Nat.pow_zero,Nat.div_one,Nat.one_mul] at hn ⊢
  omega

theorem native_count_nonzero {n : Nat} (hn : 1≤n) (hm : n≤4481) : Fp.ofNat n≠0 := by
  intro he
  have hh := congrArg Fp.toNat he
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega),Fp.toNat_zero] at hh
  omega

end ZkFormal.NearV3.Candidates.MerkleRender

import ZkFormal.NearV3.Qv.Extract.NativeNibbleLookup

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Membership in an authenticated native key stream determines the exact
natural position and symbol; the field cannot alias positions below P. -/
theorem repaired_key_lookup (id : Fp) (bs : NearSpec.Bytes)
    (hb : 2*bs.length<P) {id' sym last : Fp} {j : Nat} (hj : j<P)
    (hm : [id',(j:Fp),sym,last]∈repairedKeyTraffic id bs) :
    id'=id ∧ ((j<2*bs.length ∧ sym=((NearSpec.nibbles bs).getD j 0:Nat) ∧ last=0) ∨
      (j=2*bs.length ∧ sym=(SYM_END:Nat) ∧ last=1)) := by
  obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp hm
  have hi := List.mem_range.mp hi
  simp only [repairedKeyRow,List.mem_append] at hm
  rcases hm with hm|hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with hm|hm
    · have he := List.cons.inj hm
      have hp := List.cons.inj he.2
      have hs := List.cons.inj hp.2
      have hl := List.cons.inj hs.2
      have hpos : j=2*i := by
        apply ofNat_inj hj (by omega)
        change Fp.ofNat j=Fp.ofNat (2*i)
        rw [←ofNat_mul']
        exact hp.1
      refine ⟨he.1,Or.inl ⟨by omega,?_,hl.1⟩⟩
      rw [hpos,native_nibble_high]
      exact hs.1
    · have he := List.cons.inj hm
      have hp := List.cons.inj he.2
      have hs := List.cons.inj hp.2
      have hl := List.cons.inj hs.2
      have hpos : j=2*i+1 := by
        apply ofNat_inj hj (by omega)
        change Fp.ofNat j=Fp.ofNat (2*i+1)
        rw [←ofNat_add',←ofNat_mul']
        exact hp.1
      refine ⟨he.1,Or.inl ⟨by omega,?_,hl.1⟩⟩
      rw [hpos,native_nibble_low]
      exact hs.1
  · split at hm
    next hend =>
      simp only [List.mem_singleton] at hm
      have he := List.cons.inj hm
      have hp := List.cons.inj he.2
      have hs := List.cons.inj hp.2
      have hl := List.cons.inj hs.2
      have hpos : j=2*i+2 := by
        apply ofNat_inj hj (by omega)
        change Fp.ofNat j=Fp.ofNat (2*i+2)
        rw [←ofNat_add',←ofNat_mul']
        exact hp.1
      exact ⟨he.1,Or.inr ⟨by omega,hs.1,hl.1⟩⟩
    next => simp at hm

end ZkFormal.NearV3.Qv.Extract

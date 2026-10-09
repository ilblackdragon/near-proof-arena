import ZkFormal.NearV3.Qv.Extract.NativeShardBalance

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3

/-- Native QSH messages distinguish the count packet from byte packets by position. -/
theorem native_shard_member {tau id entry pos value : Fp} {ss : List Nat}
    (hm : [id,entry,pos,value]∈nativeShardMessages tau ss) :
    id=tau ∧ ((entry=0 ∧ pos=8 ∧ value=(ss.length:Fp)) ∨
      ∃ j : Nat, j<ss.length ∧ ∃ i : Nat, i<8 ∧ entry=(j:Fp) ∧ pos=(i:Fp) ∧
        value=(((u64 (ss.getD j 0)).getD i 0).toNat:Fp)) := by
  simp only [nativeShardMessages,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with hm|hm
  · simp only [List.cons.injEq] at hm
    exact ⟨hm.1,Or.inl ⟨hm.2.1,hm.2.2.1,hm.2.2.2.1⟩⟩
  · obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hm
    simp only [List.cons.injEq] at he
    exact ⟨he.1.symm,Or.inr ⟨j,List.mem_range.mp hj,i,List.mem_range.mp hi,
      he.2.1.symm,he.2.2.1.symm,he.2.2.2.1.symm⟩⟩

private theorem small_nat_cast {n : Nat} (hn : n<8) : ((n:Fp)).toNat=n := by
  change (Fp.ofNat n).toNat=n
  have hp : 8<Algebra.P := by decide
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show n<Algebra.P by omega)]

/-- A count-position lookup can never be satisfied by a shard byte. -/
theorem native_shard_count {tau id value : Fp} {ss : List Nat}
    (hm : [id,0,8,value]∈nativeShardMessages tau ss) :
    id=tau ∧ value=(ss.length:Fp) := by
  obtain ⟨hid,h⟩ := native_shard_member hm
  refine ⟨hid,?_⟩
  rcases h with h|⟨j,hj,i,hi,he,hpos,hv⟩
  · exact h.2.2
  · have hp := congrArg Fp.toNat hpos
    rw [small_nat_cast hi] at hp
    have h8 : (8:Fp).toNat=8 := by decide
    rw [h8] at hp
    omega

/-- Byte-position lookups return a real native shard byte at that exact position. -/
theorem native_shard_byte {tau id entry value : Fp} {ss : List Nat} {i : Nat}
    (hi : i<8) (hm : [id,entry,(i:Fp),value]∈nativeShardMessages tau ss) :
    id=tau ∧ ∃ j : Nat, j<ss.length ∧ entry=(j:Fp) ∧
      value=(((u64 (ss.getD j 0)).getD i 0).toNat:Fp) := by
  obtain ⟨hid,h⟩ := native_shard_member hm
  refine ⟨hid,?_⟩
  rcases h with h|⟨j,hj,k,hk,he,hpos,hv⟩
  · have hp := congrArg Fp.toNat h.2.1
    rw [small_nat_cast hi] at hp
    have h8 : (8:Fp).toNat=8 := by decide
    rw [h8] at hp
    omega
  · have hp := congrArg Fp.toNat hpos
    rw [small_nat_cast hi,small_nat_cast hk] at hp
    subst k
    exact ⟨j,hj,he,hv⟩

/-- Canonical entry indices cannot alias a different shard occurrence. -/
theorem native_shard_byte_index {tau id value : Fp} {ss : List Nat} {j i : Nat}
    (hlen : ss.length<Algebra.P) (hj : j<Algebra.P) (hi : i<8)
    (hm : [id,(j:Fp),(i:Fp),value]∈nativeShardMessages tau ss) :
    id=tau ∧ j<ss.length ∧ value=(((u64 (ss.getD j 0)).getD i 0).toNat:Fp) := by
  obtain ⟨hid,k,hk,he,hv⟩ := native_shard_byte hi hm
  have hkp : k<Algebra.P := by omega
  have hn := congrArg Fp.toNat he
  change (Fp.ofNat j).toNat=(Fp.ofNat k).toNat at hn
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hkp] at hn
  subst k
  exact ⟨hid,hk,hv⟩

/-- Canonical native lengths decode exactly, without a field-wrap assumption. -/
theorem native_shard_count_nat {tau id value : Fp} {ss : List Nat}
    (hlen : ss.length<Algebra.P) (hm : [id,0,8,value]∈nativeShardMessages tau ss) :
    id=tau ∧ value.toNat=ss.length := by
  obtain ⟨hid,hv⟩ := native_shard_count hm
  refine ⟨hid,?_⟩
  rw [hv]
  change (Fp.ofNat ss.length).toNat=ss.length
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hlen]

end ZkFormal.NearV3.Qv.Extract.Parser

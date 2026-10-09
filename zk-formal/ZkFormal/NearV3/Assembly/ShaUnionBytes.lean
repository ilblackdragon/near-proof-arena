import ZkFormal.NearV3.Assembly.ShaUnionFacts

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Every byte received by any locally valid physical SHA table is a real byte,
including received bytes whose message has no exported digest. -/
theorem shaCountAt_byte_range {tr : Trace Fp} {pub : List Fp} {t : Nat}
    (hL : Sha.ShaLocal tr t pub) {id pos byte : Fp}
    (hm : 0<shaCountAt tr pub t false B_BYTES [id,pos,byte]) : byte.toNat<256 := by
  simp only [shaCountAt,tableBusCount_eq] at hm
  have hm := mem_of_count_pos hm
  simp only [List.mem_flatMap,rowTraffic,List.mem_range] at hm
  obtain ⟨r,hr,i,hi,hmi⟩ := hm
  simp only [Sha.Table.interactions,List.mem_append,List.mem_map,List.mem_range,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with ⟨q,hq,rfl⟩|rfl
  · simp only [ite_true] at hmi
    obtain ⟨_,he⟩ := List.mem_replicate.mp hmi
    have hb := congrArg (fun xs : List Fp=>xs.getD 2 0) he
    simp only [Interaction.msgVal,List.map_cons,List.map_nil,List.getD_cons_succ,
      List.getD_cons_zero] at hb
    have hK := Sha.Sound.kindStmt tr t pub hL
    rw [Sha.Frame.ev_byteE hK hr hq] at hb
    have hlt := Sha.Frame.byteAt_lt (tr:=tr) (t:=t) r q
    have hP : Sha.View.byteAt tr t r q<ZkFormal.Algebra.P := by
      exact Nat.lt_trans hlt (by decide)
    rw [hb]
    simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt hP] using hlt
  · simp at hmi

/-- Range survives summing over the explicitly allowed physical SHA tables. -/
theorem shaUnion_byte_range {tr : Trace Fp} {pub : List Fp} (ts : List Nat)
    (hL : ∀t∈ts,Sha.ShaLocal tr t pub) {id pos byte : Fp}
    (hm : 0<shaUnionCount tr pub ts false B_BYTES [id,pos,byte]) : byte.toNat<256 := by
  induction ts with
  | nil => simp [shaUnionCount] at hm
  | cons t ts ih =>
    by_cases hp : 0<shaCountAt tr pub t false B_BYTES [id,pos,byte]
    · exact shaCountAt_byte_range (hL t (by simp)) hp
    · apply ih (fun u hu=>hL u (by simp [hu]))
      simp only [shaUnionCount] at hm
      omega

end ZkFormal.NearV3.Assembly

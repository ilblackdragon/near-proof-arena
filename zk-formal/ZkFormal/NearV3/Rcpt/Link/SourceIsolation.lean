import ZkFormal.NearV3.Rcpt.Link.SourcePayload
import ZkFormal.Near.Link.ShaCore

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra

/-- Every source payload has a canonical message id, including the last path node. -/
theorem source_payload_id_lt {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) : msgId K_SRC p.1 < P := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hB
  exact source_msgId_lt h i p.1 hi (source_payload_range h (List.getElem_mem hi) hp).2

/-- Equality of field message ids identifies one source payload globally. -/
theorem source_payload_field_unique {bs : List SrcpB} (h : SrcpWf bs)
    {B C : SrcpB} (hB : B ∈ bs) (hC : C ∈ bs)
    {p p' : Nat × List Nat} (hp : p ∈ sourcePayloads B) (hp' : p' ∈ sourcePayloads C)
    (he : Fp.ofNat (msgId K_SRC p.1) = Fp.ofNat (msgId K_SRC p'.1)) : p = p' := by
  have hn := Near.Link.ofNat_inj (source_payload_id_lt h hB hp) (source_payload_id_lt h hC hp') he
  have hq : p.1 = p'.1 := by unfold msgId at hn; omega
  have hr := source_payload_range h hB hp
  have hr' := source_payload_range h hC hp'
  obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hB
  obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.mp hC
  have hij : i = j := by
    by_cases hij : i < j
    · have ho := source_interval_before h i j hi hj hij
      rw [hbi, hcj] at ho; omega
    · by_cases hji : j < i
      · have ho := source_interval_before h j i hj hi hji
        rw [hbi, hcj] at ho; omega
      · omega
  subst j
  have hBC : B = C := hbi.symm.trans hcj
  have hd := source_payload_unique h hB hp (hBC.symm ▸ hp') hq
  exact Prod.ext hq hd

/-- A field-selected source byte send is a byte of the unique matching payload. -/
theorem source_bytes_isolate {bs : List SrcpB} (h : SrcpWf bs)
    {B : SrcpB} (hB : B ∈ bs) {p : Nat × List Nat} (hp : p ∈ sourcePayloads B)
    {m : Msg} (hm : m ∈ (srcpTraffic bs).sends B_BYTES)
    {a : Nat} (ha : m.head? = some a)
    (he : Fp.ofNat a = Fp.ofNat (msgId K_SRC p.1)) :
    ∃ j, j < p.2.length ∧ m = [msgId K_SRC p.1, j, p.2.getD j 0] := by
  simp only [srcpTraffic, show B_BYTES ≠ B_SIZE by decide, ite_false] at hm
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp hm
  rw [source_block_bytes] at hm
  obtain ⟨p', hp', hm⟩ := List.mem_flatMap.mp hm
  simp only [emitAt, List.mem_map, List.mem_range] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst a
  have hpp := source_payload_field_unique h hC hB hp' hp he
  subst p'
  exact ⟨j, hj, by simp⟩

end ZkFormal.NearV3

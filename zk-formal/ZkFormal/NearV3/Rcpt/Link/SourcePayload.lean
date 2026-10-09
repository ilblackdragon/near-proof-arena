import ZkFormal.NearV3.Rcpt.Link.SourceIndex

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra

/-- A source block's leaf rehash and subsequent Merkle-node hash inputs. -/
def sourcePayloads (B : SrcpB) : List (Nat × List Nat) :=
  [(B.ql, B.leaf)] ++ B.path.map (fun it => (it.q, it.bytes))

/-- The source table has no other BYTES sends. -/
theorem source_block_bytes (B : SrcpB) :
    srcpBlockMsgs B B_BYTES true = (sourcePayloads B).flatMap (fun p => emitAt (msgId K_SRC p.1) 0 p.2) := by
  simp [srcpBlockMsgs, srcpRootMsgs, srcpLeafMsgs, srcpItemMsgs, sourcePayloads,
    B_BYTES, B_DIGEST, B_RCL, B_SRC, List.flatMap_map, Function.comp_def]

/-- Payload message numbers stay in their owning block's interval. -/
theorem source_payload_range {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) : B.ql ≤ p.1 ∧ p.1 ≤ B.lastQ := by
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · simp [SrcpB.lastQ]
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hit
    have hq := (h.items B hB i hi).1
    rw [he] at hq
    simp only [SrcpB.lastQ]
    omega

/-- No two payloads inside one block can disagree at the same message number. -/
theorem source_payload_unique {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p p' : Nat × List Nat} (hp : p ∈ sourcePayloads B) (hp' : p' ∈ sourcePayloads B)
    (he : p.1 = p'.1) : p.2 = p'.2 := by
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp hp'
  rcases hp with rfl | ⟨a, ha, rfl⟩ <;> rcases hp' with rfl | ⟨b, hb, rfl⟩
  · rfl
  · obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.mp hb
    have hq := (h.items B hB i hi).1
    rw [hh] at hq
    simp only [Prod.fst] at he
    omega
  · obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.mp ha
    have hq := (h.items B hB i hi).1
    rw [hh] at hq
    simp only [Prod.fst] at he
    omega
  · obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hj, hh'⟩ := List.mem_iff_getElem.mp hb
    have hq := (h.items B hB i hi).1
    have hq' := (h.items B hB j hj).1
    rw [hh] at hq
    rw [hh'] at hq'
    simp only [Prod.fst] at he
    have hij : i = j := by omega
    subst j
    have hab : a = b := hh.symm.trans hh'
    exact congrArg SrcpItem.bytes hab

end ZkFormal.NearV3

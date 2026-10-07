import ZkFormal.NearV3.Rcpt.Link.SourceIsolation

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Source hash payloads are exactly 32 or 64 limbs. -/
theorem source_payload_length {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) : p.2.length = 32 ∨ p.2.length = 64 := by
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · exact Or.inl (h.len B hB).2.1
  · right
    have hs := ((h.len B hB).2.2 it hit).1
    have ha := ((h.len B hB).2.2 it hit).2
    cases hd : it.dir <;> simp [SrcpItem.bytes, hd, hs, ha]

theorem source_payload_canon {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) : ∀ x ∈ p.2, x < P := by
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · intro x hx
    exact (h.canon B hB).2.2.1 x (List.mem_append.mpr (Or.inr hx))
  · intro x hx
    have hc := (h.canon B hB).2.2.2 it hit x
    cases hd : it.dir <;> simp only [SrcpItem.bytes, hd, Bool.false_eq_true, ite_false, ite_true] at hx
    · exact hc hx
    · exact hc (by simpa [List.mem_append, or_comm] using hx)

/-- SHA's closed digest contract reconstructs a source payload from exact byte traffic.
Other senders must have canonical ids of a different kind; no collision-resistance premise is used. -/
theorem source_sha_digest {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt ((srcpTraffic bs).sends B_BYTES ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_SRC)
    {d : List Nat} (hd : ∀ x ∈ d, x < P)
    (hrecv : 0 < shaS B_DIGEST (digMsg (msgId K_SRC p.1) p.2.length d).toFp) :
    Bytes8 p.2 ∧ d = (sha256 (toBytes p.2)).map UInt8.toNat := by
  have hid := source_payload_id_lt h hB hp
  have hlen : p.2.length < P := by
    rcases source_payload_length h hB hp with hh | hh <;> rw [hh] <;> decide
  apply Near.Link.sha_core hsha _ hbytes hid (source_payload_canon h hB hp) hlen hd _ hrecv
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · exact source_bytes_isolate h hB hp hm ha he
  · have hh := hother m hm a ha
    have hn := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_SRC p.1 % 16 = K_SRC := by simp [msgId, K_SRC, Nat.add_mod]
    exact False.elim (hh.2 (hn ▸ hk))

end ZkFormal.NearV3

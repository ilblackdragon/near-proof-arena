import ZkFormal.NearV3.Rcpt.Candidates.DedupPayloadIsolation
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Algebra NearSpec
/-- A field-selected source byte send is a byte of the unique matching payload. -/
theorem payload_bytes_isolate {bs : List SrcpB} (h : PayloadWf bs)
    {B : SrcpB} (hB : B ∈ bs) {p : Nat × List Nat} (hp : p ∈ payloads B)
    {m : Msg} (hm : m ∈ payloadBytes bs)
    {a : Nat} (ha : m.head? = some a)
    (he : Fp.ofNat a = Fp.ofNat (msgId K_SRC p.1)) :
    ∃ j, j < p.2.length ∧ m = [msgId K_SRC p.1, j, p.2.getD j 0] := by
  simp only [payloadBytes, List.mem_flatMap] at hm
  obtain ⟨p', ⟨C, hC, hp'⟩, hm⟩ := hm
  simp only [emitAt, List.mem_map, List.mem_range] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst a
  have hpp := payload_field_unique h hC hB hp' hp he
  subst p'
  exact ⟨j, hj, by simp⟩
/-- Source hash payloads are exactly 32 or 64 limbs. -/
theorem payload_length {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ payloads B) : p.2.length = 32 ∨ p.2.length = 64 := by
  obtain ⟨hdup, hp⟩ := payload_mem hp
  have hw := h.computed hB hdup
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · exact Or.inl (hw.len).2.1
  · right
    have hs := ((hw.len).2.2 it hit).1
    have ha := ((hw.len).2.2 it hit).2
    cases hd : it.dir <;> simp [SrcpItem.bytes, hd, hs, ha]

theorem payload_canon {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ payloads B) : ∀ x ∈ p.2, x < P := by
  obtain ⟨hdup, hp⟩ := payload_mem hp
  have hw := h.computed hB hdup
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · intro x hx
    exact (hw.canon).2.2.1 x (List.mem_append.mpr (Or.inr hx))
  · intro x hx
    have hc := (hw.canon).2.2.2 it hit x
    cases hd : it.dir <;> simp only [SrcpItem.bytes, hd, Bool.false_eq_true, ite_false, ite_true] at hx
    · exact hc hx
    · exact hc (by simpa [List.mem_append, or_comm] using hx)

/-- SHA's closed digest contract reconstructs a source payload from exact byte traffic.
Other senders must have canonical ids of a different kind; no collision-resistance premise is used. -/
theorem sha_digest {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ payloads B)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt (payloadBytes bs ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_SRC)
    {d : List Nat} (hd : ∀ x ∈ d, x < P)
    (hrecv : 0 < shaS B_DIGEST (digMsg (msgId K_SRC p.1) p.2.length d).toFp) :
    Bytes8 p.2 ∧ d = (sha256 (toBytes p.2)).map UInt8.toNat := by
  have hid := payload_id_lt h hB hp
  have hlen : p.2.length < P := by
    rcases payload_length h hB hp with hh | hh <;> rw [hh] <;> decide
  apply Near.Link.sha_core hsha _ hbytes hid (payload_canon h hB hp) hlen hd _ hrecv
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm | hm
  · exact payload_bytes_isolate h hB hp hm ha he
  · have hh := hother m hm a ha
    have hn := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_SRC p.1 % 16 = K_SRC := by simp [msgId, K_SRC, Nat.add_mod]
    exact False.elim (hh.2 (hn ▸ hk))

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof

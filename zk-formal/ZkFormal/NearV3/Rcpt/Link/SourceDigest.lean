import ZkFormal.NearV3.Rcpt.Link.SourceSha

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Executable lookup of the uniquely indexed source SHA input. -/
def sourceEncoding (bs : List SrcpB) (q : Nat) : List Nat :=
  (((bs.flatMap sourcePayloads).find? (fun p => p.1 == q)).map Prod.snd).getD []

def sourceDigest (bs : List SrcpB) (q : Nat) : Bytes := sha256 (toBytes (sourceEncoding bs q))

/-- Index isolation makes lookup recover any actual source payload. -/
theorem sourceEncoding_eq {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) : sourceEncoding bs p.1 = p.2 := by
  have hm : p ∈ bs.flatMap sourcePayloads := List.mem_flatMap.mpr ⟨B, hB, hp⟩
  unfold sourceEncoding
  cases hf : (bs.flatMap sourcePayloads).find? (fun x => x.1 == p.1) with
  | none =>
    have hn := List.find?_eq_none.mp hf p hm
    simp at hn
  | some p' =>
    have hm' := List.mem_of_find?_eq_some hf
    obtain ⟨C, hC, hp'⟩ := List.mem_flatMap.mp hm'
    have he : p'.1 = p.1 := by simpa using List.find?_some hf
    have hh := source_payload_field_unique h hC hB hp' hp (by rw [he])
    simp [hh]

theorem sourceDigest_eq {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) :
    sourceDigest bs p.1 = sha256 (toBytes p.2) := by
  rw [sourceDigest, sourceEncoding_eq h hB hp]

/-- SHA digest outputs reconstruct the canonical source digest as spec bytes. -/
theorem source_sha_digest_bytes {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt ((srcpTraffic bs).sends B_BYTES ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_SRC)
    {d : List Nat} (hd : ∀ x ∈ d, x < P)
    (hrecv : 0 < shaS B_DIGEST (digMsg (msgId K_SRC p.1) p.2.length d).toFp) :
    toBytes d = sourceDigest bs p.1 := by
  have hh := (source_sha_digest h hB hp hsha others hbytes hother hd hrecv).2
  rw [hh, sourceDigest_eq h hB hp]
  simp [toBytes, List.map_map, Function.comp_def, UInt8.ofNat_toNat]

end ZkFormal.NearV3

import ZkFormal.NearV3.Rcpt.Candidates.DedupPayloadView
import ZkFormal.Near.Link.ShaCore
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
/-- Payload message numbers stay in their owning block's interval. -/
theorem block_payload_range {B : SrcpB} (h : BlockWf B)
    {p : Nat × List Nat} (hp : p ∈ sourcePayloads B) : B.ql ≤ p.1 ∧ p.1 ≤ B.lastQ := by
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · simp [SrcpB.lastQ]
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hit
    have hq := (h.items i hi).1
    rw [he] at hq
    simp only [SrcpB.lastQ]
    omega

/-- No two payloads inside one block can disagree at the same message number. -/
theorem block_payload_unique {B : SrcpB} (h : BlockWf B)
    {p p' : Nat × List Nat} (hp : p ∈ sourcePayloads B) (hp' : p' ∈ sourcePayloads B)
    (he : p.1 = p'.1) : p.2 = p'.2 := by
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp hp'
  rcases hp with rfl | ⟨a, ha, rfl⟩ <;> rcases hp' with rfl | ⟨b, hb, rfl⟩
  · rfl
  · obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.mp hb
    have hq := (h.items i hi).1
    rw [hh] at hq
    simp only [Prod.fst] at he
    omega
  · obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.mp ha
    have hq := (h.items i hi).1
    rw [hh] at hq
    simp only [Prod.fst] at he
    omega
  · obtain ⟨i, hi, hh⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hj, hh'⟩ := List.mem_iff_getElem.mp hb
    have hq := (h.items i hi).1
    have hq' := (h.items j hj).1
    rw [hh] at hq
    rw [hh'] at hq'
    simp only [Prod.fst] at he
    have hij : i = j := by omega
    subst j
    have hab : a = b := hh.symm.trans hh'
    exact congrArg SrcpItem.bytes hab

theorem payload_range {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B∈bs)
    {p : Nat × List Nat} (hp : p∈payloads B) : B.ql≤p.1 ∧ p.1≤B.qe := by
  obtain ⟨hd, hp⟩ := payload_mem hp
  have hw := h.computed hB hd
  rw [hw.root.1]
  exact block_payload_range hw hp

theorem payload_id_lt {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B∈bs)
    {p : Nat × List Nat} (hp : p∈payloads B) : msgId K_SRC p.1<P := by
  have hh := (payload_range h hB hp).2
  have hid := h.ids B hB
  unfold msgId at *
  omega

/-- Field equality identifies a unique computed payload; skips emit none. -/
theorem payload_field_unique {bs : List SrcpB} (h : PayloadWf bs)
    {B C : SrcpB} (hB : B∈bs) (hC : C∈bs)
    {p p' : Nat × List Nat} (hp : p∈payloads B) (hp' : p'∈payloads C)
    (he : Fp.ofNat (msgId K_SRC p.1)=Fp.ofNat (msgId K_SRC p'.1)) : p=p' := by
  have hn := Near.Link.ofNat_inj (payload_id_lt h hB hp) (payload_id_lt h hC hp') he
  have hq : p.1=p'.1 := by unfold msgId at hn; omega
  have hr := payload_range h hB hp
  have hr' := payload_range h hC hp'
  obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hB
  obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.mp hC
  have hij : i=j := by
    by_cases hij : i<j
    · have ho := h.interval_before i j hi hj hij
      rw [hbi, hcj] at ho; omega
    · by_cases hji : j<i
      · have ho := h.interval_before j i hj hi hji
        rw [hbi, hcj] at ho; omega
      · omega
  subst j
  have hBC : B=C := hbi.symm.trans hcj
  have hbp := payload_mem hp
  have hd := block_payload_unique (h.computed (hbi ▸ List.getElem_mem hi) hbp.1)
    hbp.2 (hBC.symm ▸ (payload_mem hp').2) hq
  exact Prod.ext hq hd

/-- Exact natural byte messages emitted by all computed source payloads. -/
def payloadBytes (bs : List SrcpB) : List Msg :=
  (bs.flatMap payloads).flatMap (fun p => emitAt (msgId K_SRC p.1) 0 p.2)

theorem block_bytes (B : SrcpB) (rep : Bool) :
    DedupRender.blockMsgs B rep B_BYTES true =
      (payloads B).flatMap (fun p => emitAt (msgId K_SRC p.1) 0 p.2) := by
  cases hd : B.dup <;>
    simp [DedupRender.blockMsgs, DedupRender.rootMsgs, payloads, hd, sourcePayloads,
      srcpLeafMsgs, srcpItemMsgs, B_BYTES, B_DIGEST, B_RCL, B_SRC, List.flatMap_map,
      Function.comp_def]

theorem chain_bytes (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) :
    chainMsgs tr tt s bs B_BYTES true=payloadBytes bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih =>
    rw [chainMsgs, block_bytes, ih]
    simp [payloadBytes, List.flatMap_append]

theorem source_bytes (tr : Trace Fp) (tt : Nat) (bs : List SrcpB) :
    sourceMsgs tr tt bs B_BYTES true=payloadBytes bs := by
  simp only [sourceMsgs, show B_BYTES≠B_SIZE by decide, ite_false]
  exact chain_bytes tr tt 0 bs

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof

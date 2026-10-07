import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractProof
import ZkFormal.NearV3.Rcpt.Link.SourcePayload

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3

/-- A skipped occurrence has an empty SHA-input interval. -/
def payloads (B : SrcpB) : List (Nat × List Nat) :=
  if B.dup then [] else sourcePayloads B

/-- Facts needed by the SHA linker, independent of physical partition height. -/
structure PayloadWf (bs : List SrcpB) : Prop where
  blocks : ∀ B∈bs, if B.dup then B.L=12 ∧ B.path=[] ∧ B.le=0 ∧ B.qe+1=B.ql else BlockWf B
  next : ∀ i (hi : i+1<bs.length), bs[i+1].ql=bs[i].qe+1
  ids : ∀ B∈bs, msgId K_SRC B.qe<P

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem BlockSpan.qe_id_lt {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    msgId K_SRC B.qe<P := by
  cases h with
  | computed m hs ht hd hm =>
    have hq := block_end_q hL hs ht hd hm
    rw [← (block_wf hL hs ht hd hm).root.1] at hq
    rw [← hq]
    exact counter_id_lt hL hm.bound (Or.inr (segment_last_active hL hm.bound hm.sl_end))
  | skipped hs hd => exact counter_id_lt hL hs (Or.inl (duplicate_root hL hs hd))

theorem BlockChain.payload_wf {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    PayloadWf bs := by
  refine ⟨h.local hL, h.q_next hL, ?_⟩
  induction h with
  | last s n B hs hp =>
    intro B' hB; obtain rfl := List.mem_singleton.mp hB; exact hs.qe_id_lt hL
  | cons s n B hs bs e ht ih =>
    intro B' hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hs.qe_id_lt hL
    · exact ih B' hB

omit hL in
theorem PayloadWf.computed {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B∈bs)
    (hd : B.dup=false) : BlockWf B := by simpa [hd] using h.blocks B hB

omit hL in
theorem payload_mem {B : SrcpB} {p : Nat × List Nat} (hp : p∈payloads B) :
    B.dup=false ∧ p∈sourcePayloads B := by
  cases hd : B.dup <;> simp_all [payloads]

omit hL in
theorem PayloadWf.ql_le {bs : List SrcpB} (h : PayloadWf bs) {B : SrcpB} (hB : B∈bs) :
    B.ql≤B.qe+1 := by
  have hh := h.blocks B hB
  cases hd : B.dup
  · have hf := h.computed hB hd
    have hr := hf.root.1
    unfold SrcpB.lastQ at hr
    omega
  · simp only [hd, ite_true] at hh
    omega

omit hL in
/-- Empty skipped intervals do not create collisions between computed intervals. -/
theorem PayloadWf.interval_before {bs : List SrcpB} (h : PayloadWf bs)
    (i j : Nat) (hi : i<bs.length) (hj : j<bs.length) (hij : i<j) :
    bs[i].qe<bs[j].ql := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [h.next j hj]
    by_cases he : i=j
    · subst i; omega
    · have hh := ih (by omega) (by omega)
      have hq := h.ql_le (List.getElem_mem (show j<bs.length by omega))
      omega

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof

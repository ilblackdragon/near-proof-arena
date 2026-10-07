import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceVerify
import ZkFormal.NearV3.Rcpt.Candidates.SourcePublicBinding
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3
open NearSpecV3 (SrcList)

/-- Pair every extracted proof/skip with its actual root repetition bit. -/
def sourceViews (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) : List (SrcpB × Bool) :=
  match bs with
  | [] => []
  | B::tail => (B, repeatedAt tr tt s)::sourceViews tr tt (s+1+DedupRender.payloadRows B) tail

theorem sourceViews_blocks (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) :
    (sourceViews tr tt s bs).map Prod.fst=bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih => simp [sourceViews, ih]

theorem sourceViews_length (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) :
    (sourceViews tr tt s bs).length=bs.length := by
  have hh := congrArg List.length (sourceViews_blocks tr tt s bs)
  simpa using hh

theorem chain_src_records (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) :
    chainMsgs tr tt s bs B_SRC false=
      (sourceViews tr tt s bs).map (fun v => SourcePublic.viewRecord v.1 v.2) := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih =>
    rw [chainMsgs, ih]
    have hb : DedupRender.blockMsgs B (repeatedAt tr tt s) B_SRC false=
        [SourcePublic.viewRecord B (repeatedAt tr tt s)] := by
      cases hd : B.dup <;>
        simp [DedupRender.blockMsgs, DedupRender.rootMsgs, srcpLeafMsgs, srcpItemMsgs,
          SourcePublic.viewRecord, hd, B_SRC, B_BYTES, B_DIGEST, B_RCL]
    rw [hb]
    rfl

theorem source_src_records (tr : Trace Fp) (tt : Nat) (bs : List SrcpB) :
    sourceMsgs tr tt bs B_SRC false=
      (sourceViews tr tt 0 bs).map (fun v => SourcePublic.viewRecord v.1 v.2) := by
  simp only [sourceMsgs, show B_SRC≠B_SIZE by decide, ite_false]
  exact chain_src_records tr tt 0 bs

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

omit hL in
theorem BlockSpan.root_canon {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) :
    B.j<P ∧ ∀ x∈B.root, x<P := by
  cases h with
  | computed m hs ht hd hm =>
    refine ⟨Fp.toNat_lt _, ?_⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Fp.toNat_lt _
  | skipped hs hd =>
    refine ⟨Fp.toNat_lt _, ?_⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Fp.toNat_lt _

omit hL in
theorem BlockSpan.record_canon {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n) (rep : Bool) :
    Link.Canon (SourcePublic.viewRecord B rep) := by
  intro x hx
  simp only [SourcePublic.viewRecord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | hx
  · exact h.root_canon.1
  · cases B.dup <;> decide +kernel
  · cases rep <;> decide +kernel
  · exact h.root_canon.2 x hx

theorem BlockChain.views_facts {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e) :
    ∀ v∈sourceViews tr tt s bs,
      Link.Canon (SourcePublic.viewRecord v.1 v.2) ∧ (v.2=true → v.1.L=12) := by
  induction h with
  | last s n B hs hp =>
    intro v hv
    simp only [sourceViews, List.mem_cons, List.not_mem_nil, or_false] at hv
    subst v
    exact ⟨hs.record_canon _, hs.repeated_empty hL⟩
  | cons s n B hs bs e ht ih =>
    intro v hv
    simp only [sourceViews, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨hs.record_canon _, hs.repeated_empty hL⟩
    · rw [hs.render_rows] at ih
      apply ih v
      simpa only [Nat.add_assoc] using hv

/-- Candidate public count equality binds all extracted flags and roots and
fixes the exact number of occurrences. All repetition lengths follow locally. -/
theorem BlockChain.bind_public {e : Nat} {bs : List SrcpB} (h : BlockChain tr tt 0 bs e)
    (sources : List SrcList) (hlen : sources.length<P)
    (hbal : ∀ m, cnt (sourceMsgs tr tt bs B_SRC false) m=cnt (SourcePublic.records sources) m) :
    bs.length=sources.length ∧
    ∀ v∈sourceViews tr tt 0 bs,
      v.1.j<sources.length ∧ v.1.dup=Public.sourceDup sources v.1.j ∧
      v.2=sourceRepeated sources v.1.j ∧
      toBytes v.1.root=(sources.getD v.1.j ⟨[],0,[]⟩).root ∧
      (sourceRepeated sources v.1.j=true → v.1.L=12) := by
  have hb := hbal
  rw [source_src_records] at hb
  constructor
  · have hh := SourcePublic.bind_length hb
    simpa only [List.length_map, sourceViews_length] using hh
  · intro v hv
    have hf := h.views_facts hL v hv
    have hm : SourcePublic.viewRecord v.1 v.2∈
        (sourceViews tr tt 0 bs).map (fun v => SourcePublic.viewRecord v.1 v.2) :=
      List.mem_map.mpr ⟨v, hv, rfl⟩
    have hh := SourcePublic.bind_record hlen hb hm hf.1
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2,
      fun hp => hf.2 (hh.2.2.1.trans hp)⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof

import ZkFormal.NearV3.Rcpt.Link.SourceDuplicate
import ZkFormal.NearV3.Public.Source

/-! Isolated source-dedup metadata. These definitions do not change active public records.
The repetition bit covers every occurrence, including the first occurrence of a repeated key. -/
namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Publicly computable all-occurrence repetition metadata. -/
def sourceRepeated (sources : List SrcList) (j : Nat) : Bool :=
  decide (2 ≤ (sources.map SrcList.key).count (sources.getD j ⟨[],0,[]⟩).key)

private theorem repeated_split {α : Type} [BEq α] [LawfulBEq α] (key : α) :
    ∀ keys : List α, 2 ≤ keys.count key →
      ∃ pre mid post, keys = pre ++ key :: mid ++ key :: post
  | [], h => by simp at h
  | a :: rest, h => by
    classical
    by_cases he : a = key
    · subst a
      have hc : 0 < rest.count key := by simp only [List.count_cons_self] at h; omega
      obtain ⟨mid, post, hs⟩ := List.eq_append_cons_of_mem (List.count_pos_iff.mp hc)
      exact ⟨[], mid, post, by simp [hs]⟩
    · have hc : 2 ≤ rest.count key := by simpa [List.count_cons_of_ne he] using h
      obtain ⟨pre, mid, post, hs⟩ := repeated_split key rest hc
      exact ⟨a :: pre, mid, post, by simp [hs]⟩

/-- An already-seen key is marked repeated even though the marker also covers its first row. -/
theorem sourceDup_repeated (sources : List SrcList) {j : Nat} (hj : j < sources.length)
    (hd : Public.sourceDup sources j = true) : sourceRepeated sources j = true := by
  unfold Public.sourceDup at hd
  obtain ⟨s, hs, hk⟩ := List.any_eq_true.mp hd
  have hk : s.key = (sources.getD j ⟨[],0,[]⟩).key := by simpa using hk
  have hm : (sources.getD j ⟨[],0,[]⟩).key ∈ (sources.take j).map SrcList.key :=
    List.mem_map.mpr ⟨s, hs, hk⟩
  have hp := List.count_pos_iff.mpr hm
  have hdcomp := List.take_append_drop j sources
  have hdrop := List.drop_eq_getElem_cons hj
  have hcnt := congrArg (fun xs : List SrcList =>
    (xs.map SrcList.key).count (sources.getD j ⟨[],0,[]⟩).key) hdcomp
  rw [hdrop] at hcnt
  simp only [List.map_append, List.map_cons, List.count_append] at hcnt
  have hg : sources[j].key = (sources.getD j ⟨[],0,[]⟩).key := by
    rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩]
  rw [hg, List.count_cons_self] at hcnt
  simp only [sourceRepeated, decide_eq_true_eq]
  omega

/-- Replaying a key twice under the D0a routing and distinct-id conditions forces
its raw receipt list empty. This applies to the first occurrence as well as later ones. -/
theorem repeated_receipts_empty (keys : List Bytes) (key : Bytes)
    (receipts : Bytes → List Receipt) (route : Receipt → Bool)
    (hc : 2 ≤ keys.count key)
    (hr : ∀ r ∈ receipts key, route r = true)
    (hn : ((keys.flatMap (fun k => (receipts k).filter route)).map Receipt.receiptId).Nodup) :
    receipts key = [] := by
  obtain ⟨pre, mid, post, he⟩ := repeated_split key keys hc
  rw [he] at hn
  simp only [List.flatMap_append, List.flatMap_cons] at hn
  apply source_duplicate_empty route (pre.flatMap (fun k => (receipts k).filter route))
    (receipts key) (mid.flatMap (fun k => (receipts k).filter route))
    (post.flatMap (fun k => (receipts k).filter route)) hr
  simpa only [List.append_assoc] using hn

/-- Every marked occurrence has exactly the empty-list RC encoding length. -/
theorem sourceRepeated_length (sources : List SrcList) (j : Nat)
    (receipts : Bytes → List Receipt) (route : Receipt → Bool)
    (hc : sourceRepeated sources j = true)
    (hr : ∀ r ∈ receipts (sources.getD j ⟨[],0,[]⟩).key, route r = true)
    (hn : (((sources.map SrcList.key).flatMap (fun k => (receipts k).filter route)).map Receipt.receiptId).Nodup)
    (shard : Nat) :
    (u64 shard ++ encodeReceipts (receipts (sources.getD j ⟨[],0,[]⟩).key)).length = 12 := by
  have hc' : 2 ≤ (sources.map SrcList.key).count (sources.getD j ⟨[],0,[]⟩).key := by
    simpa only [sourceRepeated, decide_eq_true_eq] using hc
  rw [repeated_receipts_empty _ _ receipts route hc' hr hn]
  simp [encodeReceipts, concatAll, u64, u32, leN]

/-- Native consistency predicate proposed for prepared roots. Its completeness follows
from successful last-wins source verification, without collision resistance. -/
def sourceRootsConsistent (sources : List SrcList) : Bool :=
  sources.all (fun s => sources.all (fun t => !(s.key == t.key) || (s.root == t.root)))

theorem sourceRootsConsistent_of_verified (sources : List SrcList) (entries : List ProofEntry)
    (hv : ∀ s ∈ sources, ∃ e, lookupLast s.key entries = some e ∧ verifyReceiptProof s.root e = true) :
    sourceRootsConsistent sources = true := by
  simp only [sourceRootsConsistent, List.all_eq_true]
  intro s hs t ht
  by_cases he : s.key = t.key
  · obtain ⟨e, he', hv'⟩ := hv s hs
    obtain ⟨f, hf', hw'⟩ := hv t ht
    have hroot := source_roots_eq_of_lookupLast entries s.key t.key s.root t.root he e f he' hf' hv' hw'
    simp [he, hroot]
  · simp [he]

/-- Exact interpretation of the proposed native root check. -/
theorem sourceRootsConsistent_iff (sources : List SrcList) :
    sourceRootsConsistent sources = true ↔
      ∀ s ∈ sources, ∀ t ∈ sources, s.key = t.key → s.root = t.root := by
  simp only [sourceRootsConsistent, List.all_eq_true]
  constructor
  · intro h s hs t ht he
    simpa [he] using h s hs t ht
  · intro h s hs t ht
    by_cases he : s.key = t.key
    · simp [he, h s hs t ht he]
    · simp [he]

/-- Soundness of computing one representative per used key: every skipped occurrence
uses the same last-wins proof and equal public root. No encoded dictionary is removed. -/
theorem sources_verified_of_computed (sources computed : List SrcList)
    (entries : List ProofEntry)
    (hr : sourceRootsConsistent sources = true)
    (hmem : ∀ c ∈ computed, c ∈ sources)
    (hcover : ∀ s ∈ sources, ∃ c ∈ computed, c.key = s.key)
    (hv : ∀ c ∈ computed, ∃ e, lookupLast c.key entries = some e ∧ verifyReceiptProof c.root e = true) :
    ∀ s ∈ sources, ∃ e, lookupLast s.key entries = some e ∧ verifyReceiptProof s.root e = true := by
  intro s hs
  obtain ⟨c, hc, hk⟩ := hcover s hs
  obtain ⟨e, he, hp⟩ := hv c hc
  have heq := (sourceRootsConsistent_iff sources).mp hr c (hmem c hc) s hs hk
  exact ⟨e, by simpa only [hk] using he, by simpa only [heq] using hp⟩

end ZkFormal.NearV3.Rcpt.Candidates

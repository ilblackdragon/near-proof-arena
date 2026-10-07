import ZkFormal.NearV3.Rcpt.Candidates.SourceSizeEncoding
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRepeated
import ZkFormal.NearV3.Rcpt.Candidates.DictionaryCount

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 Render.SrcpGen

private theorem sum_cost_le {α : Type} (xs : List α) (dup : α → Bool)
    (cost full : α → Nat)
    (hd : ∀ x ∈ xs, dup x = true → cost x = 12)
    (hn : ∀ x ∈ xs, dup x = false → cost x = full x) :
    (xs.map cost).sum ≤ ((xs.filter fun x => !dup x).map full).sum + 12 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy => hd y (by simp [hy])) (fun y hy => hn y (by simp [hy]))
    cases hx : dup x with
    | false =>
      have he := hn x (by simp) hx
      simp only [List.map_cons, List.sum_cons, List.filter_cons, hx, Bool.not_false,
        ite_true, List.length_cons] at *
      omega
    | true =>
      have he := hd x (by simp) hx
      simp only [List.map_cons, List.sum_cons, List.filter_cons, hx, Bool.not_true,
        Bool.false_eq_true, ite_false, List.length_cons] at *
      omega

/-- Candidate SIZE is bounded by unique selected computation charges and at most
one empty header per public source occurrence. -/
theorem size_le_computed (sources : List SrcList) (entries : List ProofEntry)
    (hd : ∀ j, j < sources.length → Public.sourceDup sources j = true →
      (block sources entries j).L = 12) :
    DedupRender.size (blocks sources entries) ≤
      ((firstSourceEntries sources (entryAt sources entries)).map entrySizeCharge).sum +
        12 * sources.length := by
  have hh := sum_cost_le (List.range sources.length) (Public.sourceDup sources)
    (fun j => DedupRender.sizeStep (block sources entries j))
    (fun j => entrySizeCharge (entryAt sources entries j))
    (by
      intro j hj hdup
      have he := hd j (List.mem_range.mp hj) hdup
      simp only [DedupRender.sizeStep, block, blockOfProof] at *
      simp only [hdup, ite_true, Nat.add_zero]
      exact he)
    (by
      intro j hj hdup
      simp only [DedupRender.sizeStep, block, blockOfProof, hdup, Bool.false_eq_true,
        ite_false, proofItems_length, entrySizeCharge, encodeReceipts, encList])
  simpa only [DedupRender.size, blocks, List.map_map, Function.comp_def,
    firstSourceEntries, firstSourceIndices, List.length_range] using hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile

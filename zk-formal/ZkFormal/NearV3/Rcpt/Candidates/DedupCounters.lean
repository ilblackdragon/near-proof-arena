import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra Render.SrcpGen

private theorem sum_skip {α : Type} (xs : List α) (skip : α → Bool) (weight : α → Nat) :
    (xs.map fun a => if skip a then 0 else 1 + weight a).sum =
      (xs.filter fun a => !skip a).length + ((xs.filter fun a => !skip a).map weight).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    cases ha : skip a <;> simp only [List.map_cons, List.sum_cons, ha, Bool.false_eq_true,
      ↓reduceIte, List.filter_cons, Bool.not_true, Bool.not_false, List.length_cons, ih] <;> omega

/-- The source counter counts each computed leaf/path message once. -/
theorem message_count (sources : List SrcList) (entries : List ProofEntry) :
    ((List.range sources.length).map (messageWeight sources entries)).sum =
      computedLists sources entries + computedPaths sources entries := by
  simp only [computedLists, computedPaths, blocks, List.filter_map, List.length_map,
    List.map_map, Function.comp_def, block, blockOfProof, proofItems_length, messageWeight]
  exact sum_skip _ _ _

private theorem weighted_sublist {α : Type} (f : α → Nat) {xs ys : List α}
    (h : List.Sublist xs ys) : (xs.map f).sum ≤ (ys.map f).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a h ih => simp only [List.map_cons, List.sum_cons]; omega

theorem nextQ_bound (sources : List SrcList) (entries : List ProofEntry) {j : Nat}
    (hj : j ≤ sources.length) :
    nextQ sources entries j ≤ 1 + computedLists sources entries + computedPaths sources entries := by
  have ht := weighted_sublist (messageWeight sources entries) (List.take_sublist j (List.range sources.length))
  simp only [List.take_range, Nat.min_eq_left hj, message_count] at ht
  unfold nextQ
  omega

theorem nextQ_succ (sources : List SrcList) (entries : List ProofEntry) (j : Nat) :
    nextQ sources entries (j + 1) = nextQ sources entries j + messageWeight sources entries j := by
  simp only [nextQ, List.range_succ, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem computed_end (sources : List SrcList) (entries : List ProofEntry) (j : Nat)
    (hd : Public.sourceDup sources j = false) :
    (block sources entries j).qe + 1 = nextQ sources entries (j + 1) := by
  rw [nextQ_succ]
  simp only [block, blockOfProof, messageWeight, hd, Bool.false_eq_true, ↓reduceIte]
  omega

theorem duplicate_counter_stays (sources : List SrcList) (entries : List ProofEntry) (j : Nat)
    (hd : Public.sourceDup sources j = true) :
    nextQ sources entries (j + 1) = nextQ sources entries j := by
  rw [nextQ_succ]
  simp [messageWeight, hd]

/-- Counter ids remain canonical in the base field under the actual D0a raw budget. -/
theorem relD0a_counter_bound {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    {j : Nat} (hj : j ≤ p.lists.length) :
    nextQ p.lists w.entries j ≤ 256185 ∧ msgId K_SRC (nextQ p.lists w.entries j) < ZkFormal.Algebra.P := by
  have hc := (relD0a_work_bounds h hp hf hw).2.2
  have hq := nextQ_bound p.lists w.entries hj
  have hn : nextQ p.lists w.entries j ≤ 256185 := by omega
  refine ⟨hn, ?_⟩
  simp only [msgId, K_SRC, ZkFormal.Algebra.P]
  omega

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile

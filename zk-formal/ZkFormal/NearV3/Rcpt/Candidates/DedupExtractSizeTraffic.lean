import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractSizeGate

/-!
# Exact source-proof SIZE traffic

Each root contributes its list length and each path start contributes 33 bytes.
The prefix sum is related to the field accumulator by casting, without assuming
that the natural sum is below the field modulus. A global size bound is a later
link obligation, not an extra local-table assumption.
-/

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3

open SrcpProof (rowSize prefixSize)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem szStep {r : Nat} (hr : r + 1 < tr.height tt) :
    tr.cell tt (r + 1) sz = tr.cell tt r sz + tr.cell tt (r + 1) rt * tr.cell tt (r + 1) L +
      33 * (tr.cell tt (r + 1) sf * tr.cell tt (r + 1) sg * (1 - tr.cell tt (r + 1) lf)) := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (.mul .isTransition (sub (n sz) (sum [c sz, .mul (n rt) (n L),
      smul 33 (mul3 (n sf) (n sg) (Dsl.not (n lf)))]))) (by decide +kernel)
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_sum_cons, eval_sum_nil, eval_smul,
    eval_isTransition, SrcpProof.nxt hr, if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  grind


theorem rowSize_field {r : Nat} (hr : r < tr.height tt) :
    Fp.ofNat (rowSize tr tt r) = tr.cell tt r rt * tr.cell tt r L +
      33 * (tr.cell tt r sf * tr.cell tt r sg * (1 - tr.cell tt r lf)) := by
  have hb1 := isBool hL hr (x := rt) (by simp [SrcpProof.bools])
  have hb2 := isBool hL hr (x := sf) (by simp [SrcpProof.bools])
  have hb3 := isBool hL hr (x := sg) (by simp [SrcpProof.bools])
  have hb4 := isBool hL hr (x := lf) (by simp [SrcpProof.bools])
  rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2 <;>
    rcases hb3 with h3 | h3 <;> rcases hb4 with h4 | h4 <;>
    simp [rowSize, h1, h2, h3, h4, ← ofNat_add', Fp.ofNat_toNat, show Fp.ofNat 0 = (0 : Fp) from rfl,
      show Fp.ofNat 33 = (33 : Fp) from rfl] <;> grind

/-- The running field accumulator is the cast of the exact natural row sum. -/
theorem size_prefix {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r sz = Fp.ofNat (prefixSize tr tt (r + 1)) := by
  induction r with
  | zero =>
    have h0 := row0 hL
    have hs : tr.cell tt 0 sg = 0 := by
      have he := disjoint hL hr
      rw [h0.1] at he; grind
    simp [prefixSize, rowSize, h0.1, hs, h0.2.2.2, Fp.ofNat_toNat]
  | succ r ih =>
    rw [szStep hL hr, ih (by omega)]
    have he : prefixSize tr tt (r + 1 + 1) = prefixSize tr tt (r + 1) + rowSize tr tt (r + 1) := by
      simp [prefixSize, List.range_succ, List.map_append, List.sum_append, Nat.add_assoc]
    rw [he, ← ofNat_add', rowSize_field hL hr]
    grind

omit hL in
private theorem flatMap_at {α : Type} (v : List α) (n k : Nat) (hk : k < n) :
    (List.range n).flatMap (fun o => if o = k then v else []) = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases he : k = n
    · subst k
      have hz : (List.range n).flatMap (fun o => if o = n then v else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        simp [show o ≠ n by have := List.mem_range.mp ho; omega]
      rw [hz]; simp
    · rw [ih (by omega)]; simp [Ne.symm he]

/-- There is exactly one SIZE send, whose payload is the natural prefix sum cast to Fp. -/
theorem size_traffic : ∃ K, 0 < K ∧ K ≤ tr.height tt ∧
    (∀ r, r < K → tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) ∧
    (∀ r, K ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0) ∧
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub B_SIZE true) =
      [Msg.toFp [2, prefixSize tr tt K]] ∧
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub B_SIZE false) = [] := by
  obtain ⟨K, hK, hKH, ha, hp⟩ := active_end hL
  refine ⟨K, hK, hKH, ha, hp, ?_, ?_⟩
  · have hrow : ∀ r, r < tr.height tt →
        rowTraffic DedupTable.interactions tr tt r pub B_SIZE true =
          if r = K - 1 then [Msg.toFp [2, prefixSize tr tt K]] else [] := by
      intro r hr
      rw [DedupRender.candidate_rowT]
      simp only [B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC, Bool.true_eq_false,
        and_false, false_and, ite_false, List.nil_append, true_and]
      simp only [size_gate hL hK hKH ha hp hr]
      by_cases he : r = K - 1
      · have he' : r + 1 = K := by omega
        rw [if_pos he', if_pos he, size_prefix hL hr, he']
        rfl
      · simp [he, show r + 1 ≠ K by omega]
    rw [flatMap_congr' (fun r hr => hrow r (List.mem_range.mp hr))]
    exact flatMap_at _ _ _ (by omega)
  · apply List.flatMap_eq_nil_iff.mpr
    intro r _
    rw [DedupRender.candidate_rowT]
    simp [B_SIZE, B_BYTES, B_DIGEST, B_RCL, B_SRC]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof

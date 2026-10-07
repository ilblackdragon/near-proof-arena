import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractChainTraffic
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl SrcpV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL
theorem active_end : ∃ K, 0 < K ∧ K ≤ tr.height tt ∧
    (∀ r, r < K → tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) ∧
    (∀ r, K ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0) := by
  have hH : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨K, hK, hmin⟩ := exists_least (p := fun k =>
    k = tr.height tt ∨ (k < tr.height tt ∧ tr.cell tt k rt = 0 ∧ tr.cell tt k sg = 0))
    ⟨tr.height tt, Or.inl rfl⟩
  have hKH : K ≤ tr.height tt := by rcases hK with h | h <;> omega
  have hK0 : 0 < K := by
    apply Classical.byContradiction
    intro hn
    have he : K = 0 := by omega
    rw [he] at hK
    rcases hK with h | h
    · omega
    · have hr := (row0 hL).1
      rw [h.2.1] at hr
      exact absurd hr (by decide)
  refine ⟨K, hK0, hKH, ?_, ?_⟩
  · intro r hr
    rcases isBool hL (by omega : r < _) (x := rt) (by simp [SrcpProof.bools]) with ht | ht
    · rcases isBool hL (by omega : r < _) (x := sg) (by simp [SrcpProof.bools]) with hs | hs
      · exact False.elim (hmin r hr (Or.inr ⟨by omega, ht, hs⟩))
      · exact Or.inr hs
    · exact Or.inl ht
  · intro r hr hrt
    have hbase : tr.cell tt K rt = 0 ∧ tr.cell tt K sg = 0 := by
      rcases hK with h | h
      · omega
      · exact h.2
    have hpad : ∀ d, K + d < tr.height tt →
        tr.cell tt (K + d) rt = 0 ∧ tr.cell tt (K + d) sg = 0 := by
      intro d
      induction d with
      | zero => intro _; simpa using hbase
      | succ d ih =>
        intro hd
        have hp := ih (by omega)
        simpa only [Nat.add_assoc] using padStep hL (r := K + d) (by omega) hp.1 hp.2
    simpa [Nat.add_sub_cancel' hr] using hpad (r - K) (by omega)


/-- A SIZE gate ends either a computed proof or a duplicate skip. -/
theorem gz_active {r : Nat} (hr : r<tr.height tt) (hz : tr.cell tt r gz=1) :
    tr.cell tt r rt=1 ∨ tr.cell tt r sg=1 := by
  have hh := con hL hr (.mul (c gz) (Dsl.not DedupTable.endRow)) (by decide +kernel)
  simp only [DedupTable.endRow, eval_mul, eval_c, eval_not, eval_add, hz] at hh
  rcases isBool hL hr (x := dup) (by simp [SrcpProof.bools]) with hd | hd
  · have hl : tr.cell tt r sl=1 := by rw [hd] at hh; grind
    exact Or.inr (segment_last_active hL hr hl)
  · exact Or.inl (duplicate_root hL hr hd)

/-- Ending a source block before inactive traffic forces the SIZE gate. -/
theorem end_padding_gate {r : Nat} (hr : r<tr.height tt)
    (he : tr.cell tt r sl+tr.cell tt r dup=1)
    (hp : r+1<tr.height tt → tr.cell tt (r+1) rt=0 ∧ tr.cell tt (r+1) sg=0) :
    tr.cell tt r gz=1 := by
  by_cases hn : r+1<tr.height tt
  · have hh := con hL hr (.mul (mul3 .isTransition DedupTable.endRow (Dsl.not (c gz)))
      (Dsl.not (.add (n rt) (n sg)))) (by decide +kernel)
    have hh0 := hp hn
    simp only [DedupTable.endRow, eval_mul, eval_mul3, eval_add, eval_c, eval_n,
      eval_not, eval_isTransition, SrcpProof.nxt hn,
      show r+1≠tr.height tt by omega, ite_false, he, hh0.1, hh0.2] at hh
    grind
  · have hh := con hL hr (.mul .isLast (.mul DedupTable.endRow (Dsl.not (c gz)))) (by decide +kernel)
    simp only [DedupTable.endRow, eval_mul, eval_c, eval_add, eval_not, eval_isLast,
      show r+1=tr.height tt by omega, ite_true, he] at hh
    grind

/-- The unique SIZE output is the final active row, including a final skipped
header. No assumption that the last block is computed is needed. -/
theorem size_gate {K : Nat} (hK : 0<K) (hKH : K≤tr.height tt)
    (ha : ∀ r, r<K → tr.cell tt r rt=1 ∨ tr.cell tt r sg=1)
    (hp : ∀ r, K≤r → r<tr.height tt → tr.cell tt r rt=0 ∧ tr.cell tt r sg=0)
    {r : Nat} (hr : r<tr.height tt) : tr.cell tt r gz=1 ↔ r+1=K := by
  constructor
  · intro hz
    have hac := gz_active hL hr hz
    have hrK : r<K := by
      apply Classical.byContradiction
      intro hn
      have hh := hp r (by omega) hr
      rcases hac with hac | hac <;> simp_all
    apply Classical.byContradiction
    intro hn
    have hh := gz_next_inactive hL (r := r) (by omega) hz
    have hnac := ha (r+1) (by omega)
    rcases hnac with hnac | hnac <;> simp_all
  · intro he
    have heflag : tr.cell tt r sl+tr.cell tt r dup=1 := by
      rcases ha r (by omega) with ht | hs
      · rcases isBool hL hr (x := dup) (by simp [SrcpProof.bools]) with hd | hd
        · have hn := computed_root_not_last hL hr ht hd
          have hh := (computed_after_root hL hn ht hd).1
          rw [(hp (r+1) (by omega) hn).2] at hh
          exact False.elim (by simpa using hh)
        · have hsg : tr.cell tt r sg=0 := by
            have hh := disjoint hL hr; rw [ht] at hh; grind
          have hsl : tr.cell tt r sl=0 := by
            rcases isBool hL hr (x := sl) (by simp [SrcpProof.bools]) with hl | hl
            · exact hl
            · have hh := segment_last_active hL hr hl; rw [hsg] at hh
              exact False.elim (by simpa using hh)
          rw [hsl, hd]; grind
      · have hd := segment_nodup hL hr hs
        have hl : tr.cell tt r sl=1 := by
          by_cases hn : r+1<tr.height tt
          · rcases isBool hL hr (x := sl) (by simp [SrcpProof.bools]) with hl | hl
            · have hh := (inSeg hL hn hs hl).1
              rw [(hp (r+1) (by omega) hn).2] at hh
              exact False.elim (by simpa using hh)
            · exact hl
          · have hh := last_segment hL (by simpa [show tr.height tt-1=r by omega] using hs)
            simpa [show tr.height tt-1=r by omega] using hh
        rw [hl, hd]; grind
    exact end_padding_gate hL hr heflag (fun hn => hp (r+1) (by omega) hn)

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof

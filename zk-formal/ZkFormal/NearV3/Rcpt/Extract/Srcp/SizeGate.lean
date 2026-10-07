import ZkFormal.NearV3.Rcpt.Extract.Srcp.Counters

/-! The source-proof table emits SIZE exactly on its last active row. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
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
    · have hr := (row0 hL hH).1
      rw [h.2.1] at hr
      exact absurd hr (by decide)
  refine ⟨K, hK0, hKH, ?_, ?_⟩
  · intro r hr
    rcases isBool hL (by omega : r < _) (x := rt) (by simp [bools]) with ht | ht
    · rcases isBool hL (by omega : r < _) (x := sg) (by simp [bools]) with hs | hs
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

/-- The SIZE gate is one at exactly the end of the active prefix. -/
theorem size_gate {K : Nat} (hK : 0 < K) (hKH : K ≤ tr.height tt)
    (ha : ∀ r, r < K → tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1)
    (hp : ∀ r, K ≤ r → r < tr.height tt → tr.cell tt r rt = 0 ∧ tr.cell tt r sg = 0)
    {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r gz = 1 ↔ r + 1 = K := by
  have sl_sg {x : Nat} (hx : x < tr.height tt) (hl : tr.cell tt x sl = 1) :
      tr.cell tt x sg = 1 := by
    obtain ⟨-, -, -, hw, -, hs, -⟩ := local_ hL hx
    rcases isBool hL hx (x := wl) (by simp [bools]) with h | h
    · rw [hs, h] at hl; exact False.elim (by grind)
    · exact (hw h).1
  constructor
  · intro hg
    have hl := (local_ hL hr).2.2.2.2.2.2.2.2.2.2.2.2.2 hg
    have hs := sl_sg hr hl
    have hrK : r < K := by
      apply Classical.byContradiction
      intro hn
      have he := (hp r (by omega) hr).2
      rw [he] at hs
      exact absurd hs (by decide)
    apply Classical.byContradiction
    intro hn
    have hnK : r + 1 < K := by omega
    have hz := (gzStep hL (by omega) hl).mp hg
    have hb1 := isBool hL (by omega : r + 1 < _) (x := rt) (by simp [bools])
    have hb2 := isBool hL (by omega : r + 1 < _) (x := sg) (by simp [bools])
    rcases ha (r + 1) hnK with he | he <;> rcases hb1 with h1 | h1 <;>
      rcases hb2 with h2 | h2 <;> rw [h1, h2] at hz <;> first | exact absurd hz (by decide) | grind
  · intro he
    have hs : tr.cell tt r sg = 1 := by
      rcases ha r (by omega) with ht | ht
      · have hn := root_not_last hL hr ht
        have hsg := (afterRoot hL hn ht).1
        have hp' := (hp (r + 1) (by omega) hn).2
        rw [hp'] at hsg
        exact False.elim (by simpa using hsg)
      · exact ht
    have hl : tr.cell tt r sl = 1 := by
      by_cases hn : r + 1 < tr.height tt
      · rcases isBool hL hr (x := sl) (by simp [bools]) with hl | hl
        · have hnsg := (inSeg hL hn hs hl).1
          have hp' := (hp (r + 1) (by omega) hn).2
          rw [hp'] at hnsg
          exact False.elim (by simpa using hnsg)
        · exact hl
      · have hl := (lastRow hL (by omega)).2.1
        rw [show tr.height tt - 1 = r by omega] at hl
        exact hl hs
    by_cases hn : r + 1 < tr.height tt
    · apply (gzStep hL hn hl).mpr
      rw [(hp (r + 1) (by omega) hn).1, (hp (r + 1) (by omega) hn).2]
      rfl
    · have hg := (lastRow hL (by omega)).2.2
      rw [show tr.height tt - 1 = r by omega] at hg
      exact hg hl

end ZkFormal.NearV3.SrcpProof

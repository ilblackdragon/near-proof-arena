import ZkFormal.NearV3.Extract.Ups.LayoutRows

/-!
# ZkFormal.NearV3.Extract.Ups.Layout — the layout of an instance segment (layer 2)

From `UpsWf`: rows `0 … 3` are `W0 … W3`; rows `4 … 3+L` the value part (`qpos = d`, `pf`
exactly at the first, `pl` exactly at the last); the remaining rows are the node parts,
consecutive sub-segments `(o_k, ℓ_k)` with `qpos = d`, part number `j = k + 1`, constant part
constants, `pf`/`pl` exactly at the ends.  Segment constants are constant over the segment.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem P_big : 1073741824 < P := by unfold P; omega

theorem le_sum_of_mem' {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.mem_cons, List.sum_cons] at h ⊢
    rcases h with rfl | h
    · omega
    · have := ih h; omega

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

theorem okRow {i : Nat} (hi : i < s.rows.length) : URowOk (s.row i) (s.next i) := hw.rows s hs i hi

theorem next_eq {i : Nat} (hi : i + 1 < s.rows.length) : s.next i = s.row (i + 1) := by
  unfold UpsSeg.next; rw [if_pos hi]

theorem rowLt (i x : Nat) : s.row i x < P := (hw.canon s hs).1 i x
theorem nextLt (i x : Nat) : s.next i x < P := by
  unfold UpsSeg.next; split
  · exact rowLt hw hs _ _
  · exact (hw.canon s hs).2 x

theorem lenLe : s.rows.length ≤ 2 ^ 22 := by
  have := hw.count
  have h : s.rows.length ≤ (v.map (·.rows.length)).sum := le_sum_of_mem' (List.mem_map_of_mem hs)
  omega

theorem okIn {i : Nat} (hi : i + 1 < s.rows.length) : URowOk (s.row i) (s.row (i + 1)) := by
  rw [← next_eq hw hs hi]; exact okRow hw hs (by omega)

/-- The segment's end: `qb·pl·rootP` exactly at the last row. -/
theorem notEnd {i : Nat} (hi : i + 1 < s.rows.length) :
    ¬ (s.row i qb = 1 ∧ s.row i pl = 1 ∧ s.row i rootP = 1) := fun h =>
  absurd ((hw.stop s hs i (by omega)).1 h) (by omega)

/-- A row that is not `qb` is not the last row. -/
theorem notLast {i : Nat} (hi : i < s.rows.length) (hq : s.row i qb ≠ 1) : i + 1 < s.rows.length := by
  rcases Nat.lt_or_ge (i + 1) s.rows.length with h | h
  · exact h
  · exact absurd ((hw.stop s hs i hi).2 (by omega)).1 hq

theorem walkRows : 4 < s.rows.length ∧ s.row 0 sf = 1 ∧ s.row 1 wt1 = 1 ∧ s.row 2 wt2 = 1 ∧
    s.row 3 wt3 = 1 ∧ s.row 4 vb = 1 ∧ s.row 4 pf = 1 := by
  obtain ⟨h0, hsf⟩ := hw.start s hs
  have K := fun i (hi : i + 1 < s.rows.length) =>
    kinds (okIn hw hs hi) (rowLt hw hs i) (rowLt hw hs (i + 1))
  have Kq : ∀ i, i < s.rows.length → (s.row i sf = 1 ∨ s.row i wt1 = 1 ∨ s.row i wt2 = 1 ∨ s.row i wt3 = 1) →
      s.row i qb ≠ 1 := by
    intro i hi h
    obtain ⟨b0, e1, e2, -⟩ := kinds (okRow hw hs hi) (rowLt hw hs i) (nextLt hw hs i)
    have := le1 b0; omega
  have h1 : 1 < s.rows.length := notLast hw hs h0 (Kq 0 h0 (Or.inl hsf))
  have w1 : s.row 1 wt1 = 1 := (K 0 h1).2.2.2.2.2.2.2.2.2.2.2.1 hsf
  have h2 : 2 < s.rows.length := notLast hw hs h1 (Kq 1 h1 (Or.inr (Or.inl w1)))
  have w2 : s.row 2 wt2 = 1 := (K 1 h2).2.2.2.2.2.2.2.2.2.2.2.2.1 w1
  have h3 : 3 < s.rows.length := notLast hw hs h2 (Kq 2 h2 (Or.inr (Or.inr (Or.inl w2))))
  have w3 : s.row 3 wt3 = 1 := (K 2 h3).2.2.2.2.2.2.2.2.2.2.2.2.2.1 w2
  have h4 : 4 < s.rows.length := notLast hw hs h3 (Kq 3 h3 (Or.inr (Or.inr (Or.inr w3))))
  have L3 := layoutRow (okIn hw hs h4) (rowLt hw hs 3) (rowLt hw hs 4)
  exact ⟨h4, hsf, w1, w2, w3, (L3.2.2.2.2.2.1 w3).1, (L3.2.2.2.2.2.1 w3).2⟩

theorem vbNotQb {i : Nat} (hi : i < s.rows.length) (h : s.row i vb = 1) : s.row i qb ≠ 1 := by
  obtain ⟨b0, e1, -⟩ := kinds (okRow hw hs hi) (rowLt hw hs i) (nextLt hw hs i)
  have := le1 b0; omega

/-- Successive `vb` rows without `pl` from row 4. -/
theorem vbRun (d0 : Nat) (hpl : ∀ d, d < d0 → 4 + d < s.rows.length → s.row (4 + d) pl ≠ 1) :
    ∀ d, d ≤ d0 → 4 + d < s.rows.length →
      s.row (4 + d) vb = 1 ∧ s.row (4 + d) qpos = d ∧ (s.row (4 + d) pf = 1 ↔ d = 0) := by
  obtain ⟨h4, -, -, -, -, v4, p4⟩ := walkRows hw hs
  have hm := lenLe hw hs
  intro d
  induction d with
  | zero =>
    intro _ _
    have L := layoutRow (okRow hw hs h4) (rowLt hw hs 4) (nextLt hw hs 4)
    exact ⟨v4, L.2.2.2.2.1 p4, by simp [p4]⟩
  | succ d ih =>
    intro hd hlt
    obtain ⟨hv, hq, -⟩ := ih (by omega) (by omega)
    have hn : 4 + d + 1 < s.rows.length := by omega
    have L := layoutRow (okIn hw hs hn) (rowLt hw hs _) (rowLt hw hs _)
    have hp0 : s.row (4 + d) pl = 0 := by
      have := hpl d (by omega) (by omega); rcases L.2.1 with h | h <;> omega
    obtain ⟨n1, n2, n3⟩ := L.2.2.2.2.2.2.1 hv hp0
    rw [hq] at n3
    have : s.row (4 + d + 1) qpos = d + 1 := by
      apply natv (rowLt hw hs _ _) (by have := P_big; omega)
      rw [n3, natCast_add]; rfl
    rw [show 4 + (d + 1) = 4 + d + 1 by omega]
    exact ⟨n1, this, by simp [n2]⟩

/-- **The value part**: rows `4 … 3+L`, followed by the first node part. -/
theorem valuePart : ∃ L, 1 ≤ L ∧ 4 + L < s.rows.length ∧
    (∀ d, d < L → s.row (4 + d) vb = 1 ∧ s.row (4 + d) qpos = d ∧ (s.row (4 + d) pf = 1 ↔ d = 0) ∧
      (s.row (4 + d) pl = 1 ↔ d + 1 = L)) ∧
    s.row (4 + L) qb = 1 ∧ s.row (4 + L) pf = 1 ∧ s.row (4 + L) j = 1 := by
  obtain ⟨h4, -⟩ := walkRows hw hs
  have hex : ∃ d, 4 + d < s.rows.length ∧ s.row (4 + d) pl = 1 := by
    refine Classical.byContradiction fun hne => ?_
    have hpl : ∀ d, 4 + d < s.rows.length → s.row (4 + d) pl ≠ 1 := fun d hd h => hne ⟨d, hd, h⟩
    have hlast := vbRun hw hs (s.rows.length - 5) (fun d _ hd => hpl d hd) (s.rows.length - 5) (Nat.le_refl _)
      (by omega)
    rw [show 4 + (s.rows.length - 5) = s.rows.length - 1 by omega] at hlast
    have hend := (hw.stop s hs (s.rows.length - 1) (by omega)).2 (by omega)
    exact vbNotQb hw hs (by omega) hlast.1 hend.1
  obtain ⟨d0, ⟨hd0, hpl0⟩, hmin⟩ := exists_least hex
  have run := vbRun hw hs d0 (fun d hd hlt h => hmin d hd ⟨hlt, h⟩)
  obtain ⟨hv0, hq0, -⟩ := run d0 (Nat.le_refl _) hd0
  have hn : 4 + d0 + 1 < s.rows.length := notLast hw hs hd0 (vbNotQb hw hs hd0 hv0)
  have L := layoutRow (okIn hw hs hn) (rowLt hw hs _) (rowLt hw hs _)
  obtain ⟨n1, n2, n3⟩ := L.2.2.2.2.2.2.2.1 hv0 hpl0
  refine ⟨d0 + 1, by omega, by omega, fun d hd => ?_, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := run d (by omega) (by omega)
    refine ⟨a1, a2, a3, ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases Nat.lt_or_ge d d0 with hlt | hge
      · exact absurd ⟨by omega, h⟩ (hmin d hlt)
      · omega
    · rw [show d = d0 by omega]; exact hpl0
  · rw [show 4 + (d0 + 1) = 4 + d0 + 1 by omega]; exact ⟨n1, n2, n3⟩

/-- From a `qb` row on, every row of the segment is a `qb` row. -/
theorem qbRun {b0 : Nat} (hq : s.row b0 qb = 1) : ∀ r, b0 + r < s.rows.length → s.row (b0 + r) qb = 1 := by
  intro r
  induction r with
  | zero => intro _; simpa using hq
  | succ r ih =>
    intro hr
    have h := ih (by omega)
    have hn : b0 + r + 1 < s.rows.length := by omega
    have L := layoutRow (okIn hw hs hn) (rowLt hw hs _) (rowLt hw hs _)
    rw [show b0 + (r + 1) = b0 + r + 1 by omega]
    rcases L.2.1 with hp | hp
    · exact (L.2.2.2.2.2.2.2.2.2.1 h hp).1
    · exact (L.2.2.2.2.2.2.2.2.2.2.1 h hp (fun h' => notEnd hw hs hn ⟨h, hp, h'⟩)).1

end

theorem consec_shift (b : Nat) : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l →
    Consec (b + s0) (l.map fun p => (b + p.1, p.2)) ∧ segEnd (b + s0) (l.map fun p => (b + p.1, p.2)) = b + segEnd s0 l
  | [], _, _ => ⟨trivial, by simp [segEnd]⟩
  | (s', ℓ) :: rest, s0, ⟨h1, h2⟩ => by
    obtain ⟨c, e⟩ := consec_shift b rest (s0 + ℓ) h2
    subst h1
    refine ⟨⟨rfl, by rw [show b + s' + ℓ = b + (s' + ℓ) by omega]; exact c⟩, ?_⟩
    simp only [List.map_cons, segEnd]
    rw [show b + s' + ℓ = b + (s' + ℓ) by omega]; exact e

theorem consec_head : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l → (h : 0 < l.length) → (l[0]'h).1 = s0
  | [], _, _, h => by simp at h
  | _ :: _, _, ⟨h1, _⟩, _ => h1

theorem consec_mem_lt : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l → ∀ k (hk : k < l.length),
    s0 ≤ l[k].1 ∧ l[k].1 + l[k].2 ≤ segEnd s0 l := fun l s0 hc k hk =>
  seg_le_end l s0 hc l[k] (List.getElem_mem hk)

def colAt (s : UpsSeg) (x b r : Nat) : Bool := decide (s.row (b + r) x = 1)

attribute [local irreducible] UpsSeg.row

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- Inside a node part: the next row continues it. -/
theorem qbStep {r : Nat} (hr : r + 1 < s.rows.length) (hq : s.row r qb = 1) (hp : s.row r pl = 0) :
    s.row (r + 1) qb = 1 ∧ s.row (r + 1) pf = 0 ∧
      ((s.row (r + 1) qpos : Nat) : Fp) = ((s.row r qpos : Nat) : Fp) + 1 ∧
      ∀ x ∈ partConst, s.row (r + 1) x = s.row r x := by
  have L' := layoutRow (okIn hw hs hr) (rowLt hw hs _) (rowLt hw hs _)
  obtain ⟨n1, n2, n3⟩ := L'.2.2.2.2.2.2.2.2.2.1 hq hp
  exact ⟨n1, n2, n3, fun x hx => pconst (okIn hw hs hr) (rowLt hw hs _) (rowLt hw hs _) (Or.inr hq) hp hx⟩

/-- At a part end that is not the segment end, the next part starts. -/
theorem qbNext {r : Nat} (hr : r + 1 < s.rows.length) (hq : s.row r qb = 1) (hp : s.row r pl = 1) :
    s.row (r + 1) qb = 1 ∧ s.row (r + 1) pf = 1 ∧
      ((s.row (r + 1) j : Nat) : Fp) = ((s.row r j : Nat) : Fp) + 1 := by
  have L' := layoutRow (okIn hw hs hr) (rowLt hw hs _) (rowLt hw hs _)
  exact L'.2.2.2.2.2.2.2.2.2.2.1 hq hp (fun h' => notEnd hw hs hr ⟨hq, hp, h'⟩)

theorem pfQpos {r : Nat} (hr : r < s.rows.length) (h : s.row r pf = 1) : s.row r qpos = 0 :=
  (layoutRow (okRow hw hs hr) (rowLt hw hs _) (nextLt hw hs _)).2.2.2.2.1 h

theorem plBool {r : Nat} (hr : r < s.rows.length) : s.row r pl = 0 ∨ s.row r pl = 1 :=
  (layoutRow (okRow hw hs hr) (rowLt hw hs _) (nextLt hw hs _)).2.1

theorem pfBool {r : Nat} (hr : r < s.rows.length) : s.row r pf = 0 ∨ s.row r pf = 1 :=
  (layoutRow (okRow hw hs hr) (rowLt hw hs _) (nextLt hw hs _)).1

/-- A node part `(o, ℓ)` (absolute rows). -/
theorem partOf {o ℓ : Nat} (hℓ : 0 < ℓ) (hoℓ : o + ℓ ≤ s.rows.length) (hpf : s.row o pf = 1)
    (hq : ∀ d, d < ℓ → s.row (o + d) qb = 1)
    (hpfn : ∀ d, 0 < d → d < ℓ → s.row (o + d) pf ≠ 1)
    (hpln : ∀ d, d + 1 < ℓ → s.row (o + d) pl ≠ 1) (hpll : s.row (o + ℓ - 1) pl = 1) :
    ∀ d, d < ℓ → s.row (o + d) qpos = d ∧
        (s.row (o + d) pf = 1 ↔ d = 0) ∧ (s.row (o + d) pl = 1 ↔ d + 1 = ℓ) ∧
        ∀ x ∈ partConst, s.row (o + d) x = s.row o x := by
  have hm := lenLe hw hs
  have hpl0 : ∀ d, d + 1 < ℓ → s.row (o + d) pl = 0 := fun d hd =>
    (plBool hw hs (r := o + d) (by omega)).resolve_right (hpln d hd)
  have st := fun d (hd : d + 1 < ℓ) => qbStep hw hs (r := o + d) (by omega) (hq d (by omega)) (hpl0 d hd)
  have q0 := pfQpos hw hs (r := o) (by omega) hpf
  intro d hd
  refine ⟨?_, ⟨fun h => ?_, fun h => by subst h; simpa using hpf⟩, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have hc := counter_of (f := fun r => ((s.row r qpos : Nat) : Fp)) (s := o) (ℓ := ℓ) (v0 := 0)
      (by simp only [q0]) (fun r h1 h2 => by
        have := (st (r - o) (by omega)).2.2.1
        rwa [show o + (r - o) = r by omega] at this) (o + d) (by omega) (by omega)
    simp only [show 0 + (o + d - o) = d by omega] at hc
    exact natv (rowLt hw hs _ _) (by have := P_big; omega) hc
  · rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact h0
    · exact absurd h (hpfn d h0 hd)
  · rcases Nat.lt_or_ge (d + 1) ℓ with h' | h'
    · exact absurd h (hpln d h')
    · omega
  · rw [show o + d = o + ℓ - 1 by omega]; exact hpll
  · intro x hx
    exact const_of (f := fun r => s.row r x) (s := o) (ℓ := ℓ) (fun r h1 h2 => by
      have := (st (r - o) (by omega)).2.2.2 x hx
      rwa [show o + (r - o) = r by omega] at this) (o + d) (by omega) (by omega)

/-- The `qb` rows from `base` on, as a segmented table (parts `pf … pl`). -/
theorem qbSegFacts {base : Nat} (hb : base < s.rows.length) (q0 : s.row base qb = 1)
    (p0 : s.row base pf = 1) :
    SegFacts (s.rows.length - base) (colAt s qb base) (colAt s pf base) (colAt s pl base) := by
  have QB := qbRun hw hs q0
  refine ⟨fun r hr _ => by simp only [colAt, decide_eq_true_eq]; exact QB r (by omega),
    fun r hr _ => by simp only [colAt, decide_eq_true_eq]; exact QB r (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr _ hl
    simp only [colAt, decide_eq_true_eq, decide_eq_false_iff_not] at hl ⊢
    have hn : base + r + 1 < s.rows.length := by omega
    have hp : s.row (base + r) pl = 0 := (plBool hw hs (by omega)).resolve_right hl
    have st := qbStep hw hs hn (QB r (by omega)) hp
    rw [show base + (r + 1) = base + r + 1 by omega, st.2.1]
    exact ⟨st.1, by decide⟩
  · intro r hr hl _
    simp only [colAt, decide_eq_true_eq] at hl ⊢
    have hn : base + r + 1 < s.rows.length := by omega
    rw [show base + (r + 1) = base + r + 1 by omega]
    exact (qbNext hw hs hn (QB r (by omega)) hl).2.1
  · intro r hr ha
    simp only [colAt, decide_eq_false_iff_not] at ha
    exact absurd (QB r (by omega)) ha
  · intro _; simp only [colAt, decide_eq_true_eq, Nat.add_zero]; exact p0
  · intro _ _
    simp only [colAt, decide_eq_true_eq]
    have he := ((hw.stop s hs (s.rows.length - 1) (by omega)).2 (by omega)).2.1
    rw [show base + (s.rows.length - base - 1) = s.rows.length - 1 by omega]; exact he

/-- **The node parts**: consecutive parts from `4 + L` to the segment end, numbered
`j = 1, 2, …`, each with its position counter, its `pf`/`pl` flags and its part constants. -/
theorem nodeParts : ∃ L ps, 1 ≤ L ∧ 4 + L < s.rows.length ∧
    (∀ d, d < L → s.row (4 + d) vb = 1 ∧ s.row (4 + d) qpos = d ∧ (s.row (4 + d) pf = 1 ↔ d = 0) ∧
      (s.row (4 + d) pl = 1 ↔ d + 1 = L)) ∧
    Consec (4 + L) ps ∧ segEnd (4 + L) ps = s.rows.length ∧ 0 < ps.length ∧
    ∀ k (hk : k < ps.length), 0 < ps[k].2 ∧ s.row ps[k].1 j = k + 1 ∧
      ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) qb = 1 ∧ s.row (ps[k].1 + d) qpos = d ∧
        (s.row (ps[k].1 + d) pf = 1 ↔ d = 0) ∧ (s.row (ps[k].1 + d) pl = 1 ↔ d + 1 = ps[k].2) ∧
        ∀ x ∈ partConst, s.row (ps[k].1 + d) x = s.row ps[k].1 x := by
  obtain ⟨L, hL1, hLm, hval, q0, p0, j0⟩ := valuePart hw hs
  have hm := lenLe hw hs
  have QB := qbRun hw hs q0
  have hf := qbSegFacts hw hs hLm q0 p0
  obtain ⟨ps0, hc0, he0, hall, hpad⟩ := segments_of hf (by omega)
  have hcov : segEnd 0 ps0 = s.rows.length - (4 + L) := by
    rcases Nat.lt_or_ge (segEnd 0 ps0) (s.rows.length - (4 + L)) with h | h
    · have := hpad _ (Nat.le_refl _) h
      simp only [colAt, decide_eq_false_iff_not] at this
      exact absurd (QB _ (by omega)) this
    · omega
  obtain ⟨hc, he⟩ := consec_shift (4 + L) ps0 0 hc0
  rw [Nat.add_zero] at hc he
  generalize hps : ps0.map (fun p => (4 + L + p.1, p.2)) = ps at hc he
  have hlen : ps.length = ps0.length := by rw [← hps, List.length_map]
  have hget : ∀ k (hk : k < ps.length), ps[k] = (4 + L + (ps0[k]'(by omega)).1, (ps0[k]'(by omega)).2) := by
    intro k hk; subst hps; simp
  have hpos : 0 < ps.length := by
    rcases Nat.eq_zero_or_pos ps.length with h | h
    · rw [hlen, List.length_eq_zero_iff] at h; subst h; simp [segEnd] at hcov; omega
    · exact h
  -- each part
  have part : ∀ k (hk : k < ps.length), 0 < ps[k].2 ∧ ps[k].1 + ps[k].2 ≤ s.rows.length ∧
      ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) qb = 1 ∧ s.row (ps[k].1 + d) qpos = d ∧
        (s.row (ps[k].1 + d) pf = 1 ↔ d = 0) ∧ (s.row (ps[k].1 + d) pl = 1 ↔ d + 1 = ps[k].2) ∧
        ∀ x ∈ partConst, s.row (ps[k].1 + d) x = s.row ps[k].1 x := by
    intro k hk
    have hk0 : k < ps0.length := by omega
    obtain ⟨hℓ, hfst, hlst, -, hnf, hnl⟩ := hall _ (List.getElem_mem hk0)
    have hle := consec_mem_lt ps0 0 hc0 k hk0
    rw [hget k hk]
    simp only [colAt, decide_eq_true_eq, decide_eq_false_iff_not] at hfst hlst hnf hnl
    have hle' : 4 + L + ps0[k].1 + ps0[k].2 ≤ s.rows.length := by omega
    have P := partOf hw hs (o := 4 + L + ps0[k].1) (ℓ := ps0[k].2) hℓ hle' hfst
      (fun d hd => by rw [Nat.add_assoc]; exact QB _ (by omega))
      (fun d h0 hd => by
        have := hnf (ps0[k].1 + d) (by omega) (by omega); rwa [← Nat.add_assoc] at this)
      (fun d hd => by
        have := hnl (ps0[k].1 + d) (by omega) (by omega); rwa [← Nat.add_assoc] at this)
      (by rw [show 4 + L + ps0[k].1 + ps0[k].2 - 1 = 4 + L + (ps0[k].1 + ps0[k].2 - 1) by omega]
          exact hlst)
    exact ⟨hℓ, hle', fun d hd => ⟨by rw [Nat.add_assoc]; exact QB _ (by omega), P d hd⟩⟩
  have lb : ∀ k (hk : k < ps.length), 4 + L + k ≤ ps[k].1 := by
    intro k
    induction k with
    | zero => intro hk; rw [consec_head ps (4 + L) hc hk]; omega
    | succ k ih =>
      intro hk
      have := consec_get ps (4 + L) hc k hk
      have := (part k (by omega)).1
      have := ih (by omega)
      omega
  -- numbering
  have num : ∀ k (hk : k < ps.length), s.row ps[k].1 j = k + 1 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have := consec_head ps (4 + L) hc hk
      rw [this]; exact j0
    | succ k ih =>
      intro hk
      have hprev := part k (by omega)
      have hnx := consec_get ps (4 + L) hc k hk
      have hlast := (hprev.2.2 (ps[k].2 - 1) (by omega))
      have hr : ps[k].1 + (ps[k].2 - 1) + 1 = ps[k + 1].1 := by omega
      have hsz := part (k + 1) hk
      have hr1 : ps[k].1 + (ps[k].2 - 1) + 1 < s.rows.length := by omega
      have N := qbNext hw hs hr1 hlast.1 (hlast.2.2.2.1.2 (by omega))
      rw [hr] at N
      have hj := hlast.2.2.2.2 j (by simp [partConst, j])
      rw [hj, ih (by omega)] at N
      have hge := lb (k + 1) hk
      exact natv (rowLt hw hs _ _) (by have := P_big; omega) (by rw [N.2.2, natCast_add (k + 1) 1]; rfl)
  refine ⟨L, ps, hL1, hLm, hval, hc, ?_, hpos, fun k hk => ⟨(part k hk).1, num k hk, (part k hk).2.2⟩⟩
  rw [he, hcov]; omega

end

end ZkFormal.NearV3.UpsRows

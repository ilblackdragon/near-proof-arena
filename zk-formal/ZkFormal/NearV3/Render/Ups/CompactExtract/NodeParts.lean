import ZkFormal.NearV3.Render.Ups.CompactExtract.Layout
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s∈v)
include hw hs

theorem lenLe : s.rows.length≤2^22 := by
  have := hw.count
  have h : s.rows.length≤(v.map (·.rows.length)).sum:=le_sum_of_mem' (List.mem_map_of_mem hs)
  omega

theorem notEnd {i : Nat} (hi : i+1<s.rows.length) :
    ¬(s.row i qb=1 ∧ s.row i pl=1 ∧ s.row i rootP=1) := fun h=>
  absurd ((hw.stop s hs i (by omega)).1 h) (by omega)

theorem qbRun {b0 : Nat} (hq : s.row b0 qb = 1) : ∀ r, b0 + r < s.rows.length → s.row (b0 + r) qb = 1 := by
  intro r
  induction r with
  | zero => intro _; simpa using hq
  | succ r ih =>
    intro hr
    have h := ih (by omega)
    have hn : b0 + r + 1 < s.rows.length := by omega
    have L := layoutRow (nodeRowOk (okIn hw hs hn) (rowLt hw hs _) h) (rowLt hw hs _) (rowLt hw hs _)
    rw [show b0 + (r + 1) = b0 + r + 1 by omega]
    rcases L.2.1 with hp | hp
    · exact (L.2.2.2.2.2.2.2.2.2.1 h hp).1
    · exact (L.2.2.2.2.2.2.2.2.2.2.1 h hp (fun h' => notEnd hw hs hn ⟨h, hp, h'⟩)).1

theorem qbStep {r : Nat} (hr : r + 1 < s.rows.length) (hq : s.row r qb = 1) (hp : s.row r pl = 0) :
    s.row (r + 1) qb = 1 ∧ s.row (r + 1) pf = 0 ∧
      ((s.row (r + 1) qpos : Nat) : Fp) = ((s.row r qpos : Nat) : Fp) + 1 ∧
      ∀ x ∈ partConst, s.row (r + 1) x = s.row r x := by
  have L' := layoutRow (nodeRowOk (okIn hw hs hr) (rowLt hw hs _) hq) (rowLt hw hs _) (rowLt hw hs _)
  obtain ⟨n1, n2, n3⟩ := L'.2.2.2.2.2.2.2.2.2.1 hq hp
  exact ⟨n1, n2, n3, fun x hx => pconst (nodeRowOk (okIn hw hs hr) (rowLt hw hs _) hq) (rowLt hw hs _) (rowLt hw hs _) (Or.inr hq) hp hx⟩

/-- At a part end that is not the segment end, the next part starts. -/
theorem qbNext {r : Nat} (hr : r + 1 < s.rows.length) (hq : s.row r qb = 1) (hp : s.row r pl = 1) :
    s.row (r + 1) qb = 1 ∧ s.row (r + 1) pf = 1 ∧
      ((s.row (r + 1) j : Nat) : Fp) = ((s.row r j : Nat) : Fp) + 1 := by
  have L' := layoutRow (nodeRowOk (okIn hw hs hr) (rowLt hw hs _) hq) (rowLt hw hs _) (rowLt hw hs _)
  exact L'.2.2.2.2.2.2.2.2.2.2.1 hq hp (fun h' => notEnd hw hs hr ⟨hq, hp, h'⟩)


theorem pfQpos {r : Nat} (hr : r<s.rows.length) (hp : s.row r pf=1) : s.row r qpos=0 := by
  have h:=fact (okRow hw hs hr) (e:=.mul (c pf) (c qpos))
    (by simp [compactConstraints,compactRows,cRows])
  uev_simp
  simp only [hp,cast_ofNat,cast1] at h
  exact natv (rowLt hw hs _ _) (by have := P_gt; omega) (by rw [cast0]; grind)

theorem plBool {r : Nat} (hr : r<s.rows.length) : s.row r pl=0 ∨ s.row r pl=1 :=
  rowBool (okRow hw hs hr) (rowLt hw hs _) (by simp [rowBools])

theorem pfBool {r : Nat} (hr : r<s.rows.length) : s.row r pf=0 ∨ s.row r pf=1 :=
  rowBool (okRow hw hs hr) (rowLt hw hs _) (by simp [rowBools])
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

theorem nodeParts : ∃ ps, 4<s.rows.length ∧
    Consec (4) ps ∧ segEnd (4) ps = s.rows.length ∧ 0 < ps.length ∧
    ∀ k (hk : k < ps.length), 0 < ps[k].2 ∧ s.row ps[k].1 j = k + 1 ∧
      ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) qb = 1 ∧ s.row (ps[k].1 + d) qpos = d ∧
        (s.row (ps[k].1 + d) pf = 1 ↔ d = 0) ∧ (s.row (ps[k].1 + d) pl = 1 ↔ d + 1 = ps[k].2) ∧
        ∀ x ∈ partConst, s.row (ps[k].1 + d) x = s.row ps[k].1 x := by
  obtain ⟨hLm,_,_,_,_,q0,p0,j0⟩ := walkRows hw hs
  have hm := lenLe hw hs
  have QB := qbRun hw hs q0
  have hf := qbSegFacts hw hs hLm q0 p0
  obtain ⟨ps0, hc0, he0, hall, hpad⟩ := segments_of hf (by omega)
  have hcov : segEnd 0 ps0 = s.rows.length - (4) := by
    rcases Nat.lt_or_ge (segEnd 0 ps0) (s.rows.length - (4)) with h | h
    · have := hpad _ (Nat.le_refl _) h
      simp only [colAt, decide_eq_false_iff_not] at this
      exact absurd (QB _ (by omega)) this
    · omega
  obtain ⟨hc, he⟩ := consec_shift (4) ps0 0 hc0
  rw [Nat.add_zero] at hc he
  generalize hps : ps0.map (fun p => (4 + p.1, p.2)) = ps at hc he
  have hlen : ps.length = ps0.length := by rw [← hps, List.length_map]
  have hget : ∀ k (hk : k < ps.length), ps[k] = (4 + (ps0[k]'(by omega)).1, (ps0[k]'(by omega)).2) := by
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
    have hle' : 4 + ps0[k].1 + ps0[k].2 ≤ s.rows.length := by omega
    have P := partOf hw hs (o := 4 + ps0[k].1) (ℓ := ps0[k].2) hℓ hle' hfst
      (fun d hd => by rw [Nat.add_assoc]; exact QB _ (by omega))
      (fun d h0 hd => by
        have := hnf (ps0[k].1 + d) (by omega) (by omega); rwa [← Nat.add_assoc] at this)
      (fun d hd => by
        have := hnl (ps0[k].1 + d) (by omega) (by omega); rwa [← Nat.add_assoc] at this)
      (by rw [show 4 + ps0[k].1 + ps0[k].2 - 1 = 4 + (ps0[k].1 + ps0[k].2 - 1) by omega]
          exact hlst)
    exact ⟨hℓ, hle', fun d hd => ⟨by rw [Nat.add_assoc]; exact QB _ (by omega), P d hd⟩⟩
  have lb : ∀ k (hk : k < ps.length), 4 + k ≤ ps[k].1 := by
    intro k
    induction k with
    | zero => intro hk; rw [consec_head ps (4) hc hk]; omega
    | succ k ih =>
      intro hk
      have := consec_get ps (4) hc k hk
      have := (part k (by omega)).1
      have := ih (by omega)
      omega
  -- numbering
  have num : ∀ k (hk : k < ps.length), s.row ps[k].1 j = k + 1 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have := consec_head ps (4) hc hk
      rw [this]; exact j0
    | succ k ih =>
      intro hk
      have hprev := part k (by omega)
      have hnx := consec_get ps (4) hc k hk
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
  refine ⟨ps, hLm, hc, ?_, hpos, fun k hk => ⟨(part k hk).1, num k hk, (part k hk).2.2⟩⟩
  rw [he, hcov]; omega

end
end ZkFormal.NearV3.Render.UpsRelay.Extract

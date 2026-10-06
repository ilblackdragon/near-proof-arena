import ZkFormal.NearV3.Sched.View.ScanReq
import ZkFormal.NearV3.Sched.View.Dist

/-!
# ZkFormal.NearV3.Sched.Link.ScanRows — the scan rows of `ssdV3` partition into request blocks

Global structure of the scan family inside the merged table (`Local ScanDist.constraints`):

* `dist_next`: a distribute row (`kSh`, `kGH` or `kC`) is followed by a distribute row or
  padding, never by a scan row;
* `shape_all`: a request-start row `f` (`fQ = 1`) is followed by its 20-row block (`kS = 1`,
  `re = [x = 19]`, request constants carried); unlike `struct_all` this needs no bitmap;
* **`kS_block`**: every request row lies in the block of a request-start row `f ≤ w < f + 20`;
* `re_block`: every row with `re = 1` is the end row `f + 19` of a block;
* **`param_of`**: every request-start row has a param row `p < f` with the same instance
  constants `τ, n, base, D` (sections start with a param row).
-/

namespace ZkFormal.NearV3.Sched.Scan

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- **A distribute row is not followed by a scan row.** -/
theorem dist_next (hL : Local ScanDist.constraints tr t pub) {w : Nat} (hw : w + 1 < tr.height t)
    (hd : cv tr t w Dist.kSh = 1 ∨ cv tr t w Dist.kGH = 1 ∨ cv tr t w Dist.kC = 1) :
    cv tr t (w + 1) kS = 0 ∧ cv tr t (w + 1) kP = 0 := by
  have hD := Dist.DLocal.of_sd hL
  have hw0 : w < tr.height t := by omega
  have F0 := row_flags (SLocal.of_sd hL) hw0
  have F1 := row_flags (SLocal.of_sd hL) hw
  simp only [act, kP, kS, kSh, kGH, kC] at F0 F1 ⊢
  suffices h : ¬ (cv tr t (w + 1) Dist.kSh = 0 ∧ cv tr t (w + 1) Dist.kGH = 0 ∧
      cv tr t (w + 1) Dist.kC = 0 ∧ cv tr t (w + 1) Dist.act = 1) by
    have b1 := Dist.bool_of hD hw (x := Dist.kSh) (by simp [Dist.boolCols])
    have b2 := Dist.bool_of hD hw (x := Dist.kGH) (by simp [Dist.boolCols])
    have b3 := Dist.bool_of hD hw (x := Dist.kC) (by simp [Dist.boolCols])
    omega
  rintro ⟨h1, h2, h3, h4⟩
  have he1 := Dist.bool_of hD hw0 (x := Dist.e1) (by simp [Dist.boolCols])
  have heI := Dist.bool_of hD hw0 (x := Dist.eI) (by simp [Dist.boolCols])
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  obtain ⟨z1, c1⟩ := Mem.zdvd hD hw0 (e := Dist.mul3 (c Dist.kSh) (Dist.notE (c Dist.e1))
    (Dist.notE (n Dist.kSh))) (by simp [Dist.constraints, Dist.cShard])
  obtain ⟨z2, c2⟩ := Mem.zdvd hD hw0 (e := Dist.mul3 (c Dist.kSh) (c Dist.e1)
    (.mul (Dist.notE (c Dist.side)) (Dist.notE (n Dist.kSh)))) (by simp [Dist.constraints, Dist.cShard])
  obtain ⟨z3, c3⟩ := Mem.zdvd hD hw0 (e := Dist.mul3 (c Dist.kSh) (c Dist.e1)
    (.mul (c Dist.side) (Dist.notE (n Dist.kGH)))) (by simp [Dist.constraints, Dist.cShard])
  obtain ⟨z4, c4⟩ := Mem.zdvd hD hw0 (e := .mul (c Dist.kGH) (Dist.notE (n Dist.kC)))
    (by simp [Dist.constraints, Dist.cGrid])
  obtain ⟨z5, c5⟩ := Mem.zdvd hD hw0 (e := Dist.mul3 (c Dist.kC) (Dist.notE (c Dist.e1))
    (Dist.notE (n Dist.kC))) (by simp [Dist.constraints, Dist.cGrid])
  obtain ⟨z6, c6⟩ := Mem.zdvd hD hw0 (e := Dist.mul3 (c Dist.kC) (c Dist.e1)
    (.mul (Dist.notE (c Dist.e2)) (Dist.notE (n Dist.kGH)))) (by simp [Dist.constraints, Dist.cGrid])
  obtain ⟨z7, c7⟩ := Mem.zdvd hD hw0 (e := sub (c Dist.eI) (Dist.mul3 (c Dist.kC) (c Dist.e1) (c Dist.e2)))
    (by simp [Dist.constraints, Dist.cGrid])
  obtain ⟨z8, c8⟩ := Mem.zdvd hD hw0 (e := Dist.mul3 (c Dist.eI) (n Dist.act) (Dist.notE (n Dist.kSh)))
    (by simp [Dist.constraints, Dist.cGrid])
  simp only [Dist.mul3, Dist.notE, zev_mul, zev_sub, zev_c, zev_n, zev_k, cur_cv, nxt_cv hw, h1, h2,
    h3, h4, Int.natCast_one, Int.natCast_zero, Int.sub_zero, Int.sub_self, Int.mul_one, Int.one_mul,
    Int.mul_zero, Int.zero_mul] at c1 c2 c3 c4 c5 c6 c7 c8
  have := lt Dist.side; have := lt Dist.e2
  rcases hd with h | h | h
  · have g1 : cv tr t w Dist.kGH = 0 := by omega
    have g2 : cv tr t w Dist.kC = 0 := by omega
    rw [h] at c1 c2 c3
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he1 with e | e <;>
      simp only [e, Int.natCast_one, Int.natCast_zero, Int.sub_zero, Int.sub_self, Int.mul_one,
        Int.one_mul, Int.mul_zero, Int.zero_mul] at c1 c2 c3 <;> omega
  · rw [h] at c4
    simp only [Int.natCast_one, Int.one_mul] at c4
    omega
  · have g1 : cv tr t w Dist.kSh = 0 := by omega
    rw [h] at c5 c6 c7
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he1 with e | e
    · simp only [e, Int.natCast_one, Int.natCast_zero, Int.sub_zero, Int.sub_self, Int.mul_one,
        Int.one_mul, Int.mul_zero, Int.zero_mul] at c5
      omega
    · simp only [e, Int.natCast_one, Int.natCast_zero, Int.sub_zero, Int.sub_self, Int.mul_one,
        Int.one_mul, Int.mul_zero, Int.zero_mul] at c6 c7
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 heI with e' | e' <;>
        simp only [e', Int.natCast_one, Int.natCast_zero, Int.sub_zero, Int.sub_self, Int.mul_one,
          Int.one_mul, Int.mul_zero, Int.zero_mul] at c7 c8 <;> omega

/-! ## The shape of a request block (no bitmap needed) -/

/-- Invariant on the first row of byte `yy` of a block. -/
def BS (tr : Trace Fp) (t f yy : Nat) : Prop :=
  f + 4 * yy < tr.height t ∧ cv tr t (f + 4 * yy) kS = 1 ∧ cv tr t (f + 4 * yy) u0 = 0 ∧
    cv tr t (f + 4 * yy) u1 = 0 ∧ cv tr t (f + 4 * yy) y = yy ∧
    ∀ col ∈ reqCols, cv tr t (f + 4 * yy) col = cv tr t f col

/-- Row `f + x` of a block. -/
def RS (tr : Trace Fp) (t f x : Nat) : Prop :=
  f + x < tr.height t ∧ cv tr t (f + x) kS = 1 ∧ cv tr t (f + x) re = (if x = 19 then 1 else 0) ∧
    ∀ col ∈ reqCols, cv tr t (f + x) col = cv tr t f col

theorem shape_byte (hL : SLocal tr t pub) {f yy : Nat} (hyy : yy ≤ 4) (hI : BS tr t f yy) :
    (∀ kk, kk < 4 → RS tr t f (4 * yy + kk)) ∧ (yy < 4 → BS tr t f (yy + 1)) := by
  obtain ⟨hg, hk0, hu00, hu10, hy0, hc0⟩ := hI
  generalize hgd : f + 4 * yy = g at hg hk0 hu00 hu10 hy0 hc0
  obtain ⟨re0, hw1, k1, u1e, y1, c1, -, -⟩ :=
    mid_step hL hg hk0 (uu := 0) (by rw [hu00, hu10]) (by omega) hy0 hyy
  obtain ⟨re1, hw2, k2, u2e, y2, c2, -, -⟩ := mid_step hL hw1 k1 (uu := 1) u1e (by omega) y1 hyy
  obtain ⟨re2, hw3, k3, u3e, y3, c3, -, -⟩ := mid_step hL hw2 k2 (uu := 2) u2e (by omega) y2 hyy
  have hu03 := bool_of hL hw3 (x := u0) (by simp [boolCols, sharedBool, ownBool])
  have hu13 := bool_of hL hw3 (x := u1) (by simp [boolCols, sharedBool, ownBool])
  have hu0e : cv tr t (g + 1 + 1 + 1) u0 = 1 := by omega
  have hu1e : cv tr t (g + 1 + 1 + 1) u1 = 1 := by omega
  have cc1 : ∀ col ∈ reqCols, cv tr t (g + 1) col = cv tr t f col := fun col h => by
    rw [c1 col h, hc0 col h]
  have cc2 : ∀ col ∈ reqCols, cv tr t (g + 1 + 1) col = cv tr t f col := fun col h => by
    rw [c2 col h, cc1 col h]
  have cc3 : ∀ col ∈ reqCols, cv tr t (g + 1 + 1 + 1) col = cv tr t f col := fun col h => by
    rw [c3 col h, cc2 col h]
  refine ⟨fun kk hkk => ?_, fun hlt => ?_⟩
  · unfold RS
    rcases (by omega : kk = 0 ∨ kk = 1 ∨ kk = 2 ∨ kk = 3) with h | h | h | h <;> subst h
    · rw [show f + (4 * yy + 0) = g by omega]
      exact ⟨hg, hk0, by rw [re0, if_neg (by omega)], hc0⟩
    · rw [show f + (4 * yy + 1) = g + 1 by omega]
      exact ⟨hw1, k1, by rw [re1, if_neg (by omega)], cc1⟩
    · rw [show f + (4 * yy + 2) = g + 1 + 1 by omega]
      exact ⟨hw2, k2, by rw [re2, if_neg (by omega)], cc2⟩
    · rw [show f + (4 * yy + 3) = g + 1 + 1 + 1 by omega]
      refine ⟨hw3, k3, ?_, cc3⟩
      rw [re_of hL hw3 k3]
      by_cases h4 : yy = 4
      · rw [if_pos ⟨by rw [y3, h4], hu0e, hu1e⟩, if_pos (by omega)]
      · rw [if_neg (fun h => h4 (by rw [← y3]; exact h.1)), if_neg (by omega)]
  · obtain ⟨-, hw4, k4, u04, u14, y4, c4, -⟩ := end_step hL hw3 k3 hu0e hu1e y3 hlt
    unfold BS
    rw [show f + 4 * (yy + 1) = g + 1 + 1 + 1 + 1 by omega]
    exact ⟨hw4, k4, u04, u14, y4, fun col h => by rw [c4 col h, cc3 col h]⟩

/-- **Shape pass.** -/
theorem shape_all (hL : SLocal tr t pub) {f : Nat} (hf : f < tr.height t) (hfQ : cv tr t f fQ = 1) :
    ∀ x, x < 20 → RS tr t f x := by
  have main : ∀ yy, yy ≤ 4 → BS tr t f yy ∧ ∀ x, x < 4 * yy → RS tr t f x := by
    intro yy
    induction yy with
    | zero =>
      intro _
      obtain ⟨hk, hu0, hu1, hy, -⟩ := row_start hL hf hfQ
      exact ⟨⟨hf, hk, hu0, hu1, hy, fun _ _ => rfl⟩, fun x hx => by omega⟩
    | succ yy ih =>
      intro hyy
      obtain ⟨hI, hR⟩ := ih (by omega)
      obtain ⟨hrows, hnext⟩ := shape_byte hL (by omega) hI
      refine ⟨hnext (by omega), fun x hx => ?_⟩
      by_cases h : x < 4 * yy
      · exact hR x h
      · have := hrows (x - 4 * yy) (by omega)
        rwa [show 4 * yy + (x - 4 * yy) = x by omega] at this
  intro x hx
  obtain ⟨hI, hR⟩ := main 4 (Nat.le_refl _)
  by_cases h : x < 16
  · exact hR x (by omega)
  · have := (shape_byte hL (Nat.le_refl _) hI).1 (x - 16) (by omega)
    rwa [show 4 * 4 + (x - 16) = x by omega] at this

/-! ## Every request row lies in a block -/

/-- Row 0 is not a request row. -/
theorem kS_zero (hL : SLocal tr t pub) (h0 : 0 < tr.height t) : cv tr t 0 kS ≠ 1 := by
  intro hk
  have F := row_flags hL h0
  rcases row_first hL h0 (by omega) with h | h <;> omega

/-- The row above a request row is a param row, a request row, or (for a request start)
a request end. -/
theorem prev_kind (hL : Local ScanDist.constraints tr t pub) {v : Nat} (hv : v + 1 < tr.height t)
    (hk : cv tr t (v + 1) kS = 1) :
    cv tr t v kP = 1 ∨ cv tr t v kS = 1 := by
  have hS := SLocal.of_sd hL
  have hv0 : v < tr.height t := by omega
  have F0 := row_flags hS hv0
  have F1 := row_flags hS hv
  by_cases ha : cv tr t v act = 0
  · have := row_pad hS hv ha; omega
  · have hd := dist_next hL hv
    simp only [kSh, kGH, kC] at F0
    simp only [kS] at hk
    simp only [kS] at hd
    by_cases h : cv tr t v kP = 1
    · exact Or.inl h
    · by_cases h' : cv tr t v kS = 1
      · exact Or.inr h'
      · have := hd (by simp only [kP, kS] at h h' F0; omega); omega

/-- **Every request row lies in a block.** -/
theorem kS_block (hL : Local ScanDist.constraints tr t pub) :
    ∀ w, w < tr.height t → cv tr t w kS = 1 →
      ∃ f, f ≤ w ∧ w < f + 20 ∧ cv tr t f fQ = 1 := by
  have hS := SLocal.of_sd hL
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro hw hk
    by_cases hq : cv tr t w fQ = 1
    · exact ⟨w, Nat.le_refl _, by omega, hq⟩
    rcases w with _ | v
    · exact absurd hk (kS_zero hS hw)
    have hv0 : v < tr.height t := by omega
    rcases prev_kind hL hw hk with hp | hp
    · exact absurd (row_param hS hv0 hp).2.2.2.1 hq
    · have hre := bool_of hS hv0 (x := re) (by simp [boolCols, ownBool])
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hre with h0 | h1
      · obtain ⟨f, hf1, hf2, hfQ⟩ := ih v (by omega) hv0 hp
        have hfh : f < tr.height t := by omega
        refine ⟨f, by omega, ?_, hfQ⟩
        by_cases e : v = f + 19
        · have := (shape_all hS hfh hfQ 19 (by omega)).2.2.1
          rw [← e, h0] at this; simp at this
        · omega
      · exact absurd ((row_after_end hS hw h1).1 hk) hq

theorem fQ_le_kS (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (h : cv tr t w fQ = 1) :
    cv tr t w kS = 1 := (row_start hL hw h).1

/-- **Every request end is the end row of a block.** -/
theorem re_block (hL : Local ScanDist.constraints tr t pub) {w : Nat} (hw : w < tr.height t)
    (hre : cv tr t w re = 1) : ∃ f, w = f + 19 ∧ cv tr t f fQ = 1 := by
  have hS := SLocal.of_sd hL
  have F := row_flags hS hw
  obtain ⟨f, h1, h2, hfQ⟩ := kS_block hL w hw (by have := bool_of hS hw (x := kS) (by simp [boolCols, sharedBool]); omega)
  have hR := (shape_all hS (by omega) hfQ (w - f) (by omega)).2.2.1
  rw [show f + (w - f) = w by omega, hre] at hR
  refine ⟨f, ?_, hfQ⟩
  by_cases e : w - f = 19
  · omega
  · rw [if_neg e] at hR; simp at hR

/-- **Every request start has the param row of its section above it.** -/
theorem param_of (hL : Local ScanDist.constraints tr t pub) :
    ∀ f, f < tr.height t → cv tr t f fQ = 1 →
      ∃ p, p < f ∧ cv tr t p kP = 1 ∧ ∀ col ∈ instCols, cv tr t f col = cv tr t p col := by
  have hS := SLocal.of_sd hL
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
    intro hf hq
    have hk := fQ_le_kS hS hf hq
    rcases f with _ | v
    · exact absurd hk (kS_zero hS hf)
    have hv0 : v < tr.height t := by omega
    rcases prev_kind hL hf hk with hp | hp
    · exact ⟨v, by omega, hp, fun col h => (row_param hS hv0 hp).2.2.2.2.2 col h⟩
    · have hre := bool_of hS hv0 (x := re) (by simp [boolCols, ownBool])
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hre with h0 | h1
      · exact absurd (row_step hS hv0 hp h0).2.2.1 (by omega)
      · obtain ⟨f', e, hq'⟩ := re_block hL hv0 h1
        have hf' : f' < tr.height t := by omega
        obtain ⟨p, hp1, hp2, hp3⟩ := ih f' (by omega) hf' hq'
        have hc := (shape_all hS hf' hq' 19 (by omega)).2.2.2
        have ha := (row_after_end hS hf h1).2 hq
        refine ⟨p, by omega, hp2, fun col h => ?_⟩
        have hr : col ∈ reqCols := by
          simp only [instCols, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl <;> simp [reqCols]
        rw [ha.2 col h, e, hc col hr, hp3 col h]

end

end ZkFormal.NearV3.Sched.Scan

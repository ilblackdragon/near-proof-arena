import ZkFormal.NearV3.Sched.View.Scan
import ZkFormal.NearV3.Sched.View.ScanSpec

/-!
# ZkFormal.NearV3.Sched.View.ScanReq — a request block of `sscV3` and its contract

A request block is the 20 rows `f … f + 19` after a request-start row `f` (`fQ = 1`), whose
register holds the request's bytes `q₀ … q₄` (the public `SRAW` record).

* `struct_all` (structure pass): every row `f + x`, `x < 20`, is a request row with the request
  constants of row `f`, bit position `2x`, `re = [x = 19]`, and its bits `b₀, b₁` are bits `2x`,
  `2x + 1` of the bitmap (`getBit`) — the byte register is consumed two bits per row and rotated.
* `vals_all` (value pass): `cur, j` on row `f + x` are the scan state `stAt … (2x)`.
* **`scan_request`**: `m = (incsOf p bm).length`, every `INC` sent with nonzero multiplicity at
  slot `k` of row `f + x` is `(τ, cid·64 + j, (incsOf p bm)[j], len − j − 1, s, r, link)` for the
  index `j = (stAt … (2x + k)).2 < len` of a set bit `2x + k` (distinct slots give distinct
  `j`: `ScanSpec.stAt_snd_lt`), and the end row's `PUSH` / `READ` messages.

The quotients are exact (`Q = D·(pos + 1)/40`) by the table's range checks `Q₀, Q₁ < 2^23`
(`Scan.q_ranges`, `Scan.q_exact`), given `D < 2^24`.
-/

namespace ZkFormal.NearV3.Sched.Scan

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched.ScanSpec

/-- Row facts of row `f + x` of a request block. -/
def RF (tr : Trace Fp) (t f : Nat) (bm : List UInt8) (x : Nat) : Prop :=
  f + x < tr.height t ∧ cv tr t (f + x) kS = 1 ∧ cv tr t (f + x) re = (if x = 19 then 1 else 0) ∧
    (∀ col ∈ reqCols, cv tr t (f + x) col = cv tr t f col) ∧ posv tr t (f + x) = 2 * x ∧
    (NearSpecV3.Scheduler.getBit bm (2 * x) = true ↔ cv tr t (f + x) b0 = 1) ∧
    (NearSpecV3.Scheduler.getBit bm (2 * x + 1) = true ↔ cv tr t (f + x) b1 = 1)

/-- Invariant on the first row `f + 4·yy` of byte `yy`. -/
def BI (tr : Trace Fp) (t f yy : Nat) : Prop :=
  f + 4 * yy < tr.height t ∧ cv tr t (f + 4 * yy) kS = 1 ∧ cv tr t (f + 4 * yy) u0 = 0 ∧
    cv tr t (f + 4 * yy) u1 = 0 ∧ cv tr t (f + 4 * yy) y = yy ∧
    (∀ col ∈ reqCols, cv tr t (f + 4 * yy) col = cv tr t f col) ∧
    (∀ i, yy + i ≤ 4 → cv tr t (f + 4 * yy) (q i) = cv tr t f (q (yy + i)))

theorem getBit_byte (bm : List UInt8) (yy kk : Nat) (hk : kk < 8) :
    NearSpecV3.Scheduler.getBit bm (8 * yy + kk) = true ↔ (bm.getD yy 0).toNat / 2 ^ kk % 2 = 1 := by
  unfold NearSpecV3.Scheduler.getBit
  rw [show (8 * yy + kk) / 8 = yy by omega, show (8 * yy + kk) % 8 = kk by omega,
    Nat.shiftRight_eq_div_pow]
  simp

theorem bits_of_digits {B a0 c0 a1 c1 a2 c2 a3 c3 : Nat}
    (ha0 : a0 ≤ 1) (hc0 : c0 ≤ 1) (ha1 : a1 ≤ 1) (hc1 : c1 ≤ 1) (ha2 : a2 ≤ 1) (hc2 : c2 ≤ 1)
    (ha3 : a3 ≤ 1) (hc3 : c3 ≤ 1)
    (hB : B = (a0 + 2 * c0) + 4 * (a1 + 2 * c1) + 16 * (a2 + 2 * c2) + 64 * (a3 + 2 * c3)) :
    B / 2 ^ 0 % 2 = a0 ∧ B / 2 ^ 1 % 2 = c0 ∧ B / 2 ^ 2 % 2 = a1 ∧ B / 2 ^ 3 % 2 = c1 ∧
      B / 2 ^ 4 % 2 = a2 ∧ B / 2 ^ 5 % 2 = c2 ∧ B / 2 ^ 6 % 2 = a3 ∧ B / 2 ^ 7 % 2 = c3 := by
  show B / 1 % 2 = a0 ∧ B / 2 % 2 = c0 ∧ B / 4 % 2 = a1 ∧ B / 8 % 2 = c1 ∧
      B / 16 % 2 = a2 ∧ B / 32 % 2 = c2 ∧ B / 64 % 2 = a3 ∧ B / 128 % 2 = c3
  omega

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- `re = [y = 4 ∧ u = 3]` on a request row. -/
theorem re_of (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1) :
    cv tr t w re = if cv tr t w y = 4 ∧ cv tr t w u0 = 1 ∧ cv tr t w u1 = 1 then 1 else 0 := by
  obtain ⟨-, -, -, he4, hre, -, -⟩ := row_cur hL hw hk
  have b := fun x (hx : x ∈ boolCols) => bool_of hL hw hx
  have h4 := b e4 (by simp [boolCols]); have hu0 := b u0 (by simp [boolCols])
  have hu1 := b u1 (by simp [boolCols])
  rw [hre]
  split
  · next hc =>
    obtain ⟨hy, h0, h1⟩ := hc
    rw [h0, h1, he4.2 hy]
  · next hc =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h4 with h | h
    · rw [h, Nat.zero_mul, Nat.zero_mul]
    · have hy := he4.1 h
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu0 with e | e
      · rw [e, Nat.mul_zero, Nat.zero_mul]
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu1 with e' | e'
        · rw [e', Nat.mul_zero]
        · exact absurd ⟨hy, e, e'⟩ hc

/-- A step in the middle of a byte (`u < 3`). -/
theorem mid_step (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1)
    {uu yy : Nat} (hu : cv tr t w u0 + 2 * cv tr t w u1 = uu) (huu : uu < 3)
    (hy : cv tr t w y = yy) (hyy : yy ≤ 4) :
    cv tr t w re = 0 ∧ w + 1 < tr.height t ∧ cv tr t (w + 1) kS = 1 ∧
      cv tr t (w + 1) u0 + 2 * cv tr t (w + 1) u1 = uu + 1 ∧ cv tr t (w + 1) y = yy ∧
      (∀ x ∈ reqCols, cv tr t (w + 1) x = cv tr t w x) ∧
      (∀ i, i < 4 → cv tr t (w + 1) (q (i + 1)) = cv tr t w (q (i + 1))) ∧
      ∃ z : Int, (cv tr t w (q 0) : Int) =
        cv tr t w b0 + 2 * cv tr t w b1 + 4 * cv tr t (w + 1) (q 0) + 2013265921 * z := by
  have hu0 := bool_of hL hw (x := u0) (by simp [boolCols])
  have hu1 := bool_of hL hw (x := u1) (by simp [boolCols])
  have hp : cv tr t w u0 * cv tr t w u1 = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu0 with e | e <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu1 with e' | e' <;> simp only [e, e'] <;> omega
  have hre : cv tr t w re = 0 := by
    rw [re_of hL hw hk, if_neg]; omega
  obtain ⟨hw1, k1, -, hc, hu', hy', -, -, -, -, hkeep, hcons⟩ := row_step hL hw hk hre
  rw [hp] at hu' hy'
  refine ⟨hre, hw1, k1, by omega, by rw [hy', hy]; omega, hc, hkeep hp, hcons hp⟩

/-- The byte-end step (`u = 3`, `y < 4`): rotation. -/
theorem end_step (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1)
    (hu0 : cv tr t w u0 = 1) (hu1 : cv tr t w u1 = 1) {yy : Nat} (hy : cv tr t w y = yy)
    (hyy : yy < 4) :
    cv tr t w re = 0 ∧ w + 1 < tr.height t ∧ cv tr t (w + 1) kS = 1 ∧ cv tr t (w + 1) u0 = 0 ∧
      cv tr t (w + 1) u1 = 0 ∧ cv tr t (w + 1) y = yy + 1 ∧
      (∀ x ∈ reqCols, cv tr t (w + 1) x = cv tr t w x) ∧
      (∀ i, i < 4 → cv tr t (w + 1) (q i) = cv tr t w (q (i + 1))) := by
  have hre : cv tr t w re = 0 := by
    rw [re_of hL hw hk, if_neg]; omega
  have hp : cv tr t w u0 * cv tr t w u1 = 1 := by rw [hu0, hu1]
  have hw1 := row_next_lt_kS hL hw hk
  have hu0' := bool_of hL hw1 (x := u0) (by simp [boolCols])
  have hu1' := bool_of hL hw1 (x := u1) (by simp [boolCols])
  obtain ⟨-, k1, -, hc, hu', hy', -, -, -, hrot, -, -⟩ := row_step hL hw hk hre
  rw [hp, hu0, hu1] at hu'
  rw [hp, hy] at hy'
  refine ⟨hre, hw1, k1, by omega, by omega, by rw [hy']; omega, hc, hrot hp⟩

theorem byte_step (hL : SLocal tr t pub) {f : Nat} {bm : List UInt8}
    (hbm : ∀ i, i < 5 → (bm.getD i 0).toNat = cv tr t f (q i)) {yy : Nat} (hyy : yy ≤ 4)
    (hI : BI tr t f yy) :
    (∀ kk, kk < 4 → RF tr t f bm (4 * yy + kk)) ∧ (yy < 4 → BI tr t f (yy + 1)) := by
  obtain ⟨hg, hk0, hu00, hu10, hy0, hc0, hq0⟩ := hI
  have hB : cv tr t (f + 4 * yy) (q 0) = cv tr t f (q yy) := by
    have := hq0 0 (by omega); simpa using this
  have hBlt : cv tr t f (q yy) < 256 := by
    rw [← hbm yy (by omega)]; exact UInt8.toNat_lt _
  generalize hgd : f + 4 * yy = g at hg hk0 hu00 hu10 hy0 hc0 hq0 hB
  obtain ⟨re0, hw1, k1, u1e, y1, c1, keep1, z0, hz0⟩ :=
    mid_step hL hg hk0 (uu := 0) (by rw [hu00, hu10]) (by omega) hy0 hyy
  obtain ⟨re1, hw2, k2, u2e, y2, c2, keep2, z1, hz1⟩ :=
    mid_step hL hw1 k1 (uu := 1) u1e (by omega) y1 hyy
  obtain ⟨re2, hw3, k3, u3e, y3, c3, keep3, z2, hz2⟩ :=
    mid_step hL hw2 k2 (uu := 2) u2e (by omega) y2 hyy
  have hw3' : g + 1 + 1 + 1 < tr.height t := hw3
  have bb := fun w (hw : w < tr.height t) x (hx : x ∈ boolCols) => bool_of hL hw hx
  have hu03 := bb _ hw3' u0 (by simp [boolCols]); have hu13 := bb _ hw3' u1 (by simp [boolCols])
  have hu0e : cv tr t (g + 1 + 1 + 1) u0 = 1 := by omega
  have hu1e : cv tr t (g + 1 + 1 + 1) u1 = 1 := by omega
  have hq3 := (row_cur hL hw3' k3).2.2.1 hu0e hu1e
  have hw0 : g < tr.height t := hg
  have hw1' : g + 1 < tr.height t := hw1
  have hw2' : g + 1 + 1 < tr.height t := hw2
  have a0 := bb _ hw0 b0 (by simp [boolCols]); have c0 := bb _ hw0 b1 (by simp [boolCols])
  have a1 := bb _ hw1' b0 (by simp [boolCols]); have c1' := bb _ hw1' b1 (by simp [boolCols])
  have a2 := bb _ hw2' b0 (by simp [boolCols]); have c2' := bb _ hw2' b1 (by simp [boolCols])
  have a3 := bb _ hw3' b0 (by simp [boolCols]); have c3' := bb _ hw3' b1 (by simp [boolCols])
  have hdig : (bm.getD yy 0).toNat =
      (cv tr t g b0 + 2 * cv tr t g b1) + 4 * (cv tr t (g + 1) b0 + 2 * cv tr t (g + 1) b1) +
      16 * (cv tr t (g + 1 + 1) b0 + 2 * cv tr t (g + 1 + 1) b1) +
      64 * (cv tr t (g + 1 + 1 + 1) b0 + 2 * cv tr t (g + 1 + 1 + 1) b1) := by
    rw [hbm yy (by omega)]
    have := cv_lt (tr := tr) (t := t) (g + 1) (q 0)
    have := cv_lt (tr := tr) (t := t) (g + 1 + 1) (q 0)
    have := cv_lt (tr := tr) (t := t) (g + 1 + 1 + 1) (q 0)
    omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := bits_of_digits a0 c0 a1 c1' a2 c2' a3 c3' hdig
  have gb := fun kk (hk : kk < 8) => getBit_byte bm yy kk hk
  have hre3 := re_of hL hw3' k3
  rw [y3, hu0e, hu1e] at hre3
  -- the four rows
  have rows : ∀ kk, kk < 4 → RF tr t f bm (4 * yy + kk) := by
    intro kk hk
    unfold RF
    rcases (by omega : kk = 0 ∨ kk = 1 ∨ kk = 2 ∨ kk = 3) with h | h | h | h <;> subst h
    · rw [show f + (4 * yy + 0) = g by omega, show 2 * (4 * yy + 0) + 1 = 8 * yy + 1 by omega,
        show 2 * (4 * yy + 0) = 8 * yy + 0 by omega]
      refine ⟨hw0, hk0, by rw [re0, if_neg (by omega)], hc0, ?_, ?_, ?_⟩
      · unfold posv; omega
      · rw [gb 0 (by omega), d0]
      · rw [gb 1 (by omega), d1]
    · rw [show f + (4 * yy + 1) = g + 1 by omega, show 2 * (4 * yy + 1) + 1 = 8 * yy + 3 by omega,
        show 2 * (4 * yy + 1) = 8 * yy + 2 by omega]
      refine ⟨hw1', k1, by rw [re1, if_neg (by omega)], fun x hx => ?_, ?_, ?_, ?_⟩
      · rw [c1 x hx]; exact hc0 x hx
      · unfold posv; omega
      · rw [gb 2 (by omega), d2]
      · rw [gb 3 (by omega), d3]
    · rw [show f + (4 * yy + 2) = g + 1 + 1 by omega, show 2 * (4 * yy + 2) + 1 = 8 * yy + 5 by omega,
        show 2 * (4 * yy + 2) = 8 * yy + 4 by omega]
      refine ⟨hw2', k2, by rw [re2, if_neg (by omega)], fun x hx => ?_, ?_, ?_, ?_⟩
      · rw [c2 x hx, c1 x hx]; exact hc0 x hx
      · unfold posv; omega
      · rw [gb 4 (by omega), d4]
      · rw [gb 5 (by omega), d5]
    · rw [show f + (4 * yy + 3) = g + 1 + 1 + 1 by omega, show 2 * (4 * yy + 3) + 1 = 8 * yy + 7 by omega,
        show 2 * (4 * yy + 3) = 8 * yy + 6 by omega]
      refine ⟨hw3', k3, ?_, fun x hx => ?_, ?_, ?_, ?_⟩
      · rw [hre3]
        by_cases h4 : yy = 4
        · rw [if_pos ⟨h4, rfl, rfl⟩, if_pos (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]
      · rw [c3 x hx, c2 x hx, c1 x hx]; exact hc0 x hx
      · unfold posv; omega
      · rw [gb 6 (by omega), d6]
      · rw [gb 7 (by omega), d7]
  refine ⟨rows, fun hy4 => ?_⟩
  obtain ⟨-, hw4, k4, u04, u14, y4, c4, rot4⟩ := end_step hL hw3' k3 hu0e hu1e y3 hy4
  have ef : f + 4 * (yy + 1) = g + 1 + 1 + 1 + 1 := by omega
  unfold BI
  rw [ef]
  refine ⟨hw4, k4, u04, u14, y4, fun x hx => ?_, fun i hi => ?_⟩
  · rw [c4 x hx, c3 x hx, c2 x hx, c1 x hx]; exact hc0 x hx
  · rw [show yy + 1 + i = yy + (i + 1) by omega, rot4 i (by omega), keep3 i (by omega),
      keep2 i (by omega), keep1 i (by omega)]
    exact hq0 (i + 1) (by omega)

/-- **Structure pass.** -/
theorem struct_all (hL : SLocal tr t pub) {f : Nat} (hf : f < tr.height t) (hfQ : cv tr t f fQ = 1)
    {bm : List UInt8} (hbm : ∀ i, i < 5 → (bm.getD i 0).toNat = cv tr t f (q i)) :
    ∀ x, x < 20 → RF tr t f bm x := by
  have main : ∀ yy, yy ≤ 4 → BI tr t f yy ∧ ∀ x, x < 4 * yy → RF tr t f bm x := by
    intro yy
    induction yy with
    | zero =>
      intro _
      obtain ⟨hk, hu0, hu1, hy, -⟩ := row_start hL hf hfQ
      refine ⟨⟨hf, hk, hu0, hu1, hy, fun _ _ => rfl, fun i _ => by simp⟩, fun x hx => by omega⟩
    | succ yy ih =>
      intro hyy
      obtain ⟨hI, hR⟩ := ih (by omega)
      obtain ⟨hrows, hnext⟩ := byte_step hL hbm (by omega) hI
      refine ⟨hnext (by omega), fun x hx => ?_⟩
      by_cases h : x < 4 * yy
      · exact hR x h
      · have := hrows (x - 4 * yy) (by omega)
        rwa [show 4 * yy + (x - 4 * yy) = x by omega] at this
  intro x hx
  obtain ⟨hI, hR⟩ := main 4 (Nat.le_refl _)
  by_cases h : x < 16
  · exact hR x (by omega)
  · have := (byte_step hL hbm (Nat.le_refl _) hI).1 (x - 16) (by omega)
    rwa [show 4 * 4 + (x - 16) = x by omega] at this

/-! ## Value pass -/

/-- One row of the value pass. -/
theorem val_step (hL : SLocal tr t pub) {f : Nat} {bm : List UInt8}
    {p : NearSpecV3.Scheduler.Params} (hbase : cv tr t f base = p.base)
    (hdd : cv tr t f dd = p.maxSingleGrant - p.base) (hb24 : p.base < 2 ^ 24)
    (hD24 : p.maxSingleGrant - p.base < 2 ^ 24) {x : Nat} (hx : x < 20) (hR : RF tr t f bm x)
    (hcur : cv tr t (f + x) cur = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).1)
    (hj : cv tr t (f + x) j = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).2) :
    cv tr t (f + x) cm = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).1 ∧
      cv tr t (f + x) j + cv tr t (f + x) b0 =
        (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).2 ∧
      (cv tr t (f + x) b0 = 1 →
        cv tr t (f + x) base + cv tr t (f + x) Q0 = (NearSpecV3.Scheduler.requestValues p).getD (2 * x) 0) ∧
      (cv tr t (f + x) b1 = 1 →
        cv tr t (f + x) base + cv tr t (f + x) Q1 =
          (NearSpecV3.Scheduler.requestValues p).getD (2 * x + 1) 0) ∧
      (x < 19 →
        cv tr t (f + x + 1) cur = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 2)).1 ∧
        cv tr t (f + x + 1) j = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 2)).2) ∧
      (x = 19 → cv tr t (f + x) m = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base 40).2) := by
  obtain ⟨hlt, hk, hre, hc, hpos, hg0, hg1⟩ := hR
  have hbase' : cv tr t (f + x) base = p.base := (hc base (by simp [reqCols])).trans hbase
  have hdd' : cv tr t (f + x) dd = p.maxSingleGrant - p.base := (hc dd (by simp [reqCols])).trans hdd
  obtain ⟨hr0, hr1, hz0, hz1⟩ := row_val hL hlt hk
  obtain ⟨hQa, hQb⟩ := q_ranges hL hlt
  have hQx : (cv tr t (f + x) b0 = 1 → cv tr t (f + x) Q0 < 2 ^ 25) ∧
      (cv tr t (f + x) b1 = 1 → cv tr t (f + x) Q1 < 2 ^ 25) :=
    ⟨fun _ => Nat.lt_trans hQa (by decide), fun _ => Nat.lt_trans hQb (by decide)⟩
  rw [hpos, hdd'] at hz0 hz1
  have m1 := Nat.mul_le_mul_left (p.maxSingleGrant - p.base) (show 2 * x + 1 ≤ 40 by omega)
  have m2 := Nat.mul_le_mul_left (p.maxSingleGrant - p.base) (show 2 * x + 2 ≤ 40 by omega)
  have hv0 : cv tr t (f + x) b0 = 1 →
      cv tr t (f + x) base + cv tr t (f + x) Q0 = (NearSpecV3.Scheduler.requestValues p).getD (2 * x) 0 := by
    intro h
    rw [requestValues_getD p (by omega), hbase', q_exact hr0 (hQx.1 h) (by omega) hz0]
  have hv1 : cv tr t (f + x) b1 = 1 →
      cv tr t (f + x) base + cv tr t (f + x) Q1 =
        (NearSpecV3.Scheduler.requestValues p).getD (2 * x + 1) 0 := by
    intro h
    rw [requestValues_getD p (by omega), hbase', q_exact hr1 (hQx.2 h) (by omega) hz1]
  have hb0 := bool_of hL hlt (x := b0) (by simp [boolCols])
  have hb1 := bool_of hL hlt (x := b1) (by simp [boolCols])
  obtain ⟨hcm1, hcm0, -, -, -, hm, -⟩ := row_cur hL hlt hk
  have hjle := stAt_snd_le (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)
  have hQ0lt := fun h => hQx.1 h
  have hQ1lt := fun h => hQx.2 h
  -- after b₀
  have s1 : cv tr t (f + x) cm = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).1 ∧
      cv tr t (f + x) j + cv tr t (f + x) b0 =
        (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).2 := by
    rw [stAt_succ]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb0 with h | h
    · have : NearSpecV3.Scheduler.getBit bm (2 * x) = false := by
        cases e : NearSpecV3.Scheduler.getBit bm (2 * x)
        · rfl
        · have := hg0.1 e; omega
      rw [this, if_neg (by simp), h, hcm0 h, hcur, hj]; exact ⟨rfl, rfl⟩
    · rw [if_pos (hg0.2 h), hcm1 h, h, hj]
      have := hv0 h; have := hQ0lt h
      refine ⟨?_, rfl⟩
      simp only; omega
  -- after b₁
  have s2 : ∀ v, v = cv tr t (f + x) j + cv tr t (f + x) b0 + cv tr t (f + x) b1 →
      v = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 2)).2 := by
    intro v hv
    rw [show 2 * x + 2 = 2 * x + 1 + 1 by omega, stAt_succ]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb1 with h | h
    · have : NearSpecV3.Scheduler.getBit bm (2 * x + 1) = false := by
        cases e : NearSpecV3.Scheduler.getBit bm (2 * x + 1)
        · rfl
        · have := hg1.1 e; omega
      rw [this, if_neg (by simp), ← s1.2]; omega
    · rw [if_pos (hg1.2 h), ← s1.2]; simp only; omega
  refine ⟨s1.1, s1.2, hv0, hv1, fun h19 => ?_, fun h19 => ?_⟩
  · have hre0 : cv tr t (f + x) re = 0 := by rw [hre, if_neg (by omega)]
    obtain ⟨-, -, -, -, -, -, hj', hc1, hc0, -, -, -⟩ := row_step hL hlt hk hre0
    refine ⟨?_, ?_⟩
    · rw [show 2 * x + 2 = 2 * x + 1 + 1 by omega, stAt_succ]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb1 with h | h
      · have : NearSpecV3.Scheduler.getBit bm (2 * x + 1) = false := by
          cases e : NearSpecV3.Scheduler.getBit bm (2 * x + 1)
          · rfl
          · have := hg1.1 e; omega
        rw [this, if_neg (by simp), hc0 h, s1.1]
      · rw [if_pos (hg1.2 h), hc1 h]
        have := hv1 h; have := hQ1lt h
        simp only; omega
    · rw [hj']
      apply s2
      omega
  · have hre1 : cv tr t (f + x) re = 1 := by rw [hre, if_pos h19]
    rw [hm hre1]
    rw [show (40 : Nat) = 2 * x + 2 by omega]
    apply s2
    omega

/-- **Value pass.** -/
theorem vals_all (hL : SLocal tr t pub) {f : Nat} (hf : f < tr.height t) (hfQ : cv tr t f fQ = 1)
    {bm : List UInt8} (hbm : ∀ i, i < 5 → (bm.getD i 0).toNat = cv tr t f (q i))
    {p : NearSpecV3.Scheduler.Params} (hbase : cv tr t f base = p.base)
    (hdd : cv tr t f dd = p.maxSingleGrant - p.base) (hb24 : p.base < 2 ^ 24)
    (hD24 : p.maxSingleGrant - p.base < 2 ^ 24) :
    ∀ x, x < 20 →
      cv tr t (f + x) cur = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).1 ∧
      cv tr t (f + x) j = (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).2 := by
  have hR := struct_all hL hf hfQ hbm
  intro x
  induction x with
  | zero =>
    intro _
    obtain ⟨-, -, -, -, hj, hcur, -⟩ := row_start hL hf hfQ
    simp only [Nat.add_zero, Nat.mul_zero]
    exact ⟨hcur.trans hbase, hj⟩
  | succ x ih =>
    intro hx
    obtain ⟨h1, h2⟩ := ih (by omega)
    have := (val_step hL hbase hdd hb24 hD24 (by omega) (hR x (by omega)) h1 h2).2.2.2.2.1
      (by omega)
    rw [show f + (x + 1) = f + x + 1 by omega, show 2 * (x + 1) = 2 * x + 2 by omega]
    exact this

/-! ## Messages -/

theorem eval_ofNat {e : Expr} {w v : Nat} (h : zev (tenv tr t w pub) e = (v : Int)) :
    e.eval tr t w pub = Fp.ofNat v := by
  rw [eval_eq, h, intCast_ofNat]

theorem mult_one {i : Interaction} {x w : Nat} (hm : i.mult = [c x])
    (h : i.multNat tr t w pub ≠ 0) : cv tr t w x = 1 := by
  unfold Interaction.multNat at h
  rw [hm] at h
  simp only [Interaction.multNat.go] at h
  split at h
  · next he =>
    have e : (c x).eval tr t w pub = tr.cell t w x := rfl
    unfold cv; rw [← e, he]; decide
  · simp at h

theorem inc0_def : interactions[2]! = Interaction.mk B_SINC [c us0]
      [c tau, eE, sub val0 (c cur), sub (sub (c m) (c j)) (k 1), c s, c r, c link] true := rfl

theorem inc1_def : interactions[3]! = Interaction.mk B_SINC [c us1]
      [c tau, .add eE (c b0), sub val1 (c cm), sub (sub (sub (c m) (c j)) (c b0)) (k 1),
        c s, c r, c link] true := rfl

theorem push_def : interactions[4]! = Interaction.mk B_SPUSH [c re]
      [c tau, c key, c zk0, c cid, smul 64 (c cid)] true := rfl

theorem read_def : interactions[5]! = Interaction.mk B_SOP [c re]
      [aL, .add (c cid) (k 1), k OP_READ, c key, c key, k 0, k 0, k 0] true := rfl

/-- The scan table's interactions on `SINC`, `SPUSH`, `SOP` are entries 2, 3 / 4 / 5. -/
theorem bus_cases : ∀ i ∈ interactions,
    (i.bus = B_SINC → i = interactions[2]! ∨ i = interactions[3]!) ∧
      (i.bus = B_SPUSH → i = interactions[4]!) ∧ (i.bus = B_SOP → i = interactions[5]!) := by
  decide

/-- The `INC` message of increase index `jj` of a request. -/
def incMsg (τ cid s r link : Nat) (incs : List Nat) (jj : Nat) : List Fp :=
  [τ, 64 * cid + jj, incs.getD jj 0, incs.length - jj - 1, s, r, link].map Fp.ofNat

/-- **Request contract.** -/
theorem scan_request (hL : SLocal tr t pub) {f : Nat} (hf : f < tr.height t)
    (hfQ : cv tr t f fQ = 1)
    {bm : List UInt8} (hbm : ∀ i, i < 5 → (bm.getD i 0).toNat = cv tr t f (q i))
    {p : NearSpecV3.Scheduler.Params} (hbase : cv tr t f base = p.base)
    (hdd : cv tr t f dd = p.maxSingleGrant - p.base) (hb24 : p.base < 2 ^ 24)
    (hD24 : p.maxSingleGrant - p.base < 2 ^ 24) :
    -- the block
    (∀ x, x < 20 → f + x < tr.height t ∧ cv tr t (f + x) kS = 1 ∧
      cv tr t (f + x) re = (if x = 19 then 1 else 0)) ∧
    -- the number of increases
    cv tr t f m = (incsOf p bm).length ∧
    -- INC: slot kk of row f + x
    (∀ x, x < 20 → ∀ kk, kk < 2 → (interactions[2 + kk]!).multNat tr t (f + x) pub ≠ 0 →
      NearSpecV3.Scheduler.getBit bm (2 * x + kk) = true ∧
      (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + kk)).2 < (incsOf p bm).length ∧
      (interactions[2 + kk]!).msgVal tr t (f + x) pub =
        incMsg (cv tr t f tau) (cv tr t f cid) (cv tr t f s) (cv tr t f r) (cv tr t f link) (incsOf p bm)
          (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + kk)).2) ∧
    -- PUSH / READ only at the end row
    (∀ x, x < 20 → ∀ kk, kk < 2 → (interactions[4 + kk]!).multNat tr t (f + x) pub ≠ 0 → x = 19) ∧
    (interactions[4]!).msgVal tr t (f + 19) pub =
      [cv tr t f tau, cv tr t f key, (if cv tr t f key = 0 then 1 else 0), cv tr t f cid,
        64 * cv tr t f cid].map Fp.ofNat ∧
    (interactions[5]!).msgVal tr t (f + 19) pub =
      [addrOf (cv tr t f tau) 0 (cv tr t f link), cv tr t f cid + 1, OP_READ, cv tr t f key,
        cv tr t f key, 0, 0, 0].map Fp.ofNat := by
  have hR := struct_all hL hf hfQ hbm
  have hV := vals_all hL hf hfQ hbm hbase hdd hb24 hD24
  have hlen := incsOf_length_stAt p bm
  -- m
  have hm : cv tr t f m = (incsOf p bm).length := by
    obtain ⟨h1, h2⟩ := hV 19 (by omega)
    have := (val_step hL hbase hdd hb24 hD24 (by omega) (hR 19 (by omega)) h1 h2).2.2.2.2.2 rfl
    rw [hlen, ← this, (hR 19 (by omega)).2.2.2.1 m (by simp [reqCols])]
  refine ⟨fun x hx => ⟨(hR x hx).1, (hR x hx).2.1, (hR x hx).2.2.1⟩, hm, ?_, ?_, ?_, ?_⟩
  · intro x hx kk hkk hmult
    obtain ⟨hlt, hk, hre, hc, hpos, hg0, hg1⟩ := hR x hx
    obtain ⟨hcur, hj⟩ := hV x hx
    obtain ⟨s1a, s1b, hv0, hv1, -, -⟩ := val_step hL hbase hdd hb24 hD24 hx (hR x hx) hcur hj
    have F := row_flags hL hlt
    have cc := fun col (h : col ∈ reqCols) => hc col h
    have lt := fun col => cv_lt (tr := tr) (t := t) (f + x) col
    have hmx : cv tr t (f + x) m = (incsOf p bm).length := by rw [cc m (by simp [reqCols]), hm]
    rcases (by omega : kk = 0 ∨ kk = 1) with h | h <;> subst h
    · rw [Nat.add_zero] at hmult ⊢
      have hu : cv tr t (f + x) us0 = 1 := mult_one (by rfl) hmult
      have hb : cv tr t (f + x) b0 = 1 := by have := F.2.2.2.2.1; have := bool_of hL hlt (x := b0) (by simp [boolCols]); omega
      have hgb := hg0.2 hb
      have hjlt := stAt_snd_lt (NearSpecV3.Scheduler.requestValues p) bm p.base
        (show 2 * x < 40 by omega) hgb
      rw [← hlen] at hjlt
      refine ⟨hgb, hjlt, ?_⟩
      have hle := stAt_fst_le p bm (2 * x) (2 * x) (Nat.le_refl _) (by omega)
      have hinc := incsOf_getD p bm (show 2 * x < 40 by omega) hgb
      have hv := hv0 hb
      have e1 : (c tau).eval tr t (f + x) pub = Fp.ofNat (cv tr t f tau) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc tau (by simp [reqCols])])
      have e2 : eE.eval tr t (f + x) pub = Fp.ofNat (64 * cv tr t f cid +
          (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).2) :=
        eval_ofNat (by simp only [eE, zev_add, zev_smul, zev_c, cur_cv]; rw [cc cid (by simp [reqCols]), hj]; omega)
      have e3 : (sub val0 (c cur)).eval tr t (f + x) pub = Fp.ofNat
          ((incsOf p bm).getD (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).2 0) :=
        eval_ofNat (by simp only [val0, zev_sub, zev_add, zev_c, cur_cv]; rw [hinc, hcur]; omega)
      have e4' : (sub (sub (c m) (c j)) (k 1)).eval tr t (f + x) pub = Fp.ofNat ((incsOf p bm).length -
            (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x)).2 - 1) :=
        eval_ofNat (by simp only [zev_sub, zev_c, zev_k, cur_cv]; rw [hmx, hj]; omega)
      have e5 : (c s).eval tr t (f + x) pub = Fp.ofNat (cv tr t f s) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc s (by simp [reqCols])])
      have e6 : (c r).eval tr t (f + x) pub = Fp.ofNat (cv tr t f r) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc r (by simp [reqCols])])
      have e7 : (c link).eval tr t (f + x) pub = Fp.ofNat (cv tr t f link) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc link (by simp [reqCols])])
      rw [inc0_def]
      simp only [Interaction.msgVal, incMsg, List.map_cons, List.map_nil, e1, e2, e3, e4', e5, e6, e7]
    · rw [show 2 + 1 = 3 from rfl] at hmult ⊢
      have hu : cv tr t (f + x) us1 = 1 := mult_one (by rfl) hmult
      have hb : cv tr t (f + x) b1 = 1 := by have := F.2.2.2.2.2.1; have := bool_of hL hlt (x := b1) (by simp [boolCols]); omega
      have hgb := hg1.2 hb
      have hjlt := stAt_snd_lt (NearSpecV3.Scheduler.requestValues p) bm p.base
        (show 2 * x + 1 < 40 by omega) hgb
      rw [← hlen] at hjlt
      refine ⟨hgb, hjlt, ?_⟩
      have hle := stAt_fst_le p bm (2 * x + 1) (2 * x + 1) (Nat.le_refl _) (by omega)
      have hinc := incsOf_getD p bm (show 2 * x + 1 < 40 by omega) hgb
      have hv := hv1 hb
      have e1 : (c tau).eval tr t (f + x) pub = Fp.ofNat (cv tr t f tau) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc tau (by simp [reqCols])])
      have e2 : (Expr.add eE (c b0)).eval tr t (f + x) pub = Fp.ofNat (64 * cv tr t f cid +
          (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).2) :=
        eval_ofNat (by simp only [eE, zev_add, zev_smul, zev_c, cur_cv]; rw [cc cid (by simp [reqCols]), ← s1b]; omega)
      have e3 : (sub val1 (c cm)).eval tr t (f + x) pub = Fp.ofNat
          ((incsOf p bm).getD (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).2 0) :=
        eval_ofNat (by simp only [val1, zev_sub, zev_add, zev_c, cur_cv]; rw [hinc, s1a]; omega)
      have e4' : (sub (sub (sub (c m) (c j)) (c b0)) (k 1)).eval tr t (f + x) pub = Fp.ofNat
          ((incsOf p bm).length - (stAt (NearSpecV3.Scheduler.requestValues p) bm p.base (2 * x + 1)).2 - 1) :=
        eval_ofNat (by simp only [zev_sub, zev_c, zev_k, cur_cv]; rw [hmx, ← s1b]; omega)
      have e5 : (c s).eval tr t (f + x) pub = Fp.ofNat (cv tr t f s) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc s (by simp [reqCols])])
      have e6 : (c r).eval tr t (f + x) pub = Fp.ofNat (cv tr t f r) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc r (by simp [reqCols])])
      have e7 : (c link).eval tr t (f + x) pub = Fp.ofNat (cv tr t f link) :=
        eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc link (by simp [reqCols])])
      rw [inc1_def]
      simp only [Interaction.msgVal, incMsg, List.map_cons, List.map_nil, e1, e2, e3, e4', e5, e6, e7]
  · intro x hx kk hkk hmult
    have hre : cv tr t (f + x) re = 1 := by
      rcases (by omega : kk = 0 ∨ kk = 1) with h | h <;> subst h
      · exact mult_one (by rfl) hmult
      · exact mult_one (by rfl) hmult
    have := (hR x hx).2.2.1
    rw [hre] at this
    by_cases h : x = 19
    · exact h
    · rw [if_neg h] at this; omega
  · obtain ⟨hlt, hk, -, hc, -⟩ := hR 19 (by omega)
    have cc := fun col (h : col ∈ reqCols) => hc col h
    have hzk := (row_cur hL hlt hk).2.2.2.2.2.2
    have e1 : (c tau).eval tr t (f + 19) pub = Fp.ofNat (cv tr t f tau) :=
      eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc tau (by simp [reqCols])])
    have e2 : (c key).eval tr t (f + 19) pub = Fp.ofNat (cv tr t f key) :=
      eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc key (by simp [reqCols])])
    have e3 : (c zk0).eval tr t (f + 19) pub = Fp.ofNat (if cv tr t f key = 0 then 1 else 0) :=
      eval_ofNat (by simp only [zev_c, cur_cv]; rw [hzk, cc key (by simp [reqCols])])
    have e4' : (c cid).eval tr t (f + 19) pub = Fp.ofNat (cv tr t f cid) :=
      eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc cid (by simp [reqCols])])
    have e5 : (smul 64 (c cid)).eval tr t (f + 19) pub = Fp.ofNat (64 * cv tr t f cid) :=
      eval_ofNat (by simp only [zev_smul, zev_c, cur_cv]; rw [cc cid (by simp [reqCols])]; omega)
    rw [push_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, e1, e2, e3, e4', e5]
  · obtain ⟨hlt, hk, -, hc, -⟩ := hR 19 (by omega)
    have cc := fun col (h : col ∈ reqCols) => hc col h
    have e1 : aL.eval tr t (f + 19) pub = Fp.ofNat (addrOf (cv tr t f tau) 0 (cv tr t f link)) :=
      eval_ofNat (by
        simp only [aL, zev_add, zev_smul, zev_c, cur_cv]
        rw [cc tau (by simp [reqCols]), cc link (by simp [reqCols])]; simp only [addrOf]; omega)
    have e2 : (Expr.add (c cid) (k 1)).eval tr t (f + 19) pub = Fp.ofNat (cv tr t f cid + 1) :=
      eval_ofNat (by simp only [zev_add, zev_c, zev_k, cur_cv]; rw [cc cid (by simp [reqCols])]; omega)
    have e3 : (k OP_READ).eval tr t (f + 19) pub = Fp.ofNat OP_READ := eval_ofNat (zev_k _ _)
    have e4' : (c key).eval tr t (f + 19) pub = Fp.ofNat (cv tr t f key) :=
      eval_ofNat (by simp only [zev_c, cur_cv]; rw [cc key (by simp [reqCols])])
    have e5 : (k 0).eval tr t (f + 19) pub = Fp.ofNat 0 := eval_ofNat (zev_k _ _)
    rw [read_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, e1, e2, e3, e4', e5]

end

end ZkFormal.NearV3.Sched.Scan

import ZkFormal.Near.Render.Statements
import ZkFormal.Near.Extract.Eval
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Render.Proof.Base — the honest trace, cell by cell

`render c e` reads table `t ∈ 1…6` from the bundle's row arrays; heights
`clog2` of their sizes.  Tables built by `mkTab H W f` read `f r col`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- Rows `t − 1` of the six NEAR tables (`1 node … 6 sort`). -/
def partOf (B : Bundle) : Nat → Array Row
  | 1 => B.node | 2 => B.walk | 3 => B.rcpt | 4 => B.acct | 5 => B.mrk | 6 => B.sort
  | _ => #[]

theorem render_log (c : Claim) (e : Ext) {t : Nat} (h0 : t ≠ 0) (h7 : t < 7) :
    (render c e).log t = clog2 (partOf (bundle c e) t).size := by
  match t, h0, h7 with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ =>
    simp [render, renderParts, partOf]

theorem getD_map_ofNat (A : Array Row) (r col : Nat) :
    ((Option.map (fun x => Array.map Fp.ofNat x) A[r]?).getD #[])[col]?.getD 0 =
      Fp.ofNat ((A[r]?.getD #[])[col]?.getD 0) := by
  cases A[r]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
    cases row[col]? <;> rfl

theorem render_cell (c : Claim) (e : Ext) {t : Nat} (h0 : t ≠ 0) (h7 : t < 7) (r col : Nat) :
    (render c e).cell t r col = Fp.ofNat (((partOf (bundle c e) t).getD r #[]).getD col 0) := by
  match t, h0, h7 with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _ =>
    simp [render, renderParts, partOf, getD_map_ofNat]

/-! ## `clog2`, `logOf` -/

theorem clog2_go_pow (k : Nat) : ∀ f a, a ≤ k → k < a + f → clog2.go (2 ^ k) f a = k := by
  intro f
  induction f with
  | zero => intro a h1 h2; omega
  | succ f ih =>
    intro a h1 h2
    simp only [clog2.go]
    by_cases h : a = k
    · subst h; simp
    · have : ¬ 2 ^ k ≤ 2 ^ a := by
        rw [Nat.not_le]; exact Nat.pow_lt_pow_right (by omega) (by omega)
      rw [if_neg this]; exact ih (a + 1) (by omega) (by omega)

theorem clog2_pow (k : Nat) : clog2 (2 ^ k) = k :=
  clog2_go_pow k _ 0 (Nat.zero_le _) (by simpa using Nat.lt_two_pow_self)

theorem clog2_go_le {m k : Nat} (hm : m ≤ 2 ^ k) : ∀ f a, a ≤ k → clog2.go m f a ≤ k := by
  intro f
  induction f with
  | zero => intro a h; simpa [clog2.go] using h
  | succ f ih =>
    intro a h
    simp only [clog2.go]
    split
    · exact h
    · rename_i hn
      by_cases ha : a = k
      · subst ha; exact absurd hm hn
      · exact ih (a + 1) (by omega)

theorem clog2_le {m k : Nat} (hm : m ≤ 2 ^ k) : clog2 m ≤ k := clog2_go_le hm _ 0 (Nat.zero_le _)

theorem logOf_le {m k : Nat} (hk : 1 ≤ k) (hm : m ≤ 2 ^ k) : logOf m ≤ k := by
  have := clog2_le hm; simp only [logOf]; omega

theorem one_le_logOf (m : Nat) : 1 ≤ logOf m := by simp only [logOf]; omega

theorem clog2_go_ge {m : Nat} : ∀ f a, m ≤ 2 ^ (a + f) → m ≤ 2 ^ clog2.go m f a := by
  intro f
  induction f with
  | zero => intro a h; simpa [clog2.go] using h
  | succ f ih =>
    intro a h
    simp only [clog2.go]
    split
    · assumption
    · exact ih (a + 1) (by rw [show a + 1 + f = a + (f + 1) by omega]; exact h)

theorem le_pow_logOf (m : Nat) : m ≤ 2 ^ logOf m := by
  have h1 : m ≤ 2 ^ clog2 m := clog2_go_ge m 0 (by simpa using Nat.le_of_lt Nat.lt_two_pow_self)
  have h2 : 2 ^ clog2 m ≤ 2 ^ logOf m := Nat.pow_le_pow_right (by omega) (by simp only [logOf]; omega)
  omega

/-! ## `mkTab` -/

theorem mkTab_size (H W : Nat) (f : Nat → Nat → Nat) : (mkTab H W f).size = H := by
  simp [mkTab]

theorem mkTab_get {H W : Nat} {f : Nat → Nat → Nat} {q col : Nat} (hq : q < H) (hc : col < W) :
    ((mkTab H W f).getD q #[]).getD col 0 = f q col := by
  simp [mkTab, hq, hc, Array.getD_eq_getD_getElem?]

/-- A table of `render` built by `mkTab (2^L) W f`. -/
theorem render_mkTab {c : Claim} {e : Ext} {t L W : Nat} {f : Nat → Nat → Nat} (h0 : t ≠ 0) (h7 : t < 7)
    (hp : partOf (bundle c e) t = mkTab (2 ^ L) W f) :
    (render c e).log t = L ∧ (render c e).height t = 2 ^ L ∧
    ∀ q col, q < 2 ^ L → col < W → (render c e).cell t q col = Fp.ofNat (f q col) := by
  have hl : (render c e).log t = L := by rw [render_log c e h0 h7, hp, mkTab_size, clog2_pow]
  refine ⟨hl, by simp [Trace.height, hl], fun q col hq hc => ?_⟩
  rw [render_cell c e h0 h7, hp, mkTab_get hq hc]

end ZkFormal.Near.Render

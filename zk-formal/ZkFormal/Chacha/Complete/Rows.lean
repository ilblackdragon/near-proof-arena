import ZkFormal.Chacha.Complete.Basic

/-!
# ZkFormal.Chacha.Complete.Rows — the row structure of the honest trace

* `honestLog` bounds (`log_bounds`, `len_le_height`);
* `rowAt_blk`: row `r < 86·n` is row `r % 86` of the block of request `r / 86`;
* `step_at`: on every row `r < H`, (row `r`, row `(r+1) % H`) is a legal `Step`;
* `row0_ok`: row 0 is `I0` or padding.
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Gen

/-! ## Height -/

theorem clog2_go_ge (n : Nat) : ∀ fuel acc, n ≤ 2 ^ (acc + fuel) → n ≤ 2 ^ clog2.go n fuel acc
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · assumption
    · exact clog2_go_ge n fuel (acc + 1) (by rw [show acc + 1 + fuel = acc + (fuel + 1) by omega]; exact h)

theorem clog2_go_le (n m : Nat) (hm : n ≤ 2 ^ m) : ∀ fuel acc, acc ≤ m → clog2.go n fuel acc ≤ m
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · exact h
    · next hn =>
      apply clog2_go_le n m hm fuel (acc + 1)
      have : acc ≠ m := fun e => hn (e ▸ hm)
      omega

theorem clog2_ge (n : Nat) : n ≤ 2 ^ clog2 n :=
  clog2_go_ge n n 0 (by simpa using Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))

theorem clog2_le (n m : Nat) (hm : n ≤ 2 ^ m) : clog2 n ≤ m :=
  clog2_go_le n m hm n 0 (Nat.zero_le _)

theorem height_eq (reqs : List Req) (t : Nat) : (honestTrace reqs).height t = 2 ^ honestLog reqs := rfl

theorem len_le_height (reqs : List Req) (t : Nat) : 86 * reqs.length ≤ (honestTrace reqs).height t := by
  rw [height_eq]
  exact Nat.le_trans (clog2_ge _) (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem log_bounds (reqs : List Req) (hrows : 86 * reqs.length ≤ 2 ^ Table.maxLog) (t : Nat) :
    1 ≤ (honestTrace reqs).log t ∧ (honestTrace reqs).log t ≤ Table.maxLog := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  show max 1 (clog2 (86 * reqs.length)) ≤ Table.maxLog
  have := clog2_le _ _ hrows
  have : 1 ≤ Table.maxLog := by decide
  omega

/-! ## Rows as indexed blocks -/

/-- A default request (never used on rows `< 86·n`). -/
def dReq : Req := ⟨[], 0, []⟩

/-- Row `r` of the honest table. -/
def rowAt (reqs : List Req) (r : Nat) : Row := (honestRows reqs).getD r .pad

theorem honestCell_eq (reqs : List Req) (r c : Nat) : honestCell reqs r c = rowCell (rowAt reqs r) c := rfl

theorem blockRows_length (R : Req) : (blockRows R).length = 86 := by simp [blockRows]

theorem honestRows_length (reqs : List Req) : (honestRows reqs).length = 86 * reqs.length := by
  induction reqs with
  | nil => rfl
  | cons R rest ih =>
    show (blockRows R ++ honestRows rest).length = _
    rw [List.length_append, blockRows_length, ih, List.length_cons]; omega

theorem rowAt_blk (reqs : List Req) (r : Nat) (hr : r < 86 * reqs.length) :
    rowAt reqs r = posRow (reqs.getD (r / 86) dReq) (r % 86) := by
  induction reqs generalizing r with
  | nil => simp at hr
  | cons R rest ih =>
    unfold rowAt
    show (blockRows R ++ honestRows rest).getD r .pad = _
    rw [List.getD_eq_getElem?_getD]
    by_cases h86 : r < 86
    · rw [List.getElem?_append_left (by rw [blockRows_length]; exact h86)]
      simp [blockRows, h86, Nat.div_eq_of_lt h86, Nat.mod_eq_of_lt h86]
    · rw [List.getElem?_append_right (by rw [blockRows_length]; omega), blockRows_length]
      have := ih (r - 86) (by simp at hr; omega)
      unfold rowAt at this
      rw [List.getD_eq_getElem?_getD] at this
      rw [this, show r / 86 = (r - 86) / 86 + 1 by omega, show r % 86 = (r - 86) % 86 by omega]
      simp

theorem rowAt_pad (reqs : List Req) (r : Nat) (hr : 86 * reqs.length ≤ r) : rowAt reqs r = .pad := by
  unfold rowAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [honestRows_length]; exact hr)]
  rfl

theorem getD_mem (reqs : List Req) (i : Nat) (hi : i < reqs.length) : reqs.getD i dReq ∈ reqs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

/-! ## Transitions -/

theorem posRow_q (R : Req) {m : Nat} (h1 : 2 ≤ m) (h2 : m < 82) :
    posRow R m = .q R ((m - 2) / 8) ((m - 2) % 8) := by
  unfold posRow; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem posRow_f (R : Req) {m : Nat} (h1 : 82 ≤ m) : posRow R m = .f R (m - 82) := by
  unfold posRow; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem posStep (R : Req) (hR : ReqOk R) (m : Nat) (hm : m < 85) : Step (posRow R m) (posRow R (m + 1)) := by
  by_cases h0 : m = 0
  · subst h0; exact Step.i0 R hR
  by_cases h1 : m = 1
  · subst h1; rw [posRow_q R (m := 2) (by decide) (by decide)]; exact Step.i1 R hR
  by_cases hq : m < 81
  · rw [posRow_q R (by omega) (by omega), posRow_q R (by omega) (by omega)]
    by_cases h7 : (m - 2) % 8 < 7
    · rw [show (m + 1 - 2) / 8 = (m - 2) / 8 by omega, show (m + 1 - 2) % 8 = (m - 2) % 8 + 1 by omega]
      exact Step.qp R hR _ _ (by omega) h7
    · rw [show (m + 1 - 2) / 8 = (m - 2) / 8 + 1 by omega, show (m + 1 - 2) % 8 = 0 by omega,
        show (m - 2) % 8 = 7 by omega]
      exact Step.qd R hR _ (by omega)
  by_cases h81 : m = 81
  · subst h81
    rw [posRow_q R (m := 81) (by decide) (by decide), posRow_f R (m := 82) (by decide)]
    exact Step.qf R hR
  rw [posRow_f R (by omega), posRow_f R (by omega), show m + 1 - 82 = m - 82 + 1 by omega]
  exact Step.ff R hR _ (by omega)

theorem row0_cases (reqs : List Req) : rowAt reqs 0 = .pad ∨ ∃ R, rowAt reqs 0 = .i0 R := by
  cases reqs with
  | nil => left; rfl
  | cons R rest =>
    right; refine ⟨R, ?_⟩
    rw [rowAt_blk _ 0 (by simp)]; rfl

theorem row0_ok (reqs : List Req) : FirstOk (rowAt reqs 0) := row0_cases reqs

/-- **The transition structure**: every row and its cyclic successor form a `Step`. -/
theorem step_at (reqs : List Req) (hok : ∀ R ∈ reqs, ReqOk R) (t r : Nat)
    (hr : r < (honestTrace reqs).height t) :
    Step (rowAt reqs r) (rowAt reqs ((r + 1) % (honestTrace reqs).height t)) := by
  have hlen := len_le_height reqs t
  generalize (honestTrace reqs).height t = H at hr hlen
  have hnext : 86 * reqs.length ≤ r + 1 →
      (rowAt reqs ((r + 1) % H) = .pad ∨ ∃ R', rowAt reqs ((r + 1) % H) = .i0 R') := by
    intro h
    by_cases h2 : r + 1 < H
    · left; rw [Nat.mod_eq_of_lt h2]; exact rowAt_pad _ _ h
    · rw [show r + 1 = H by omega, Nat.mod_self]; exact row0_cases reqs
  by_cases hin : r < 86 * reqs.length
  · have hR := hok _ (getD_mem reqs (r / 86) (by omega))
    rw [rowAt_blk reqs r hin]
    by_cases hm : r % 86 < 85
    · rw [Nat.mod_eq_of_lt (show r + 1 < H by omega), rowAt_blk reqs (r + 1) (by omega),
        show (r + 1) / 86 = r / 86 by omega, show (r + 1) % 86 = r % 86 + 1 by omega]
      exact posStep _ hR _ hm
    · rw [show r % 86 = 85 by omega]
      apply Step.fe _ hR
      by_cases hl : r + 1 < 86 * reqs.length
      · right; refine ⟨reqs.getD ((r + 1) / 86) dReq, ?_⟩
        rw [Nat.mod_eq_of_lt (show r + 1 < H by omega), rowAt_blk reqs (r + 1) hl, show (r + 1) % 86 = 0 by omega]
        rfl
      · exact hnext (by omega)
  · rw [rowAt_pad reqs r (by omega)]
    exact Step.pd _ (hnext (by omega))

end ZkFormal.Chacha.Complete

import ZkFormal.Chacha.Complete.Basic

/-!
# ZkFormal.Chacha.Complete.QR — quarter-round rows of the honest trace

On a row `Q dr p` of request `R` (state `s = stBefore (init R) (8·dr + p)`, slots `grp p`):
the twelve inner constraints `qrC` hold (`q_qrC`), and the next row's state is
`qrStep p s`, i.e. the `newS` expressions (`q_copyS`).
-/

namespace ZkFormal.Chacha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table ZkFormal.Chacha.Gen
open NearSpecV3

section
variable {Z : ZEnv} {R : Req} {dr p : Nat} {Y : Row} (h : HEnv Z (.q R dr p) Y) (hR : ReqOk R)
  (hp : p < 8)

theorem kflag_qP (x : Nat) (hx : x < 8) : kflag (Row.q R dr p).kd (2 + x) = if x = p then 1 else 0 := by
  show (if 2 + x = 2 + p then 1 else if 14 ≤ 2 + x ∧ 2 + x < 18 then bt dr (2 + x - 14) else 0) = _
  by_cases e : x = p
  · simp [e]
  · rw [if_neg (by omega), if_neg (by omega), if_neg e]

include h hp in
theorem q_selP (f : Nat → Expr) : zev Z (E.sel colP 8 f) = zev Z (f p) :=
  zev_sel Z colP 8 f p hp (by rw [zP h hp, kflag_qP (R := R) p hp, if_pos rfl])
    (fun x hx hxp => by rw [zP h hx, kflag_qP (R := R) x hx, if_neg hxp])

include h hp in
theorem q_gCopy : zev Z gCopy = 0 := by
  simp only [gCopy, zev_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zev_c,
    zI0 h, zI1 h, zF h (show 0 < 4 by decide), zF h (show 1 < 4 by decide),
    zF h (show 2 < 4 by decide)]
  simp only [Row.kd, kflag, if_neg (show ¬ (0 = 2 + p) by omega), if_neg (show ¬ (1 = 2 + p) by omega),
    if_neg (show ¬ (10 = 2 + p) by omega), if_neg (show ¬ (11 = 2 + p) by omega),
    if_neg (show ¬ (12 = 2 + p) by omega), if_neg (show ¬ (14 ≤ 0 ∧ 0 < 18) by omega),
    if_neg (show ¬ (14 ≤ 1 ∧ 1 < 18) by omega), if_neg (show ¬ (14 ≤ 10 ∧ 10 < 18) by omega),
    if_neg (show ¬ (14 ≤ 11 ∧ 11 < 18) by omega), if_neg (show ¬ (14 ≤ 12 ∧ 12 < 18) by omega)]
  rfl

/-- The words of the row. -/
abbrev wq (R : Req) (dr p : Nat) : QW := qwOf R dr p

include hR in
theorem q_slots_lt :
    (qState R dr p)[(grp p).1]! < 2 ^ 32 ∧ (qState R dr p)[(grp p).2.1]! < 2 ^ 32 ∧
    (qState R dr p)[(grp p).2.2.1]! < 2 ^ 32 ∧ (qState R dr p)[(grp p).2.2.2]! < 2 ^ 32 :=
  ⟨st_lt hR _ _, st_lt hR _ _, st_lt hR _ _, st_lt hR _ _⟩

include hR in
theorem q_words_lt :
    (wq R dr p).a < 2 ^ 32 ∧ (wq R dr p).b < 2 ^ 32 ∧ (wq R dr p).c < 2 ^ 32 ∧ (wq R dr p).d < 2 ^ 32 ∧
    (wq R dr p).a1 < 2 ^ 32 ∧ (wq R dr p).d1 < 2 ^ 32 ∧ (wq R dr p).c1 < 2 ^ 32 ∧
    (wq R dr p).b1 < 2 ^ 32 ∧ (wq R dr p).a2 < 2 ^ 32 ∧ (wq R dr p).d2 < 2 ^ 32 ∧
    (wq R dr p).c2 < 2 ^ 32 ∧ (wq R dr p).b2 < 2 ^ 32 := by
  obtain ⟨ha, hb, hc, hd⟩ := q_slots_lt hR (dr := dr) (p := p)
  have := qw_lt ha hb hc hd
  exact ⟨ha, hb, hc, hd, this⟩

include h in
theorem q_bitsX : BitsOf Z (xb 0) (wq R dr p).b ∧ BitsOf Z (xb 1) (wq R dr p).d ∧
    BitsOf Z (xb 2) (wq R dr p).a1 ∧ BitsOf Z (xb 3) (wq R dr p).c1 ∧
    BitsOf Z (xb 4) (wq R dr p).a2 ∧ BitsOf Z (xb 5) (wq R dr p).c2 :=
  ⟨bitsX h (m := 0) (by decide), bitsX h (m := 1) (by decide), bitsX h (m := 2) (by decide),
   bitsX h (m := 3) (by decide), bitsX h (m := 4) (by decide), bitsX h (m := 5) (by decide)⟩

include h hR in
theorem q_bitsD1 : BitsOf Z d1 (wq R dr p).d1 := by
  obtain ⟨-, -, -, hd, ha1, -⟩ := q_words_lt hR (dr := dr) (p := p)
  obtain ⟨-, b1, b2, -⟩ := q_bitsX h
  exact bitsOf_rx b1 b2 hd ha1 (by decide) (by decide)

include h hR in
theorem q_bitsB1 : BitsOf Z b1 (wq R dr p).b1 := by
  obtain ⟨-, hb, -, -, -, -, hc1, -⟩ := q_words_lt hR (dr := dr) (p := p)
  obtain ⟨b0, -, -, b3, -⟩ := q_bitsX h
  exact bitsOf_rx b0 b3 hb hc1 (by decide) (by decide)

include h hR in
theorem q_bitsD2 : BitsOf Z d2 (wq R dr p).d2 := by
  obtain ⟨-, -, -, -, -, hd1, -, -, ha2, -⟩ := q_words_lt hR (dr := dr) (p := p)
  obtain ⟨-, -, -, -, b4, -⟩ := q_bitsX h
  exact bitsOf_rx (q_bitsD1 h hR) b4 hd1 ha2 (by decide) (by decide)

include h hR in
theorem q_bitsB2 : BitsOf Z b2 (wq R dr p).b2 := by
  obtain ⟨-, -, -, -, -, -, -, hb1, -, -, hc2, -⟩ := q_words_lt hR (dr := dr) (p := p)
  obtain ⟨-, -, -, -, -, b5⟩ := q_bitsX h
  exact bitsOf_rx (q_bitsB1 h hR) b5 hb1 hc2 (by decide) (by decide)

include h hR hp in
/-- **The inner quarter-round constraints** on a `Q` row. -/
theorem q_qrC {q : Nat} (hq : q < 12) : zev Z (qrC (grp p) q) = 0 := by
  obtain ⟨g1, g2, g3, g4, -⟩ := Sound.grp_facts hp
  obtain ⟨ha, hb, hc, hd, ha1, hd1, hc1, hb1, ha2, hd2, hc2, -⟩ := q_words_lt hR (dr := dr) (p := p)
  obtain ⟨x0, x1, x2, x3, x4, x5⟩ := q_bitsX h
  obtain ⟨k, l, hk, hl, rfl⟩ : ∃ k l, k < 6 ∧ l < 2 ∧ q = 2 * k + l :=
    ⟨q / 2, q % 2, by omega, by omega, by omega⟩
  have e2 : ∀ k, (2 * k + l) / 2 = k := fun k => by omega
  have e3 : ∀ k, (2 * k + l) % 2 = l := fun k => by omega
  have hS : ∀ i, i < 16 → zev Z (sC i l) = (limbN (qState R dr p)[i]! l : Int) :=
    fun i hi => zS h hi hl
  have hci : ∀ q', q' < 4 → zev Z (cin q' l) = if l = 0 then 0 else (cCell (.q R dr p) q' 0 : Int) :=
    fun q' hq' => zcin h hq' hl
  have L := fun {f : Nat → Expr} {w : Nat} (hw : BitsOf Z f w) => zev_limb hw hl
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [qrC, e2, e3, zev_sub, L x0, hS _ g2]; exact Int.sub_self _
  · simp only [qrC, e2, e3, zev_sub, L x1, hS _ g4]; exact Int.sub_self _
  · have := add_carry ha hb hl
    simp only [qrC, e2, e3, zev_addE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      L x0, L x2, hS _ g1, hci 0 (by decide), zC h (show 0 < 4 by decide) hl]
    simp only [wq, qwOf, qw, cCell, limbN] at this ⊢
    omega
  · have := add_carry hc hd1 hl
    simp only [qrC, e2, e3, zev_addE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      L x3, L (q_bitsD1 h hR), hS _ g3, hci 1 (by decide), zC h (show 1 < 4 by decide) hl]
    simp only [wq, qwOf, qw, cCell, limbN] at this ⊢
    omega
  · have := add_carry ha1 hb1 hl
    simp only [qrC, e2, e3, zev_addE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      L x2, L x4, L (q_bitsB1 h hR), hci 2 (by decide), zC h (show 2 < 4 by decide) hl]
    simp only [wq, qwOf, qw, cCell, limbN] at this ⊢
    omega
  · have := add_carry hc1 hd2 hl
    simp only [qrC, e2, e3, zev_addE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      L x3, L x5, L (q_bitsD2 h hR), hci 3 (by decide), zC h (show 3 < 4 by decide) hl]
    simp only [wq, qwOf, qw, cCell, limbN] at this ⊢
    omega

include hR hp in
/-- The state after the row's quarter-round. -/
theorem q_next_get (i : Nat) :
    (stBefore (init R) (8 * dr + p + 1))[i]! =
      if i = (grp p).1 then (wq R dr p).a2 else if i = (grp p).2.1 then (wq R dr p).b2
      else if i = (grp p).2.2.1 then (wq R dr p).c2 else if i = (grp p).2.2.2 then (wq R dr p).d2
      else (qState R dr p)[i]! := by
  obtain ⟨g1, g2, g3, g4, h5, h6, h7, h8, h9, h10⟩ := Sound.grp_facts hp
  have hs := st_size hR (8 * dr + p)
  rw [stBefore, show (8 * dr + p) % 8 = p by omega]
  unfold qrStep
  rw [qr_get _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) h5 h6 h7 h8 h9 h10]
  rfl

include h hR hp in
/-- **The state copy** of a `Q` row, given the next row's state. -/
theorem q_copyS (hY : ∀ i, sWord Y i = (stBefore (init R) (8 * dr + p + 1))[i]!) {i l : Nat}
    (hi : i < 16) (hl : l < 2) :
    zev Z (.add (.mul gCopy (E.sub (sN i l) (sC i l)))
      (E.sel colP 8 fun p => E.sub (sN i l) (newS (grp p) i l))) = 0 := by
  rw [zev_add, zev_mul, q_gCopy h hp, Int.zero_mul, Int.zero_add, q_selP h hp, zev_sub,
    zSn h hi hl, hY, q_next_get hR hp]
  obtain ⟨x0, x1, x2, x3, x4, x5⟩ := q_bitsX h
  unfold newS
  split
  · rw [zX h (m := 4) (by decide) hl]; exact Int.sub_self _
  split
  · rw [zev_limb (q_bitsB2 h hR) hl]; exact Int.sub_self _
  split
  · rw [zX h (m := 5) (by decide) hl]; exact Int.sub_self _
  split
  · rw [zev_limb (q_bitsD2 h hR) hl]; exact Int.sub_self _
  · rw [zS h hi hl]; exact Int.sub_self _

end

end ZkFormal.Chacha.Complete

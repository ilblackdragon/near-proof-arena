import ZkFormal.NearV3.Sched.View.Mem
import ZkFormal.NearV3.Sched.Tables.ScanDist

/-!
# ZkFormal.NearV3.Sched.View.Scan — row facts of the scan rows of `ssdV3`

`SLocal` is every scan-family constraint on every row; the merged table `ssdV3` gives it
(`SLocal.of_sd`, `ScanDist.scan_sub`). From `SLocal`: flags are bits,
`act = kP + kS + kSh + kGH + kC`, gates
(`fQ, re, us₀, us₁ ≤ kS`, `us_k ≤ b_k`); the param row; a request-start row (`fQ`); a step inside
a request (`kS = 1, re = 0`: counters advance, request constants carried, the byte register
consumed or rotated, `cur`/`j` updated); the per-row values (`cm`, the quotients `Q₀, Q₁` with
remainders `< 40`, `e4 = [y = 4]`, `re = e4·u₀·u₁`, `m` at the end, `zk0 = [key = 0]`); after a
request end. Value equations are stated over naturals modulo `P` where the cells are arbitrary
field elements; `q_exact` turns the quotient congruence into `Q = D·(pos + 1)/40` under a bound
on `Q`, which the table's bit decompositions give (`q_ranges`: `Q₀, Q₁ < 2^23`).
-/

namespace ZkFormal.NearV3.Sched.Scan

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

abbrev SLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop := Local constraints tr t pub

/-- The merged table's constraints give the scan family's. -/
theorem SLocal.of_sd {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : Local ScanDist.constraints tr t pub) : SLocal tr t pub := ScanDist.local_scan h

/-- Bit position of `b₀` on a row, as a natural. -/
def posv (tr : Trace Fp) (t w : Nat) : Nat := 8 * cv tr t w y + 2 * (cv tr t w u0 + 2 * cv tr t w u1)

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## Membership in the constraint list -/

theorem mem_bool {x : Nat} (hx : x ∈ boolCols) : ZkFormal.Chacha.Table.boolC x ∈ constraints := by
  unfold constraints shared own
  rcases List.mem_append.1 hx with h | h
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h)))
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem h))

theorem mem_rot {i : Nat} (hi : i < 4) :
    mul3 gC be (sub (n (q i)) (c (q (i + 1)))) ∈ constraints := by
  unfold constraints own body
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))))

theorem mem_keep {i : Nat} (hi : i < 4) :
    mul3 gC (notE be) (sub (n (q (i + 1))) (c (q (i + 1)))) ∈ constraints := by
  unfold constraints own body
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))))))

theorem mem_req {x : Nat} (hx : x ∈ reqCols) : Expr.mul gC (sub (n x) (c x)) ∈ constraints := by
  unfold constraints own body
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩))))))

theorem mem_instP {x : Nat} (hx : x ∈ instCols) : Expr.mul (c kP) (sub (n x) (c x)) ∈ constraints := by
  unfold constraints own body
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩))))))))))

theorem mem_instE {x : Nat} (hx : x ∈ instCols) :
    Expr.mul (.mul (c re) (n fQ)) (sub (n x) (c x)) ∈ constraints := by
  unfold constraints own body
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩))))

theorem mem_common {e : Expr} (he : e ∈ Dist.cCommon) : e ∈ constraints := by
  unfold constraints shared
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he))

/-! ## Flags -/

theorem bool_of (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) {x : Nat}
    (hx : x ∈ boolCols) : cv tr t w x ≤ 1 :=
  hL.bool hw (mem_bool hx)

/-- A gate `a·(1 − b)` between bits gives `a ≤ b`. -/
theorem le_of_gate (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) {a b : Nat}
    (he : Expr.mul (c a) (notE (c b)) ∈ constraints) (ha : a ∈ boolCols) (hb : b ∈ boolCols) :
    cv tr t w a ≤ cv tr t w b := by
  obtain ⟨z, hz⟩ := Mem.zdvd hL hw he
  have h1 := bool_of hL hw ha; have h2 := bool_of hL hw hb
  simp only [notE, zev_mul, zev_sub, zev_c, zev_k, cur_cv] at hz
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with h' | h' <;>
  simp only [h, h'] at hz ⊢ <;> omega

/-- **Flags.** The kinds are one-hot over the scan and distribute families. -/
theorem row_flags (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) :
    cv tr t w act = cv tr t w kP + cv tr t w kS + cv tr t w kSh + cv tr t w kGH + cv tr t w kC ∧
      cv tr t w act ≤ 1 ∧
      cv tr t w fQ ≤ cv tr t w kS ∧ cv tr t w re ≤ cv tr t w kS ∧
      cv tr t w us0 ≤ cv tr t w b0 ∧ cv tr t w us1 ≤ cv tr t w b1 ∧
      cv tr t w us0 ≤ cv tr t w kS ∧ cv tr t w us1 ≤ cv tr t w kS := by
  have hA := bool_of hL hw (x := act) (by simp [boolCols, sharedBool])
  refine ⟨?_, hA, le_of_gate hL hw (by simp [constraints, shared, own, body]) (by simp [boolCols, ownBool]) (by simp [boolCols, sharedBool]),
    le_of_gate hL hw (by simp [constraints, shared, own, body]) (by simp [boolCols, ownBool]) (by simp [boolCols, sharedBool]),
    le_of_gate hL hw (by simp [constraints, shared, own, body]) (by simp [boolCols, ownBool]) (by simp [boolCols, sharedBool]),
    le_of_gate hL hw (by simp [constraints, shared, own, body]) (by simp [boolCols, ownBool]) (by simp [boolCols, sharedBool]),
    le_of_gate hL hw (by simp [constraints, shared, own, body]) (by simp [boolCols, ownBool]) (by simp [boolCols, sharedBool]),
    le_of_gate hL hw (by simp [constraints, shared, own, body]) (by simp [boolCols, ownBool]) (by simp [boolCols, sharedBool])⟩
  have hP := bool_of hL hw (x := kP) (by simp [boolCols, sharedBool])
  have hS := bool_of hL hw (x := kS) (by simp [boolCols, sharedBool])
  have hH := bool_of hL hw (x := kSh) (by simp [boolCols, sharedBool])
  have hG := bool_of hL hw (x := kGH) (by simp [boolCols, sharedBool])
  have hC := bool_of hL hw (x := kC) (by simp [boolCols, sharedBool])
  obtain ⟨z, hz⟩ := Mem.zdvd hL hw (e := sub (c act) (.add (c kP) (.add (c kS) (.add (c kSh)
    (.add (c kGH) (c kC)))))) (mem_common (List.mem_cons_self ..))
  simp only [zev_sub, zev_add, zev_c, cur_cv] at hz
  omega

/-- An active row is not the last row. -/
theorem row_next_lt (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (ha : cv tr t w act = 1) : w + 1 < tr.height t := by
  refine Nat.lt_of_le_of_ne hw (fun he => ?_)
  obtain ⟨z, hz⟩ := Mem.zdvd hL hw (e := .mul .isLast (c act))
    (mem_common (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only [zev_mul, zev_c, cur_cv, zev, Mem.tenv_last_one he, ha] at hz
  omega

theorem row_next_lt_kS (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (hk : cv tr t w kS = 1) : w + 1 < tr.height t := by
  have F := row_flags hL hw
  exact row_next_lt hL hw (by omega)

/-- Row 0, when active, is a param row or (with no scan rows) a distribute shard row. -/
theorem row_first (hL : SLocal tr t pub) (h0 : 0 < tr.height t) (ha : cv tr t 0 act = 1) :
    cv tr t 0 kP = 1 ∨ cv tr t 0 kSh = 1 := by
  have F := row_flags hL h0
  have hP := bool_of hL h0 (x := kP) (by simp [boolCols, sharedBool])
  have hH := bool_of hL h0 (x := kSh) (by simp [boolCols, sharedBool])
  obtain ⟨z, hz⟩ := Mem.zdvd hL h0 (e := .mul .isFirst (.mul (c act) (notE (.add (c kP) (c kSh)))))
    (mem_common (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))))
  simp only [notE, zev_mul, zev_sub, zev_add, zev_c, zev_k, cur_cv, zev_isFirst, ha] at hz
  simp only [tenv, if_pos] at hz
  omega

/-- Padding is a suffix. -/
theorem row_pad (hL : SLocal tr t pub) {w : Nat} (hw : w + 1 < tr.height t)
    (ha : cv tr t w act = 0) : cv tr t (w + 1) act = 0 := by
  have hw0 : w < tr.height t := by omega
  have hA := bool_of hL hw (x := act) (by simp [boolCols, sharedBool, ownBool])
  obtain ⟨z, hz⟩ := Mem.zdvd hL hw0 (e := mul3 .isTransition (notE (c act)) (n act))
    (mem_common (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  simp only [mul3, notE, zev_mul, zev_sub, zev_c, zev_n, zev_k, cur_cv, nxt_cv hw, ha] at hz
  simp only [zev, Mem.tenv_last_zero hw] at hz
  omega

/-! ## Gates with a flag equal to 1 -/

theorem eq_of_gate (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) {x a b : Nat}
    (he : Expr.mul (c x) (sub (c a) (c b)) ∈ constraints) (hx : cv tr t w x = 1) :
    cv tr t w a = cv tr t w b := by
  obtain ⟨z, hz⟩ := Mem.zdvd hL hw he
  simp only [zev_mul, zev_sub, zev_c, cur_cv, hx] at hz
  have := cv_lt (tr := tr) (t := t) w a; have := cv_lt (tr := tr) (t := t) w b
  omega

theorem zero_of_gate (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) {x a : Nat}
    (he : Expr.mul (c x) (c a) ∈ constraints) (hx : cv tr t w x = 1) : cv tr t w a = 0 := by
  obtain ⟨z, hz⟩ := Mem.zdvd hL hw he
  simp only [zev_mul, zev_c, cur_cv, hx] at hz
  have := cv_lt (tr := tr) (t := t) w a
  omega

/-! ## Param row and request start -/

/-- **Param row.** `base = q₀ + 2⁸q₁ + 2¹⁶q₂`, `D = q₃ + 2⁸q₄ + 2¹⁶clo` (mod `P`); the next row
starts request `cid = 0` of the same instance. -/
theorem row_param (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hp : cv tr t w kP = 1) :
    cv tr t w base = (cv tr t w (q 0) + 256 * cv tr t w (q 1) + 65536 * cv tr t w (q 2)) % 2013265921 ∧
      cv tr t w dd = (cv tr t w (q 3) + 256 * cv tr t w (q 4) + 65536 * cv tr t w clo) % 2013265921 ∧
      w + 1 < tr.height t ∧ cv tr t (w + 1) fQ = 1 ∧ cv tr t (w + 1) cid = 0 ∧
      ∀ x ∈ instCols, cv tr t (w + 1) x = cv tr t w x := by
  have F := row_flags hL hw
  have hw1 := row_next_lt hL hw (by omega)
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨z1, h1⟩ := Mem.zdvd hL hw (e := .mul (c kP) (sub (c base)
    (.add (c (q 0)) (.add (smul 256 (c (q 1))) (smul 65536 (c (q 2))))))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z2, h2⟩ := Mem.zdvd hL hw (e := .mul (c kP) (sub (c dd)
    (.add (c (q 3)) (.add (smul 256 (c (q 4))) (smul 65536 (c clo)))))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z3, h3⟩ := Mem.zdvd hL hw (e := .mul (c kP) (notE (n fQ))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z4, h4⟩ := Mem.zdvd hL hw (e := .mul (c kP) (n cid)) (by simp [constraints, shared, own, body, Dist.cCommon])
  simp only [notE, zev_mul, zev_sub, zev_add, zev_smul, zev_c, zev_n, zev_k, cur_cv, nxt_cv hw1,
    hp] at h1 h2 h3 h4
  have := lt base; have := lt dd; have := lt (q 0); have := lt (q 1); have := lt (q 2)
  have := lt (q 3); have := lt (q 4); have := lt clo; have := lt1 fQ; have := lt1 cid
  refine ⟨by omega, by omega, hw1, by omega, by omega, fun x hx => ?_⟩
  obtain ⟨z5, h5⟩ := Mem.zdvd hL hw (mem_instP hx)
  simp only [zev_mul, zev_sub, zev_c, zev_n, cur_cv, nxt_cv hw1, hp] at h5
  have := lt x; have := lt1 x
  omega

/-- **Request start.** -/
theorem row_start (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hf : cv tr t w fQ = 1) :
    cv tr t w kS = 1 ∧ cv tr t w u0 = 0 ∧ cv tr t w u1 = 0 ∧ cv tr t w y = 0 ∧ cv tr t w j = 0 ∧
      cv tr t w cur = cv tr t w base ∧
      cv tr t w cid = (cv tr t w clo + 256 * cv tr t w chi) % 2013265921 ∧
      cv tr t w link = (cv tr t w s * cv tr t w nn + cv tr t w r) % 2013265921 := by
  have F := row_flags hL hw
  have hS := bool_of hL hw (x := kS) (by simp [boolCols, sharedBool, ownBool])
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  obtain ⟨z1, h1⟩ := Mem.zdvd hL hw (e := .mul (c fQ) (sub (c cid) (.add (c clo) (smul 256 (c chi)))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z2, h2⟩ := Mem.zdvd hL hw (e := .mul (c fQ) (sub (c link) (.add (.mul (c s) (c nn)) (c r))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  simp only [zev_mul, zev_sub, zev_add, zev_smul, zev_c, cur_cv, hf] at h1 h2
  have := lt cid; have := lt clo; have := lt chi; have := lt link; have := lt s; have := lt nn
  have := lt r
  have e2 : ((cv tr t w s * cv tr t w nn : Nat) : Int) = (cv tr t w s : Int) * (cv tr t w nn : Int) := by
    simp
  refine ⟨by omega, zero_of_gate hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) hf,
    zero_of_gate hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) hf, zero_of_gate hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) hf,
    zero_of_gate hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) hf, eq_of_gate hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) hf,
    by omega, by omega⟩

/-! ## Inside a request -/

/-- **Step.** On a continuing request row (`kS = 1`, `re = 0`): the next row continues the request
(`kS' = 1`, `fQ' = 0`), the request constants are carried, `u` advances (`u' = u + 1 − 4·be`),
`y' = y + be`, `j' = j + b₀ + b₁`, `cur' = b₁ ? base + Q₁ : cm` (mod `P`), and the byte register
is consumed (`q₀ ≡ b₀ + 2b₁ + 4q₀'`, `q₁…q₄` kept) or rotated at the byte end (`q_i' = q_{i+1}`). -/
theorem row_step (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (hk : cv tr t w kS = 1) (hre : cv tr t w re = 0) :
    w + 1 < tr.height t ∧ cv tr t (w + 1) kS = 1 ∧ cv tr t (w + 1) fQ = 0 ∧
      (∀ x ∈ reqCols, cv tr t (w + 1) x = cv tr t w x) ∧
      cv tr t (w + 1) u0 + 2 * cv tr t (w + 1) u1 + 4 * (cv tr t w u0 * cv tr t w u1) =
        cv tr t w u0 + 2 * cv tr t w u1 + 1 ∧
      cv tr t (w + 1) y = (cv tr t w y + cv tr t w u0 * cv tr t w u1) % 2013265921 ∧
      cv tr t (w + 1) j = (cv tr t w j + cv tr t w b0 + cv tr t w b1) % 2013265921 ∧
      (cv tr t w b1 = 1 → cv tr t (w + 1) cur = (cv tr t w base + cv tr t w Q1) % 2013265921) ∧
      (cv tr t w b1 = 0 → cv tr t (w + 1) cur = cv tr t w cm) ∧
      (cv tr t w u0 * cv tr t w u1 = 1 → ∀ i, i < 4 → cv tr t (w + 1) (q i) = cv tr t w (q (i + 1))) ∧
      (cv tr t w u0 * cv tr t w u1 = 0 → ∀ i, i < 4 → cv tr t (w + 1) (q (i + 1)) = cv tr t w (q (i + 1))) ∧
      (cv tr t w u0 * cv tr t w u1 = 0 → ∃ z : Int, (cv tr t w (q 0) : Int) =
        cv tr t w b0 + 2 * cv tr t w b1 + 4 * cv tr t (w + 1) (q 0) + 2013265921 * z) := by
  have hw1 := row_next_lt_kS hL hw hk
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  have b := fun x (hx : x ∈ boolCols) => bool_of hL hw hx
  have b' := fun x (hx : x ∈ boolCols) => bool_of hL hw1 hx
  have hu0 := b u0 (by simp [boolCols, sharedBool, ownBool]); have hu1 := b u1 (by simp [boolCols, sharedBool, ownBool])
  have hb0 := b b0 (by simp [boolCols, sharedBool, ownBool]); have hb1 := b b1 (by simp [boolCols, sharedBool, ownBool])
  have hu0' := b' u0 (by simp [boolCols, sharedBool, ownBool]); have hu1' := b' u1 (by simp [boolCols, sharedBool, ownBool])
  have hbe : cv tr t w u0 * cv tr t w u1 ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu0 with h | h <;> simp [h, hu1]
  obtain ⟨z1, h1⟩ := Mem.zdvd hL hw (e := .mul gC (notE (n kS))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z2, h2⟩ := Mem.zdvd hL hw (e := .mul gC (n fQ)) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z3, h3⟩ := Mem.zdvd hL hw (e := .mul gC (sub (n cur)
    (.add (.mul (c b1) val1) (.mul (notE (c b1)) (c cm))))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z4, h4⟩ := Mem.zdvd hL hw (e := .mul gC (sub (n j) (.add (c j) (.add (c b0) (c b1)))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z5, h5⟩ := Mem.zdvd hL hw (e := .mul gC (sub (.add (n u0) (smul 2 (n u1)))
    (sub (.add uE (k 1)) (smul 4 be)))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z6, h6⟩ := Mem.zdvd hL hw (e := .mul gC (sub (n y) (.add (c y) be))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z7, h7⟩ := Mem.zdvd hL hw (e := mul3 gC (notE be)
    (sub (c (q 0)) (.add (c b0) (.add (smul 2 (c b1)) (smul 4 (n (q 0))))))) (by simp [constraints, shared, own, body, Dist.cCommon])
  simp only [gC, notE, mul3, be, uE, val1, zev_mul, zev_sub, zev_add, zev_smul, zev_c, zev_n, zev_k,
    cur_cv, nxt_cv hw1, hk, hre] at h1 h2 h3 h4 h5 h6 h7
  have := lt1 kS; have := lt1 fQ; have := lt1 cur; have := lt cm; have := lt base; have := lt Q1
  have := lt1 j; have := lt j; have := lt1 y; have := lt y; have := lt (q 0); have := lt1 (q 0)
  have ebe : ((cv tr t w u0 * cv tr t w u1 : Nat) : Int) = (cv tr t w u0 : Int) * (cv tr t w u1 : Int) := by
    simp
  refine ⟨hw1, by omega, by omega, fun x hx => ?_, ?_, ?_, by omega, fun h => ?_, fun h => ?_,
    fun h i hi => ?_, fun h i hi => ?_, fun h => ?_⟩
  · obtain ⟨z, hz⟩ := Mem.zdvd hL hw (mem_req hx)
    simp only [gC, zev_mul, zev_sub, zev_c, zev_n, cur_cv, nxt_cv hw1, hk, hre] at hz
    have := lt x; have := lt1 x
    omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu0 with e | e <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu1 with e' | e' <;>
    simp only [e, e'] at h5 ⊢ <;> omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu0 with e | e <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu1 with e' | e' <;>
    simp only [e, e'] at h6 ⊢ <;> omega
  · simp only [h] at h3; omega
  · simp only [h] at h3; omega
  · obtain ⟨z, hz⟩ := Mem.zdvd hL hw (mem_rot hi)
    simp only [gC, mul3, be, zev_mul, zev_sub, zev_c, zev_n, cur_cv, nxt_cv hw1, hk, hre] at hz
    rw [← ebe, h] at hz
    have := lt (q (i + 1)); have := lt1 (q i)
    omega
  · obtain ⟨z, hz⟩ := Mem.zdvd hL hw (mem_keep hi)
    simp only [gC, notE, mul3, be, zev_mul, zev_sub, zev_c, zev_n, zev_k, cur_cv, nxt_cv hw1, hk,
      hre] at hz
    rw [← ebe, h] at hz
    have := lt (q (i + 1)); have := lt1 (q (i + 1))
    omega
  · rw [← ebe, h] at h7
    exact ⟨z7, by omega⟩

/-! ## Values of a request row -/

theorem zev_r0 (w : Nat) : zev (tenv tr t w pub) r0E = (numv tr t w rb0 6 : Int) := by
  unfold r0E ZkFormal.Chacha.Rng.Table.num
  exact zev_sum_pow _ (fun b => .col (rb0 b) false) (fun b => cv tr t w (rb0 b)) 6 (fun _ _ => rfl)

theorem zev_r1 (w : Nat) : zev (tenv tr t w pub) r1E = (numv tr t w rb1 6 : Int) := by
  unfold r1E ZkFormal.Chacha.Rng.Table.num
  exact zev_sum_pow _ (fun b => .col (rb1 b) false) (fun b => cv tr t w (rb1 b)) 6 (fun _ _ => rfl)

theorem mem_bool_rb0 {i : Nat} (hi : i < 6) : rb0 i ∈ boolCols :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))))

theorem mem_bool_rb1 {i : Nat} (hi : i < 6) : rb1 i ∈ boolCols :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))

theorem mem_bool_qb0 {i : Nat} (hi : i < 23) : qb0 i ∈ boolCols :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))

theorem mem_bool_qb1 {i : Nat} (hi : i < 23) : qb1 i ∈ boolCols :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

/-- A cell equal to a bit decomposition (constraint `x − num col len`, `len ≤ 30`) is below `2^len`. -/
theorem range_of (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) {x : Nat} {col : Nat → Nat}
    {len : Nat} (he : sub (c x) (ZkFormal.Chacha.Rng.Table.num col len) ∈ constraints)
    (hc : ∀ i, i < len → col i ∈ boolCols) (hlen : len ≤ 30) : cv tr t w x < 2 ^ len := by
  have b : numv tr t w col len < 2 ^ len := nbits_le_of (fun i hi => bool_of hL hw (hc i hi))
  have e : zev (tenv tr t w pub) (ZkFormal.Chacha.Rng.Table.num col len) = (numv tr t w col len : Int) := by
    unfold ZkFormal.Chacha.Rng.Table.num numv
    exact zev_sum_pow _ (fun b => .col (col b) false) (fun b => cv tr t w (col b)) len (fun _ _ => rfl)
  obtain ⟨z, h⟩ := Mem.zdvd hL hw he
  simp only [zev_sub, zev_c, cur_cv, e] at h
  have hx := cv_lt (tr := tr) (t := t) w x
  have : (2 : Nat) ^ len ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hlen
  omega

/-- **Quotient ranges** (every row): `Q₀, Q₁ < 2^23`. -/
theorem q_ranges (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) :
    cv tr t w Q0 < 2 ^ 23 ∧ cv tr t w Q1 < 2 ^ 23 :=
  ⟨range_of hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) (fun _ hi => mem_bool_qb0 hi) (by decide),
   range_of hL hw (by simp [constraints, shared, own, body, Dist.cCommon]) (fun _ hi => mem_bool_qb1 hi) (by decide)⟩

theorem rem_lt (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1)
    {rb : Nat → Nat} (hb : ∀ i, i < 6 → rb i ∈ boolCols)
    (h4 : mul3 (c kS) (c (rb 5)) (c (rb 4)) ∈ constraints)
    (h3 : mul3 (c kS) (c (rb 5)) (c (rb 3)) ∈ constraints) : numv tr t w rb 6 < 40 := by
  have bb := fun i (hi : i < 6) => bool_of hL hw (hb i hi)
  have b0' := bb 0 (by omega); have b1' := bb 1 (by omega); have b2' := bb 2 (by omega)
  have b3' := bb 3 (by omega); have b4' := bb 4 (by omega); have b5' := bb 5 (by omega)
  obtain ⟨z4, e4'⟩ := Mem.zdvd hL hw h4
  obtain ⟨z3, e3'⟩ := Mem.zdvd hL hw h3
  simp only [mul3, zev_mul, zev_c, cur_cv, hk] at e4' e3'
  simp only [numv, nbits]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 b5' with h | h
  · rw [h]; omega
  · rw [h] at e4' e3' ⊢; omega

/-- **Values.** On a request row: the remainders are `< 40` and
`40·Q₀ + rem₀ ≡ D·(pos + 1)`, `40·Q₁ + rem₁ ≡ D·(pos + 2)` (mod `P`). -/
theorem row_val (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1) :
    numv tr t w rb0 6 < 40 ∧ numv tr t w rb1 6 < 40 ∧
      (∃ z : Int, 40 * (cv tr t w Q0 : Int) + numv tr t w rb0 6 =
        ((cv tr t w dd * (posv tr t w + 1) : Nat) : Int) + 2013265921 * z) ∧
      (∃ z : Int, 40 * (cv tr t w Q1 : Int) + numv tr t w rb1 6 =
        ((cv tr t w dd * (posv tr t w + 2) : Nat) : Int) + 2013265921 * z) := by
  refine ⟨rem_lt hL hw hk (fun i hi => mem_bool_rb0 hi) (by simp [constraints, shared, own, body, Dist.cCommon]) (by simp [constraints, shared, own, body, Dist.cCommon]),
    rem_lt hL hw hk (fun i hi => mem_bool_rb1 hi) (by simp [constraints, shared, own, body, Dist.cCommon]) (by simp [constraints, shared, own, body, Dist.cCommon]), ?_, ?_⟩
  · obtain ⟨z, hz⟩ := Mem.zdvd hL hw (e := .mul (c kS) (sub (.add (smul 40 (c Q0)) r0E)
      (.mul (c dd) (.add posE (k 1))))) (by simp [constraints, shared, own, body, Dist.cCommon])
    simp only [posE, uE, zev_mul, zev_sub, zev_add, zev_smul, zev_c, zev_k, cur_cv, zev_r0, hk] at hz
    refine ⟨z, ?_⟩
    simp only [posv]; push_cast at hz ⊢; omega
  · obtain ⟨z, hz⟩ := Mem.zdvd hL hw (e := .mul (c kS) (sub (.add (smul 40 (c Q1)) r1E)
      (.mul (c dd) (.add posE (k 2))))) (by simp [constraints, shared, own, body, Dist.cCommon])
    simp only [posE, uE, zev_mul, zev_sub, zev_add, zev_smul, zev_c, zev_k, cur_cv, zev_r1, hk] at hz
    refine ⟨z, ?_⟩
    simp only [posv]; push_cast at hz ⊢; simp only [Int.mul_add, Int.mul_one] at hz ⊢; omega

/-- The quotient is exact when it is small: `40·Q + R ≡ V (mod P)` with `R < 40`,
`Q < 2^25`, `V < 2^30` gives `Q = V / 40`. -/
theorem q_exact {Q R V : Nat} (hR : R < 40) (hQ : Q < 2 ^ 25) (hV : V < 2 ^ 30)
    (h : ∃ z : Int, 40 * (Q : Int) + R = (V : Int) + 2013265921 * z) : Q = V / 40 := by
  obtain ⟨z, hz⟩ := h
  have hQ' : Q < 33554432 := hQ
  have hV' : V < 1073741824 := hV
  have : z = 0 := by omega
  subst this
  omega

/-- **Row values.** On a request row: `cm = b₀ ? base + Q₀ : cur` (mod `P`), the byte end
`q₀ = b₀ + 2b₁`, `e4 = [y = 4]`, `re = e4·u₀·u₁`, `m = j + b₀ + b₁` (mod `P`) at the end,
`zk0 = [key = 0]`. -/
theorem row_cur (hL : SLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hk : cv tr t w kS = 1) :
    (cv tr t w b0 = 1 → cv tr t w cm = (cv tr t w base + cv tr t w Q0) % 2013265921) ∧
      (cv tr t w b0 = 0 → cv tr t w cm = cv tr t w cur) ∧
      (cv tr t w u0 = 1 → cv tr t w u1 = 1 → cv tr t w (q 0) = cv tr t w b0 + 2 * cv tr t w b1) ∧
      (cv tr t w e4 = 1 ↔ cv tr t w y = 4) ∧
      cv tr t w re = cv tr t w e4 * cv tr t w u0 * cv tr t w u1 ∧
      (cv tr t w re = 1 → cv tr t w m = (cv tr t w j + cv tr t w b0 + cv tr t w b1) % 2013265921) ∧
      cv tr t w zk0 = (if cv tr t w key = 0 then 1 else 0) := by
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have b := fun x (hx : x ∈ boolCols) => bool_of hL hw hx
  have hb0 := b b0 (by simp [boolCols, sharedBool, ownBool]); have hb1 := b b1 (by simp [boolCols, sharedBool, ownBool])
  have hu0 := b u0 (by simp [boolCols, sharedBool, ownBool]); have hu1 := b u1 (by simp [boolCols, sharedBool, ownBool])
  have he4 := b e4 (by simp [boolCols, sharedBool, ownBool]); have hre := b re (by simp [boolCols, sharedBool, ownBool])
  have hzk := b zk0 (by simp [boolCols, sharedBool, ownBool])
  obtain ⟨z1, h1⟩ := Mem.zdvd hL hw (e := .mul (c kS) (sub (c cm)
    (.add (.mul (c b0) val0) (.mul (notE (c b0)) (c cur))))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z2, h2⟩ := Mem.zdvd hL hw (e := mul3 (c kS) be (sub (c (q 0)) (.add (c b0) (smul 2 (c b1)))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z3, h3⟩ := Mem.zdvd hL hw (e := .mul (c kS) (sub (c e4) (notE (.mul (sub (c y) (k 4)) (c iy)))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z4, h4⟩ := Mem.zdvd hL hw (e := mul3 (c kS) (sub (c y) (k 4)) (c e4))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z5, h5⟩ := Mem.zdvd hL hw (e := .mul (c kS) (sub (c re) (mul3 (c e4) (c u0) (c u1))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z6, h6⟩ := Mem.zdvd hL hw (e := .mul (c re) (sub (c m) (.add (c j) (.add (c b0) (c b1)))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z7, h7⟩ := Mem.zdvd hL hw (e := .mul (c kS) (sub (c zk0) (notE (.mul (c key) (c ikey)))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z8, h8⟩ := Mem.zdvd hL hw (e := mul3 (c kS) (c key) (c zk0))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  simp only [mul3, be, val0, notE, zev_mul, zev_sub, zev_add, zev_smul, zev_c, zev_k, cur_cv, hk]
    at h1 h2 h3 h4 h5 h6 h7 h8
  have := lt cm; have := lt cur; have := lt base; have := lt Q0; have := lt (q 0); have := lt y
  have := lt m; have := lt j; have := lt key
  refine ⟨fun h => ?_, fun h => ?_, fun e e' => ?_, ?_, ?_, fun h => ?_, ?_⟩
  · simp only [h] at h1; omega
  · simp only [h] at h1; omega
  · simp only [e, e'] at h2; omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he4 with h | h <;> simp only [h] at h3 h4
    · constructor
      · intro h'; omega
      · intro hy; simp only [hy] at h3; omega
    · constructor
      · intro _; omega
      · intro _; exact h
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he4 with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu0 with e | e <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu1 with e' | e' <;>
    simp only [h, e, e'] at h5 ⊢ <;> omega
  · simp only [h] at h6; omega
  · split
    · next hkey => simp only [hkey] at h7; omega
    · next hkey =>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hzk with h | h
      · exact h
      · simp only [h] at h8; omega

/-- **After a request end** the next active request row starts a request (`fQ`); if it does,
it is request `cid + 1` of the same instance. -/
theorem row_after_end (hL : SLocal tr t pub) {w : Nat} (hw : w + 1 < tr.height t)
    (hre : cv tr t w re = 1) :
    (cv tr t (w + 1) kS = 1 → cv tr t (w + 1) fQ = 1) ∧
      (cv tr t (w + 1) fQ = 1 → cv tr t (w + 1) cid = (cv tr t w cid + 1) % 2013265921 ∧
        ∀ x ∈ instCols, cv tr t (w + 1) x = cv tr t w x) := by
  have hw0 : w < tr.height t := by omega
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨z1, h1⟩ := Mem.zdvd hL hw0 (e := mul3 (c re) (n kS) (notE (n fQ))) (by simp [constraints, shared, own, body, Dist.cCommon])
  obtain ⟨z2, h2⟩ := Mem.zdvd hL hw0 (e := .mul (.mul (c re) (n fQ)) (sub (n cid) (.add (c cid) (k 1))))
    (by simp [constraints, shared, own, body, Dist.cCommon])
  simp only [mul3, notE, zev_mul, zev_sub, zev_add, zev_c, zev_n, zev_k, cur_cv, nxt_cv hw, hre] at h1 h2
  have := lt1 fQ; have := lt1 cid; have := lt cid
  refine ⟨fun h => ?_, fun h => ⟨?_, fun x hx => ?_⟩⟩
  · simp only [h] at h1; omega
  · simp only [h] at h2; omega
  · obtain ⟨z, hz⟩ := Mem.zdvd hL hw0 (mem_instE hx)
    simp only [zev_mul, zev_sub, zev_c, zev_n, cur_cv, nxt_cv hw, hre, h] at hz
    have := lt x; have := lt1 x
    omega

end

end ZkFormal.NearV3.Sched.Scan

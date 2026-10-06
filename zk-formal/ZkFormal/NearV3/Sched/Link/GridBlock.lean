import ZkFormal.NearV3.Sched.Link.ScanRows

/-!
# ZkFormal.NearV3.Sched.Link.GridBlock — the distribute section of an instance (stage F, b1)

Purely local facts about the distribute rows of `ssdV3` (`Local ScanDist.constraints`).

A distribute section starts at a **start row** `w₀` (`Start`: a sender shard row with
`side = a = kp = 0`) and, with `n = nn(w₀)` (`1 ≤ n ≤ 64`), has `blen n = 2n + n(n+1)` rows:

* shard rows `w₀ + sd·n + x` (`SRow`, side `sd < 2`, position `x < n`);
* for `i < n` a header `w₀ + 2n + i(n+1)` (`HRow`, `a = i`) and cells
  `w₀ + 2n + i(n+1) + 1 + j` (`CRow`, `a = i`, `b = j`, `j < n`);

all with `w₀`'s `τ` and `nn` (`IC`). **`block`** walks the section (`e1 = [x = n−1]` on shard
rows and cells, `e2 = [i = n−1]` on cells), ends with `eI = 1` on the last cell, and the next
active row is another start. **`cover`**: every distribute row lies in the section of some start
(given `1 ≤ nn ≤ 64` on shard rows, which the public shard record pins). `decode` names the row
of a section at a given offset.

The row steps (`shard_mid`, `shard_end0`, `shard_end1`, `hdr_next`, `cell_mid`, `cell_rowend`,
`cell_end`) also give the carried grid values (`s`, `N1`, `L1`, `kp`) used by b3–b5.
-/

namespace ZkFormal.NearV3.Sched.Dist

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

/-- Simp set for evaluating a distribute constraint. -/
macro "dz " h:ident " [" ts:term,* "]" : tactic => do
  let ls ← ts.getElems.mapM fun x => `(Lean.Parser.Tactic.simpLemma| $x:term)
  `(tactic| simp only [mul3, notE, x1E, zev_mul, zev_sub, zev_add, zev_c, zev_n,
      zev_k, zev_smul, cur_cv, $ls,*] at $h:ident)

/-- A flag pinned by `e = 1 − X·g`, `X·e = 0` (mod `P`) with a small `X` is `[X = 0]`. -/
theorem flag_of {e : Nat} {X g q1 q2 : Int} (he : e ≤ 1) (hX1 : -64 < X) (hX2 : X < 64)
    (h1 : (e : Int) - (1 - X * g) = 2013265921 * q1) (h2 : X * e = 2013265921 * q2) :
    e = if X = 0 then 1 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h <;> subst h
  · split
    · next hx => subst hx; simp only [Int.zero_mul, Int.sub_zero] at h1; omega
    · rfl
  · push_cast at h2
    simp only [Int.mul_one] at h2
    split
    · rfl
    · omega

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- One-hot kinds of a row (distribute view). -/
theorem kinds (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) :
    cv tr t w act = cv tr t w kP + cv tr t w kS + cv tr t w kSh + cv tr t w kGH + cv tr t w kC ∧
      cv tr t w act ≤ 1 := by
  have hA := bool_of hD hw (x := act) (by simp [boolCols])
  have hP := bool_of hD hw (x := kP) (by simp [boolCols])
  have hS := bool_of hD hw (x := kS) (by simp [boolCols])
  have hH := bool_of hD hw (x := kSh) (by simp [boolCols])
  have hG := bool_of hD hw (x := kGH) (by simp [boolCols])
  have hC := bool_of hD hw (x := kC) (by simp [boolCols])
  obtain ⟨z, hz⟩ := Mem.zdvd hD hw (e := sub (c act) (.add (c kP) (.add (c kS) (.add (c kSh)
    (.add (c kGH) (c kC)))))) (by simp [constraints, cKind, cCommon])
  simp only [zev_sub, zev_add, zev_c, cur_cv] at hz
  omega

/-- An active row is not the last one. -/
theorem next_lt (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (ha : cv tr t w act = 1) :
    w + 1 < tr.height t := by
  refine Nat.lt_of_le_of_ne hw (fun he => ?_)
  obtain ⟨z, hz⟩ := Mem.zdvd hD hw (e := .mul .isLast (c act)) (by simp [constraints, cKind, cCommon])
  simp only [zev_mul, zev_c, cur_cv, zev, Mem.tenv_last_one he, ha] at hz
  omega

theorem next_lt' (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (h : cv tr t w kSh = 1 ∨ cv tr t w kGH = 1 ∨ cv tr t w kC = 1) : w + 1 < tr.height t := by
  have K := kinds hD hw
  exact next_lt hD hw (by omega)

/-! ## Flags `e1`, `e2` -/

/-- `e1` on a shard row: `[a = n − 1]`. -/
theorem e1_sh (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    (ha : cv tr t w a < 64) (hn1 : 1 ≤ cv tr t w nn) (hn : cv tr t w nn ≤ 64) :
    cv tr t w e1 = if cv tr t w a = cv tr t w nn - 1 then 1 else 0 := by
  have K := kinds hD hw
  have hC : cv tr t w kC = 0 := by omega
  have he := bool_of hD hw (x := e1) (by simp [boolCols])
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (.add (c kSh) (c kC))
    (sub (c e1) (notE (.mul (sub x1E (sub (c nn) (k 1))) (c ig1))))) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (.add (c kSh) (c kC))
    (.mul (sub x1E (sub (c nn) (k 1))) (c e1))) (by simp [constraints, cKind])
  dz c1 [hs, hC]
  dz c2 [hs, hC]
  push_cast at c1 c2
  simp only [Int.one_mul, Int.zero_mul, Int.add_zero] at c1 c2
  have := flag_of (X := (cv tr t w a : Int) - ((cv tr t w nn : Int) - 1)) he (by omega) (by omega) c1 c2
  rw [this]
  by_cases h : cv tr t w a = cv tr t w nn - 1
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- `e1` on a cell: `[b = n − 1]`. -/
theorem e1_cell (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hc : cv tr t w kC = 1)
    (hb : cv tr t w b < 64) (hn1 : 1 ≤ cv tr t w nn) (hn : cv tr t w nn ≤ 64) :
    cv tr t w e1 = if cv tr t w b = cv tr t w nn - 1 then 1 else 0 := by
  have K := kinds hD hw
  have hS : cv tr t w kSh = 0 := by omega
  have he := bool_of hD hw (x := e1) (by simp [boolCols])
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (.add (c kSh) (c kC))
    (sub (c e1) (notE (.mul (sub x1E (sub (c nn) (k 1))) (c ig1))))) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (.add (c kSh) (c kC))
    (.mul (sub x1E (sub (c nn) (k 1))) (c e1))) (by simp [constraints, cKind])
  dz c1 [hS, hc]
  dz c2 [hS, hc]
  push_cast at c1 c2
  simp only [Int.one_mul, Int.zero_mul, Int.add_zero, Int.zero_add] at c1 c2
  have := flag_of (X := (cv tr t w b : Int) - ((cv tr t w nn : Int) - 1)) he (by omega) (by omega) c1 c2
  rw [this]
  by_cases h : cv tr t w b = cv tr t w nn - 1
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- `e2` on a cell: `[a = n − 1]`. -/
theorem e2_cell (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hc : cv tr t w kC = 1)
    (ha : cv tr t w a < 64) (hn1 : 1 ≤ cv tr t w nn) (hn : cv tr t w nn ≤ 64) :
    cv tr t w e2 = if cv tr t w a = cv tr t w nn - 1 then 1 else 0 := by
  have he := bool_of hD hw (x := e2) (by decide)
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (c kC)
    (sub (c e2) (notE (.mul (sub (c a) (sub (c nn) (k 1))) (c ig2))))) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (c kC)
    (.mul (sub (c a) (sub (c nn) (k 1))) (c e2))) (by simp [constraints, cKind])
  dz c1 [hc]
  dz c2 [hc]
  push_cast at c1 c2
  simp only [Int.one_mul] at c1 c2
  have := flag_of (X := (cv tr t w a : Int) - ((cv tr t w nn : Int) - 1)) he (by omega) (by omega) c1 c2
  rw [this]
  by_cases h : cv tr t w a = cv tr t w nn - 1
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-! ## Row steps -/

/-- A shard row before the end of its side. -/
theorem shard_mid (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    (he : cv tr t w e1 = 0) (ha : cv tr t w a < 64) :
    w + 1 < tr.height t ∧ cv tr t (w + 1) kSh = 1 ∧ cv tr t (w + 1) side = cv tr t w side ∧
      cv tr t (w + 1) a = cv tr t w a + 1 ∧
      cv tr t (w + 1) kp = (cv tr t w cx + 1) % 2013265921 ∧
      cv tr t (w + 1) tau = cv tr t w tau ∧ cv tr t (w + 1) nn = cv tr t w nn := by
  have hw1 := next_lt' hD hw (Or.inl hs)
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (notE (c e1)) (notE (n kSh)))
    (by simp [constraints, cShard])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (notE (c e1)) (sub (n side) (c side)))
    (by simp [constraints, cShard])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (notE (c e1)) (sub (n a) (.add (c a) (k 1))))
    (by simp [constraints, cShard])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (notE (c e1)) (sub (n kp) (.add (c cx) (k 1))))
    (by simp [constraints, cShard])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (n tau) (c tau)))
    (by simp [constraints, cShard, instCols])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (n nn) (c nn)))
    (by simp [constraints, cShard, instCols])
  dz c1 [nxt_cv hw1, hs, he]; dz c2 [nxt_cv hw1, hs, he]; dz c3 [nxt_cv hw1, hs, he]
  dz c4 [nxt_cv hw1, hs, he]; dz c5 [nxt_cv hw1, hs]; dz c6 [nxt_cv hw1, hs]
  push_cast at c1 c2 c3 c4 c5 c6
  have := lt1 kSh; have := lt1 side; have := lt side; have := lt1 a; have := lt1 kp; have := lt cx
  have := lt1 tau; have := lt tau; have := lt1 nn; have := lt nn
  refine ⟨hw1, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The last sender shard row: the receivers start. -/
theorem shard_end0 (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    (he : cv tr t w e1 = 1) (hsd : cv tr t w side = 0) :
    w + 1 < tr.height t ∧ cv tr t (w + 1) kSh = 1 ∧ cv tr t (w + 1) side = 1 ∧
      cv tr t (w + 1) a = 0 ∧ cv tr t (w + 1) kp = 0 ∧
      cv tr t (w + 1) tau = cv tr t w tau ∧ cv tr t (w + 1) nn = cv tr t w nn := by
  have hw1 := next_lt' hD hw (Or.inl hs)
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (c e1) (.mul (notE (c side)) (notE (n kSh))))
    (by simp [constraints, cShard])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (c e1) (.mul (notE (c side)) (sub (n side) (k 1))))
    (by simp [constraints, cShard])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (c e1) (.mul (notE (c side)) (n a)))
    (by simp [constraints, cShard])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (c e1) (n kp)) (by simp [constraints, cShard])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (n tau) (c tau)))
    (by simp [constraints, cShard, instCols])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (n nn) (c nn)))
    (by simp [constraints, cShard, instCols])
  dz c1 [nxt_cv hw1, hs, he, hsd]; dz c2 [nxt_cv hw1, hs, he, hsd]; dz c3 [nxt_cv hw1, hs, he, hsd]
  dz c4 [nxt_cv hw1, hs, he]; dz c5 [nxt_cv hw1, hs]; dz c6 [nxt_cv hw1, hs]
  push_cast at c1 c2 c3 c4 c5 c6
  have := lt1 kSh; have := lt1 side; have := lt1 a; have := lt1 kp
  have := lt1 tau; have := lt tau; have := lt1 nn; have := lt nn
  refine ⟨hw1, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The last receiver shard row: the grid starts with header 0. -/
theorem shard_end1 (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    (he : cv tr t w e1 = 1) (hsd : cv tr t w side = 1) :
    w + 1 < tr.height t ∧ cv tr t (w + 1) kGH = 1 ∧ cv tr t (w + 1) a = 0 ∧
      cv tr t (w + 1) tau = cv tr t w tau ∧ cv tr t (w + 1) nn = cv tr t w nn := by
  have hw1 := next_lt' hD hw (Or.inl hs)
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (c e1) (.mul (c side) (notE (n kGH))))
    (by simp [constraints, cShard])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := mul3 (c kSh) (c e1) (.mul (c side) (n a)))
    (by simp [constraints, cShard])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (n tau) (c tau)))
    (by simp [constraints, cShard, instCols])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (n nn) (c nn)))
    (by simp [constraints, cShard, instCols])
  dz c1 [nxt_cv hw1, hs, he, hsd]; dz c3 [nxt_cv hw1, hs, he, hsd]
  dz c5 [nxt_cv hw1, hs]; dz c6 [nxt_cv hw1, hs]
  push_cast at c1 c3 c5 c6
  have := lt1 kGH; have := lt1 a
  have := lt1 tau; have := lt tau; have := lt1 nn; have := lt nn
  refine ⟨hw1, by omega, by omega, by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- A header: `b = 255`; the next row is cell `(a, 0)` carrying the sender endpoint. -/
theorem hdr_next (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hg : cv tr t w kGH = 1) :
    cv tr t w b = 255 ∧ w + 1 < tr.height t ∧ cv tr t (w + 1) kC = 1 ∧ cv tr t (w + 1) b = 0 ∧
      cv tr t (w + 1) a = cv tr t w a ∧ cv tr t (w + 1) s = cv tr t w r ∧
      cv tr t (w + 1) N1 = cv tr t w N2 ∧ cv tr t (w + 1) L1 = cv tr t w L2 ∧
      cv tr t (w + 1) tau = cv tr t w tau ∧ cv tr t (w + 1) nn = cv tr t w nn := by
  have hw1 := next_lt' hD hw (Or.inr (Or.inl hg))
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q0, c0⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (c b) (k 255))) (by simp [constraints, cGrid])
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (notE (n kC))) (by simp [constraints, cGrid])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (n b)) (by simp [constraints, cGrid])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (n a) (c a))) (by simp [constraints, cGrid])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (n s) (c r))) (by simp [constraints, cGrid])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (n N1) (c N2))) (by simp [constraints, cGrid])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (n L1) (c L2))) (by simp [constraints, cGrid])
  obtain ⟨q7, c7⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (n tau) (c tau)))
    (by simp [constraints, cGrid, instCols])
  obtain ⟨q8, c8⟩ := Mem.zdvd hD hw (e := .mul (c kGH) (sub (n nn) (c nn)))
    (by simp [constraints, cGrid, instCols])
  dz c0 [hg]; dz c1 [nxt_cv hw1, hg]; dz c2 [nxt_cv hw1, hg]; dz c3 [nxt_cv hw1, hg]
  dz c4 [nxt_cv hw1, hg]; dz c5 [nxt_cv hw1, hg]; dz c6 [nxt_cv hw1, hg]; dz c7 [nxt_cv hw1, hg]
  dz c8 [nxt_cv hw1, hg]
  push_cast at c0 c1 c2 c3 c4 c5 c6 c7 c8
  have := lt b; have := lt1 kC; have := lt1 b; have := lt1 a; have := lt a; have := lt1 s; have := lt r
  have := lt1 N1; have := lt N2; have := lt1 L1; have := lt L2
  have := lt1 tau; have := lt tau; have := lt1 nn; have := lt nn
  refine ⟨by omega, hw1, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- A cell before the end of its row: the sender endpoint steps by `(al, gb)`. -/
theorem cell_mid (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hc : cv tr t w kC = 1)
    (he : cv tr t w e1 = 0) (hb : cv tr t w b < 64) :
    w + 1 < tr.height t ∧ cv tr t (w + 1) kC = 1 ∧ cv tr t (w + 1) a = cv tr t w a ∧
      cv tr t (w + 1) b = cv tr t w b + 1 ∧ cv tr t (w + 1) s = cv tr t w s ∧
      ((cv tr t (w + 1) N1 : Int) - ((cv tr t w N1 : Int) - cv tr t w al)) % 2013265921 = 0 ∧
      ((cv tr t (w + 1) L1 : Int) - ((cv tr t w L1 : Int) - cv tr t w gb)) % 2013265921 = 0 ∧
      cv tr t (w + 1) tau = cv tr t w tau ∧ cv tr t (w + 1) nn = cv tr t w nn := by
  have hw1 := next_lt' hD hw (Or.inr (Or.inr hc))
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (notE (n kC))) (by simp [constraints, cGrid])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n a) (c a))) (by simp [constraints, cGrid])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n b) (.add (c b) (k 1))))
    (by simp [constraints, cGrid])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n s) (c s))) (by simp [constraints, cGrid])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n N1) (sub (c N1) (c al))))
    (by simp [constraints, cGrid])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n L1) (sub (c L1) (c gb))))
    (by simp [constraints, cGrid])
  obtain ⟨q7, c7⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n tau) (c tau)))
    (by simp [constraints, cGrid, instCols])
  obtain ⟨q8, c8⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (notE (c e1)) (sub (n nn) (c nn)))
    (by simp [constraints, cGrid, instCols])
  dz c1 [nxt_cv hw1, hc, he]; dz c2 [nxt_cv hw1, hc, he]; dz c3 [nxt_cv hw1, hc, he]
  dz c4 [nxt_cv hw1, hc, he]; dz c5 [nxt_cv hw1, hc, he]; dz c6 [nxt_cv hw1, hc, he]
  dz c7 [nxt_cv hw1, hc, he]; dz c8 [nxt_cv hw1, hc, he]
  push_cast at c1 c2 c3 c4 c5 c6 c7 c8
  have := lt1 kC; have := lt1 b; have := lt1 a; have := lt a; have := lt1 s; have := lt s
  have := lt1 tau; have := lt tau; have := lt1 nn; have := lt nn
  refine ⟨hw1, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- The last cell of a row that is not the last row: the next header. -/
theorem cell_rowend (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hc : cv tr t w kC = 1)
    (he : cv tr t w e1 = 1) (he2 : cv tr t w e2 = 0) (ha : cv tr t w a < 64) :
    w + 1 < tr.height t ∧ cv tr t (w + 1) kGH = 1 ∧ cv tr t (w + 1) a = cv tr t w a + 1 ∧
      cv tr t (w + 1) tau = cv tr t w tau ∧ cv tr t (w + 1) nn = cv tr t w nn := by
  have hw1 := next_lt' hD hw (Or.inr (Or.inr hc))
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (c e1) (.mul (notE (c e2)) (notE (n kGH))))
    (by simp [constraints, cGrid])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (c e1) (.mul (notE (c e2)) (sub (n a) (.add (c a) (k 1)))))
    (by simp [constraints, cGrid])
  obtain ⟨q7, c7⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (c e1) (.mul (notE (c e2)) (sub (n tau) (c tau))))
    (by simp [constraints, cGrid, instCols])
  obtain ⟨q8, c8⟩ := Mem.zdvd hD hw (e := mul3 (c kC) (c e1) (.mul (notE (c e2)) (sub (n nn) (c nn))))
    (by simp [constraints, cGrid, instCols])
  dz c1 [nxt_cv hw1, hc, he, he2]; dz c2 [nxt_cv hw1, hc, he, he2]
  dz c7 [nxt_cv hw1, hc, he, he2]; dz c8 [nxt_cv hw1, hc, he, he2]
  push_cast at c1 c2 c7 c8
  have := lt1 kGH; have := lt1 a
  have := lt1 tau; have := lt tau; have := lt1 nn; have := lt nn
  refine ⟨hw1, by omega, by omega, by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- The last cell of the grid: `eI = 1`, and an active next row is a start. -/
theorem cell_end (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hc : cv tr t w kC = 1)
    (he : cv tr t w e1 = 1) (he2 : cv tr t w e2 = 1) :
    cv tr t w eI = 1 ∧ w + 1 < tr.height t ∧
      (cv tr t (w + 1) act = 1 → cv tr t (w + 1) kSh = 1 ∧ cv tr t (w + 1) side = 0 ∧
        cv tr t (w + 1) a = 0 ∧ cv tr t (w + 1) kp = 0) := by
  have hw1 := next_lt' hD hw (Or.inr (Or.inr hc))
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (w + 1) x
  obtain ⟨q0, c0⟩ := Mem.zdvd hD hw (e := sub (c eI) (mul3 (c kC) (c e1) (c e2))) (by simp [constraints, cGrid])
  dz c0 [hc, he, he2]
  push_cast at c0
  have heI : cv tr t w eI = 1 := by have := lt eI; omega
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := mul3 (c eI) (n act) (notE (n kSh))) (by simp [constraints, cGrid])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := mul3 (c eI) (n act) (n side)) (by simp [constraints, cGrid])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := mul3 (c eI) (n act) (n a)) (by simp [constraints, cGrid])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := .mul (c eI) (n kp)) (by simp [constraints, cGrid])
  refine ⟨heI, hw1, fun ha => ?_⟩
  dz c1 [nxt_cv hw1, heI, ha]; dz c2 [nxt_cv hw1, heI, ha]; dz c3 [nxt_cv hw1, heI, ha]
  dz c4 [nxt_cv hw1, heI]
  push_cast at c1 c2 c3 c4
  have := lt1 kSh; have := lt1 side; have := lt1 a; have := lt1 kp
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## The section of a start row -/

/-- Row `w` has row `w₀`'s instance constants. -/
def IC (tr : Trace Fp) (t w w0 : Nat) : Prop :=
  cv tr t w tau = cv tr t w0 tau ∧ cv tr t w nn = cv tr t w0 nn

/-- A start row: a sender shard row with `a = kp = 0`. -/
def Start (tr : Trace Fp) (t w0 : Nat) : Prop :=
  w0 < tr.height t ∧ cv tr t w0 kSh = 1 ∧ cv tr t w0 side = 0 ∧ cv tr t w0 a = 0 ∧ cv tr t w0 kp = 0

/-- Shard row `x` of side `sd`. -/
def SRow (tr : Trace Fp) (t w0 nv sd x : Nat) : Prop :=
  w0 + sd * nv + x < tr.height t ∧ cv tr t (w0 + sd * nv + x) kSh = 1 ∧
    cv tr t (w0 + sd * nv + x) side = sd ∧ cv tr t (w0 + sd * nv + x) a = x ∧
    IC tr t (w0 + sd * nv + x) w0 ∧ (x = 0 → cv tr t (w0 + sd * nv + x) kp = 0)

/-- Header `i`. -/
def HRow (tr : Trace Fp) (t w0 nv i : Nat) : Prop :=
  w0 + 2 * nv + i * (nv + 1) < tr.height t ∧ cv tr t (w0 + 2 * nv + i * (nv + 1)) kGH = 1 ∧
    cv tr t (w0 + 2 * nv + i * (nv + 1)) a = i ∧ IC tr t (w0 + 2 * nv + i * (nv + 1)) w0

/-- Cell `(i, j)`. -/
def CRow (tr : Trace Fp) (t w0 nv i j : Nat) : Prop :=
  w0 + 2 * nv + i * (nv + 1) + 1 + j < tr.height t ∧
    cv tr t (w0 + 2 * nv + i * (nv + 1) + 1 + j) kC = 1 ∧
    cv tr t (w0 + 2 * nv + i * (nv + 1) + 1 + j) a = i ∧
    cv tr t (w0 + 2 * nv + i * (nv + 1) + 1 + j) b = j ∧ IC tr t (w0 + 2 * nv + i * (nv + 1) + 1 + j) w0

/-- Rows of a section. -/
def blen (nv : Nat) : Nat := 2 * nv + nv * (nv + 1)

theorem blen_last {nv : Nat} (h1 : 1 ≤ nv) :
    2 * nv + (nv - 1) * (nv + 1) + 1 + (nv - 1) + 1 = blen nv := by
  cases nv with
  | zero => omega
  | succ m =>
    simp only [blen, Nat.add_sub_cancel, Nat.succ_mul]
    omega

theorem hdr_succ (nv i : Nat) (h1 : 1 ≤ nv) :
    2 * nv + i * (nv + 1) + 1 + (nv - 1) + 1 = 2 * nv + (i + 1) * (nv + 1) := by
  rw [Nat.add_mul i 1 (nv + 1), Nat.one_mul]; omega

theorem IC.step {w w0 : Nat} (h : IC tr t w w0) (h1 : cv tr t (w + 1) tau = cv tr t w tau)
    (h2 : cv tr t (w + 1) nn = cv tr t w nn) : IC tr t (w + 1) w0 :=
  ⟨h1.trans h.1, h2.trans h.2⟩

/-- **One side of shard rows.** -/
theorem side_walk (hD : DLocal tr t pub) {w0 nv sd : Nat} (h1 : 1 ≤ nv) (h64 : nv ≤ 64)
    (hn : cv tr t w0 nn = nv) (h0 : SRow tr t w0 nv sd 0) : ∀ x, x < nv → SRow tr t w0 nv sd x := by
  intro x
  induction x with
  | zero => intro _; exact h0
  | succ x ih =>
    intro hx
    obtain ⟨hw, hs, hsd, ha, hic, -⟩ := ih (by omega)
    have hnn : cv tr t (w0 + sd * nv + x) nn = nv := hic.2.trans hn
    have he := e1_sh hD hw hs (by omega) (by omega) (by omega)
    rw [ha, hnn, if_neg (by omega)] at he
    obtain ⟨hw1, s1, sd1, a1, -, t1, n1⟩ := shard_mid hD hw hs he (by omega)
    unfold SRow
    rw [show w0 + sd * nv + (x + 1) = w0 + sd * nv + x + 1 by omega]
    exact ⟨hw1, s1, sd1.trans hsd, by rw [a1, ha], hic.step t1 n1, fun h => absurd h (by omega)⟩

/-- **One row of cells.** -/
theorem row_walk (hD : DLocal tr t pub) {w0 nv i : Nat} (h1 : 1 ≤ nv) (h64 : nv ≤ 64)
    (hn : cv tr t w0 nn = nv) (hi : i < nv) (hH : HRow tr t w0 nv i) :
    ∀ j, j < nv → CRow tr t w0 nv i j := by
  obtain ⟨hw, hg, ha, hic⟩ := hH
  obtain ⟨-, hw1, k1, b1, a1, -, -, -, t1, n1⟩ := hdr_next hD hw hg
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨hw1, k1, a1.trans ha, b1, hic.step t1 n1⟩
  | succ j ih =>
    intro hj
    obtain ⟨hw', hc, ha', hb', hic'⟩ := ih (by omega)
    have hnn : cv tr t (w0 + 2 * nv + i * (nv + 1) + 1 + j) nn = nv := hic'.2.trans hn
    have he := e1_cell hD hw' hc (by omega) (by omega) (by omega)
    rw [hb', hnn, if_neg (by omega)] at he
    obtain ⟨hw2, k2, a2, b2, -, -, -, t2, n2⟩ := cell_mid hD hw' hc he (by omega)
    unfold CRow
    rw [show w0 + 2 * nv + i * (nv + 1) + 1 + (j + 1) = w0 + 2 * nv + i * (nv + 1) + 1 + j + 1 by omega]
    exact ⟨hw2, k2, a2.trans ha', by rw [b2, hb'], hic'.step t2 n2⟩

/-- **The section of a start row.** -/
theorem block (hD : DLocal tr t pub) {w0 nv : Nat} (hS : Start tr t w0) (hn : cv tr t w0 nn = nv)
    (h1 : 1 ≤ nv) (h64 : nv ≤ 64) :
    (∀ sd x, sd < 2 → x < nv → SRow tr t w0 nv sd x) ∧ (∀ i, i < nv → HRow tr t w0 nv i) ∧
      (∀ i j, i < nv → j < nv → CRow tr t w0 nv i j) ∧
      cv tr t (w0 + blen nv - 1) eI = 1 ∧ w0 + blen nv < tr.height t ∧
      (cv tr t (w0 + blen nv) act = 1 → Start tr t (w0 + blen nv)) := by
  obtain ⟨hw0, hs0, hsd0, ha0, hkp0⟩ := hS
  have S0 : SRow tr t w0 nv 0 0 := by
    unfold SRow; simp only [Nat.zero_mul, Nat.add_zero]
    exact ⟨hw0, hs0, hsd0, ha0, ⟨rfl, rfl⟩, fun _ => hkp0⟩
  have side0 := side_walk hD h1 h64 hn S0
  -- end of the sender side
  have S10 : SRow tr t w0 nv 1 0 := by
    obtain ⟨hw, hs, hsd, ha, hic, -⟩ := side0 (nv - 1) (by omega)
    have hnn : cv tr t (w0 + 0 * nv + (nv - 1)) nn = nv := hic.2.trans hn
    have he := e1_sh hD hw hs (by omega) (by omega) (by omega)
    rw [ha, hnn, if_pos rfl] at he
    obtain ⟨hw1, s1, sd1, a1, kp1, t1, n1⟩ := shard_end0 hD hw hs he hsd
    unfold SRow
    rw [show w0 + 1 * nv + 0 = w0 + 0 * nv + (nv - 1) + 1 by omega]
    exact ⟨hw1, s1, sd1, a1, hic.step t1 n1, fun _ => kp1⟩
  have side1 := side_walk hD h1 h64 hn S10
  have sides : ∀ sd x, sd < 2 → x < nv → SRow tr t w0 nv sd x := by
    intro sd x hsd hx
    rcases (by omega : sd = 0 ∨ sd = 1) with rfl | rfl
    · exact side0 x hx
    · exact side1 x hx
  -- the first header
  have H0 : HRow tr t w0 nv 0 := by
    obtain ⟨hw, hs, hsd, ha, hic, -⟩ := side1 (nv - 1) (by omega)
    have hnn : cv tr t (w0 + 1 * nv + (nv - 1)) nn = nv := hic.2.trans hn
    have he := e1_sh hD hw hs (by omega) (by omega) (by omega)
    rw [ha, hnn, if_pos rfl] at he
    obtain ⟨hw1, g1, a1, t1, n1⟩ := shard_end1 hD hw hs he hsd
    unfold HRow
    rw [show w0 + 2 * nv + 0 * (nv + 1) = w0 + 1 * nv + (nv - 1) + 1 by omega]
    exact ⟨hw1, g1, a1, hic.step t1 n1⟩
  -- the rows of the grid
  have grid : ∀ i, i < nv → HRow tr t w0 nv i := by
    intro i
    induction i with
    | zero => intro _; exact H0
    | succ i ih =>
      intro hi
      have C := row_walk hD h1 h64 hn (by omega) (ih (by omega)) (nv - 1) (by omega)
      obtain ⟨hw, hc, ha, hb, hic⟩ := C
      have hnn : cv tr t (w0 + 2 * nv + i * (nv + 1) + 1 + (nv - 1)) nn = nv := hic.2.trans hn
      have he := e1_cell hD hw hc (by omega) (by omega) (by omega)
      rw [hb, hnn, if_pos rfl] at he
      have he2 := e2_cell hD hw hc (by omega) (by omega) (by omega)
      rw [ha, hnn, if_neg (by omega)] at he2
      obtain ⟨hw1, g1, a1, t1, n1⟩ := cell_rowend hD hw hc he he2 (by omega)
      unfold HRow
      rw [show w0 + 2 * nv + (i + 1) * (nv + 1) = w0 + 2 * nv + i * (nv + 1) + 1 + (nv - 1) + 1 by
        have := hdr_succ nv i h1; omega]
      exact ⟨hw1, g1, by rw [a1, ha], hic.step t1 n1⟩
  have cells : ∀ i j, i < nv → j < nv → CRow tr t w0 nv i j :=
    fun i j hi hj => row_walk hD h1 h64 hn hi (grid i hi) j hj
  -- the end
  obtain ⟨hw, hc, ha, hb, hic⟩ := cells (nv - 1) (nv - 1) (by omega) (by omega)
  have hnn : cv tr t (w0 + 2 * nv + (nv - 1) * (nv + 1) + 1 + (nv - 1)) nn = nv := hic.2.trans hn
  have he := e1_cell hD hw hc (by omega) (by omega) (by omega)
  rw [hb, hnn, if_pos rfl] at he
  have he2 := e2_cell hD hw hc (by omega) (by omega) (by omega)
  rw [ha, hnn, if_pos rfl] at he2
  obtain ⟨heI, hw1, hnext⟩ := cell_end hD hw hc he he2
  have hl := blen_last h1
  have e0 : w0 + 2 * nv + (nv - 1) * (nv + 1) + 1 + (nv - 1) = w0 + blen nv - 1 := by omega
  have e1' : w0 + 2 * nv + (nv - 1) * (nv + 1) + 1 + (nv - 1) + 1 = w0 + blen nv := by omega
  rw [e0] at heI
  rw [e1'] at hw1 hnext
  refine ⟨sides, grid, cells, heI, hw1, fun ha => ?_⟩
  obtain ⟨s1, sd1, a1, kp1⟩ := hnext ha
  exact ⟨hw1, s1, sd1, a1, kp1⟩

/-- **The row at an offset of a section.** -/
theorem decode {w0 nv w : Nat} (h1 : 1 ≤ nv) (hlo : w0 ≤ w) (hhi : w < w0 + blen nv) :
    (∃ sd x, sd < 2 ∧ x < nv ∧ w = w0 + sd * nv + x) ∨
      (∃ i, i < nv ∧ w = w0 + 2 * nv + i * (nv + 1)) ∨
      (∃ i j, i < nv ∧ j < nv ∧ w = w0 + 2 * nv + i * (nv + 1) + 1 + j) := by
  by_cases hs0 : w < w0 + nv
  · exact Or.inl ⟨0, w - w0, by omega, by omega, by omega⟩
  by_cases hs1 : w < w0 + 2 * nv
  · exact Or.inl ⟨1, w - w0 - nv, by omega, by omega, by omega⟩
  right
  have hb : w - w0 - 2 * nv < nv * (nv + 1) := by unfold blen at hhi; omega
  have hdm := Nat.div_add_mod (w - w0 - 2 * nv) (nv + 1)
  have hi : (w - w0 - 2 * nv) / (nv + 1) < nv := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hb
  have hm := Nat.mod_lt (w - w0 - 2 * nv) (show 0 < nv + 1 by omega)
  have hc : (w - w0 - 2 * nv) / (nv + 1) * (nv + 1) = (nv + 1) * ((w - w0 - 2 * nv) / (nv + 1)) :=
    Nat.mul_comm _ _
  by_cases h0 : (w - w0 - 2 * nv) % (nv + 1) = 0
  · exact Or.inl ⟨(w - w0 - 2 * nv) / (nv + 1), hi, by omega⟩
  · exact Or.inr ⟨(w - w0 - 2 * nv) / (nv + 1), (w - w0 - 2 * nv) % (nv + 1) - 1, hi, by omega, by omega⟩

/-! ## Every distribute row lies in a section -/

/-- Row 0, when a shard row, is a start. -/
theorem first_start (hD : DLocal tr t pub) (h0 : 0 < tr.height t) (hs : cv tr t 0 kSh = 1) :
    Start tr t 0 := by
  have lt := fun x => cv_lt (tr := tr) (t := t) 0 x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD h0 (e := mul3 .isFirst (c kSh) (c side)) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD h0 (e := mul3 .isFirst (c kSh) (c a)) (by simp [constraints, cKind])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD h0 (e := mul3 .isFirst (c kSh) (c kp)) (by simp [constraints, cKind])
  dz c1 [zev_isFirst, hs]; dz c2 [zev_isFirst, hs]; dz c3 [zev_isFirst, hs]
  simp only [tenv, if_pos] at c1 c2 c3
  push_cast at c1 c2 c3
  have := lt side; have := lt a; have := lt kp
  exact ⟨h0, hs, by omega, by omega, by omega⟩

/-- After a request row, a shard row is a start; headers and cells cannot follow. -/
theorem after_scan (hD : DLocal tr t pub) {v : Nat} (hv : v + 1 < tr.height t) (hk : cv tr t v kS = 1) :
    cv tr t (v + 1) kGH = 0 ∧ cv tr t (v + 1) kC = 0 ∧
      (cv tr t (v + 1) kSh = 1 → Start tr t (v + 1)) := by
  have hv0 : v < tr.height t := by omega
  have lt1 := fun x => cv_lt (tr := tr) (t := t) (v + 1) x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hv0 (e := .mul (c kS) (n kGH)) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hv0 (e := .mul (c kS) (n kC)) (by simp [constraints, cKind])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hv0 (e := mul3 (c kS) (n kSh) (n side)) (by simp [constraints, cKind])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hv0 (e := mul3 (c kS) (n kSh) (n a)) (by simp [constraints, cKind])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hv0 (e := mul3 (c kS) (n kSh) (n kp)) (by simp [constraints, cKind])
  dz c1 [nxt_cv hv, hk]; dz c2 [nxt_cv hv, hk]
  push_cast at c1 c2
  have := lt1 kGH; have := lt1 kC
  refine ⟨by omega, by omega, fun hs => ?_⟩
  dz c3 [nxt_cv hv, hk, hs]; dz c4 [nxt_cv hv, hk, hs]; dz c5 [nxt_cv hv, hk, hs]
  push_cast at c3 c4 c5
  have := lt1 side; have := lt1 a; have := lt1 kp
  exact ⟨hv, hs, by omega, by omega, by omega⟩

/-- **Every distribute row lies in the section of a start row** (given `1 ≤ nn ≤ 64` on shard
rows). -/
theorem cover (hL : Local ScanDist.constraints tr t pub)
    (hN : ∀ w, w < tr.height t → cv tr t w kSh = 1 → 1 ≤ cv tr t w nn ∧ cv tr t w nn ≤ 64) :
    ∀ w, w < tr.height t → (cv tr t w kSh = 1 ∨ cv tr t w kGH = 1 ∨ cv tr t w kC = 1) →
      ∃ w0, Start tr t w0 ∧ w0 ≤ w ∧ w < w0 + blen (cv tr t w0 nn) := by
  have hD := DLocal.of_sd hL
  have hS := Scan.SLocal.of_sd hL
  have bl : ∀ w0, Start tr t w0 → 1 ≤ blen (cv tr t w0 nn) := fun w0 h => by
    have := (hN w0 h.1 h.2.1).1; unfold blen; omega
  intro w
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro hw hd
    have K := kinds hD hw
    rcases w with _ | v
    · -- row 0
      have ha : cv tr t 0 act = 1 := by omega
      rcases Scan.row_first hS hw ha with hp | hs
      · exfalso; simp only [Scan.kP] at hp; omega
      · have st := first_start hD hw hs
        exact ⟨0, st, Nat.le_refl _, by have := bl 0 st; omega⟩
    have hv0 : v < tr.height t := by omega
    have K0 := kinds hD hv0
    by_cases ha0 : cv tr t v act = 0
    · have := Scan.row_pad hS hw ha0
      simp only [Scan.act] at this; omega
    by_cases hp : cv tr t v kP = 1
    · have h1 := (Scan.row_param hS hv0 hp).2.2.2.1
      have h2 := Scan.fQ_le_kS hS hw h1
      simp only [Scan.kS] at h2; omega
    by_cases hk : cv tr t v kS = 1
    · obtain ⟨g0, c0, st⟩ := after_scan hD hw hk
      have hs : cv tr t (v + 1) kSh = 1 := by omega
      have st' := st hs
      exact ⟨v + 1, st', Nat.le_refl _, by have := bl _ st'; omega⟩
    have hdv : cv tr t v kSh = 1 ∨ cv tr t v kGH = 1 ∨ cv tr t v kC = 1 := by omega
    obtain ⟨w0, st, hlo, hhi⟩ := ih v (by omega) hv0 hdv
    by_cases hin : v + 1 < w0 + blen (cv tr t w0 nn)
    · exact ⟨w0, st, by omega, hin⟩
    · have hN0 := hN w0 st.1 st.2.1
      obtain ⟨-, -, -, -, hlt, hnext⟩ := block hD st rfl hN0.1 hN0.2
      have e : w0 + blen (cv tr t w0 nn) = v + 1 := by omega
      rw [e] at hnext
      have st' := hnext (by omega)
      exact ⟨v + 1, st', Nat.le_refl _, by have := bl _ st'; omega⟩

end

end ZkFormal.NearV3.Sched.Dist

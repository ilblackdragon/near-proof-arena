import ZkFormal.NearV3.Sched.View.CodecBlock

/-!
# ZkFormal.NearV3.Sched.View.CodecLink — the allowance field and the per-link pass of `schV3`

Record `k` of an instance block (`codec_block`) occupies rows `w … w + 23`, `w = f + 5 + 24k`;
its allowance bytes are rows `w + 16 … w + 23`, the comparator / `A0` row is `w + 18` (byte 2),
the record end `w + 23` (`rend`).

* `alw_walk`: `ap` at the end = the three low pre allowance bytes (LE), `bF` = some higher pre
  byte nonzero; `afin` = the three low post bytes, the higher post bytes are 0; the received
  `(apR, bigR)` and the comparator bit `cb` of byte 2 reach the end; the record data
  `al, gb, srcC, hasC, useC` is the same on all 24 rows; `hasC = 0 ⇒ apR = bigR = 0`.
* **`codec_link`**: given the comparator's answer `cb = [MA ≤ apR + fair]` (the link layer gets
  it from `cmp_sound` on the byte-2 `SCMP` message) and `apR + fair < P`:
  `a1 = bigR ? MA : min(apR + fair, MA)`, `g2 = al·base`, `a2 + al·base ≡ a1` (`a2 = a1 − al·base`
  when `al·base ≤ a1`).
* `codec_rec_msgs`: the record's messages — `SDG` at the start, `SA0` receive / `SCMP` at byte 2,
  `INIT` (`SOP`), `FIN` (`SFIN`), `SA0` send and, in instance 0, the forwarding `SCMP` / `SPUBB`
  at the end; the `SDL` delay line on the 16 id bytes.
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## Row lemmas -/

theorem nat_mod_of {a b : Nat} {q : Int} (h : (a : Int) = b + 2013265921 * q) (ha : a < 2013265921) :
    a = b % 2013265921 := by
  omega

/-- The receiver field's last row starts the allowance accumulators. -/
theorem alw_init (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r fR = 1)
    (he : cv tr t r e7 = 1) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) ap = 0 ∧ cv tr t (r + 1) big = 0 ∧
      cv tr t (r + 1) apost = 0 ∧ cv tr t (r + 1) wt = 1 ∧ cv tr t (r + 1) lowf = 1 := by
  have K := kinds hL hr
  have hr1 := act_next hL hr (by omega)
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c e7) (c fR) (n ap)) (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c e7) (c fR) (n big)) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := mul3 (c e7) (c fR) (n apost)) (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := mul3 (c e7) (c fR) (sub (n wt) (k 1))) (by simp [constraints, cRec])
  obtain ⟨q5, c5⟩ := zd hL hr (e := mul3 (c e7) (c fR) (sub (n lowf) (k 1))) (by simp [constraints, cRec])
  zs c1 [nx hr1, hk, he]; zs c2 [nx hr1, hk, he]; zs c3 [nx hr1, hk, he]; zs c4 [nx hr1, hk, he]
  zs c5 [nx hr1, hk, he]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have := l ap; have := l big; have := l apost; have := l wt; have := l lowf
  exact ⟨hr1, by omega, by omega, by omega, by omega, by omega⟩

/-- An allowance row: `lowf, nzb` bits, `nzb = [bpre ≠ 0]`, `bpost = 0` past the low bytes. -/
theorem alw_row (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hA : cv tr t r fA = 1) :
    cv tr t r lowf ≤ 1 ∧ cv tr t r nzb ≤ 1 ∧ (cv tr t r nzb = 1 ↔ cv tr t r bpre ≠ 0) ∧
      (cv tr t r lowf = 0 → cv tr t r bpost = 0) := by
  have K := kinds hL hr
  have hk : cv tr t r kR = 1 := by omega
  have bl := rbool_of hL hr hk (x := lowf) (by simp [recBoolCols])
  have bn := rbool_of hL hr hk (x := nzb) (by simp [recBoolCols])
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c fA) (notE (c lowf)) (c bpost)) (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (c fA) (sub (c nzb) (.mul (c bpre) (c ib))))
    (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (c fA) (.mul (c bpre) (notE (c nzb))))
    (by simp [constraints, cRec])
  zs c1 [hA]; zs c2 [hA]; zs c3 [hA]
  have l := fun x => lt (tr := tr) (t := t) r x
  have := l bpost; have := l bpre
  refine ⟨bl, bn, ?_, fun h => by rw [h] at c1; omega⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 bn with h | h <;> rw [h] at c2 c3
  · constructor
    · intro h'; omega
    · intro h'; exfalso; apply h'; omega
  · constructor
    · intro _ h0; rw [h0] at c2; omega
    · intro _; exact h

/-- **Allowance step** (`fA`, not the record end). -/
theorem alw_next (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hA : cv tr t r fA = 1)
    (hrd : cv tr t r rend = 0) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) wt = (256 * cv tr t r wt) % 2013265921 ∧
      (cv tr t r lowf = 1 →
        cv tr t (r + 1) ap = (cv tr t r ap + cv tr t r wt * cv tr t r bpre) % 2013265921 ∧
        cv tr t (r + 1) apost = (cv tr t r apost + cv tr t r wt * cv tr t r bpost) % 2013265921 ∧
        cv tr t (r + 1) big = cv tr t r big ∧ cv tr t (r + 1) lowf = 1 - cv tr t r e2) ∧
      (cv tr t r lowf = 0 →
        cv tr t (r + 1) ap = cv tr t r ap ∧ cv tr t (r + 1) apost = cv tr t r apost ∧
        (cv tr t r big ≤ 1 → cv tr t (r + 1) big = max (cv tr t r big) (cv tr t r nzb)) ∧
        cv tr t (r + 1) lowf = 0 ∧ cv tr t (r + 1) apR = cv tr t r apR ∧
        cv tr t (r + 1) bigR = cv tr t r bigR ∧ cv tr t (r + 1) cb = cv tr t r cb) := by
  have K := kinds hL hr
  have hr1 := act_next hL hr (by omega)
  obtain ⟨bl, bn, -, -⟩ := alw_row hL hr hA
  have b2 := bool_of hL hr (x := e2) (by simp [boolCols])
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (sub (n ap) (.add (c ap) (mul3 (c lowf) (c wt) (c bpre)))))
    (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (sub (n apost) (.add (c apost) (mul3 (c lowf) (c wt) (c bpost)))))
    (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (sub (n big) (.add (c big) (mul3 (notE (c big)) (notE (c lowf)) (c nzb)))))
    (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (sub (n wt) (smul 256 (c wt))))
    (by simp [constraints, cRec])
  obtain ⟨q5, c5⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (sub (n lowf) (.mul (c lowf) (notE (c e2)))))
    (by simp [constraints, cRec])
  obtain ⟨q6, c6⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (.mul (notE (c lowf)) (sub (n apR) (c apR))))
    (by simp [constraints, cRec])
  obtain ⟨q7, c7⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (.mul (notE (c lowf)) (sub (n bigR) (c bigR))))
    (by simp [constraints, cRec])
  obtain ⟨q8, c8⟩ := zd hL hr (e := .mul (sub (c fA) (c rend)) (.mul (notE (c lowf)) (sub (n cb) (c cb))))
    (by simp [constraints, cRec])
  zs c1 [nx hr1, hA, hrd]; zs c2 [nx hr1, hA, hrd]; zs c3 [nx hr1, hA, hrd]
  zs c4 [nx hr1, hA, hrd]; zs c5 [nx hr1, hA, hrd]; zs c6 [nx hr1, hA, hrd]
  zs c7 [nx hr1, hA, hrd]; zs c8 [nx hr1, hA, hrd]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have l0 := fun x => lt (tr := tr) (t := t) r x
  have := l ap; have := l apost; have := l big; have := l wt; have := l lowf; have := l apR
  have := l bigR; have := l cb
  have := l0 ap; have := l0 apost; have := l0 wt; have := l0 apR; have := l0 bigR; have := l0 cb
  have := l0 big
  refine ⟨hr1, by omega, fun h => ?_, fun h => ?_⟩
  · rw [h] at c1 c2 c3 c5
    push_cast at c1 c2
    simp only [Int.one_mul, Int.sub_zero] at c1 c2
    refine ⟨nat_mod_of (q := q1) (by push_cast; omega) (l ap),
      nat_mod_of (q := q2) (by push_cast; omega) (l apost), by omega, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 b2 with h' | h' <;> rw [h'] at c5 ⊢ <;> omega
  · rw [h] at c1 c2 c3 c5 c6 c7 c8
    refine ⟨by omega, by omega, fun hb => ?_, by omega, by omega, by omega, by omega⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h' | h' <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 bn with h'' | h'' <;> rw [h', h''] at c3 ⊢ <;>
      simp <;> omega

/-- **Byte 2 of the allowance** (`e2`): the received source allowance (zero without a source),
the comparator operands, carried to the next row. -/
theorem b2_row (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hA : cv tr t r fA = 1)
    (he : cv tr t r e2 = 1) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) apR = cv tr t r apR ∧
      cv tr t (r + 1) bigR = cv tr t r bigR ∧ cv tr t (r + 1) cb = cv tr t r cb ∧
      (cv tr t r hasC = 0 → cv tr t r apR = 0 ∧ cv tr t r bigR = 0) ∧
      cv tr t r a0g = cv tr t r hasC ∧ cv tr t r hasC ≤ 1 ∧
      cv tr t r cx = (cv tr t r apR + cv tr t r fair) % 2013265921 ∧ cv tr t r cy = MA ∧
      cv tr t r cbit = cv tr t r cb ∧ cv tr t r cg = 1 ∧ cv tr t r rend = 0 := by
  have K := kinds hL hr
  have hk : cv tr t r kR = 1 := by omega
  have hr1 := act_next hL hr (by omega)
  have hg := ((e2_iff hL hr).1 hA).1 he
  have h7 : cv tr t r e7 = 0 := by
    have E := (e7_iff hL hr).1 hk
    have := bool_of hL hr (x := e7) (by simp [boolCols])
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
    · exact h
    · have := E.1 h; omega
  have hrd : cv tr t r rend = 0 := by rw [rend_eq hL hr, h7, Nat.mul_zero]
  have bh := rbool_of hL hr hk (x := hasC) (by simp [recBoolCols])
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c fA) (c e2) (sub (n apR) (c apR))) (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c fA) (c e2) (sub (n bigR) (c bigR))) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := mul3 (c fA) (c e2) (sub (n cb) (c cb))) (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := .mul (.mul (c fA) (c e2)) (.mul (notE (c hasC)) (c apR)))
    (by simp [constraints, cRec])
  obtain ⟨q5, c5⟩ := zd hL hr (e := .mul (.mul (c fA) (c e2)) (.mul (notE (c hasC)) (c bigR)))
    (by simp [constraints, cRec])
  obtain ⟨q6, c6⟩ := zd hL hr (e := sub (c a0g) (mul3 (c fA) (c e2) (c hasC))) (by simp [constraints, cRec])
  obtain ⟨q7, c7⟩ := zd hL hr (e := mul3 (c fA) (c e2) (sub (c cx) (.add (c apR) (c fair))))
    (by simp [constraints, cRec])
  obtain ⟨q8, c8⟩ := zd hL hr (e := mul3 (c fA) (c e2) (sub (c cy) (k MA))) (by simp [constraints, cRec])
  obtain ⟨q9, c9⟩ := zd hL hr (e := mul3 (c fA) (c e2) (sub (c cbit) (c cb))) (by simp [constraints, cRec])
  obtain ⟨q10, c10⟩ := zd hL hr (e := sub (c fwg) (.mul (c rend) (c zt))) (by simp [constraints, cRec])
  obtain ⟨q11, c11⟩ := zd hL hr (e := sub (c cg) (.add (.mul (c fA) (c e2)) (c fwg))) (by simp [constraints, cRec])
  zs c1 [nx hr1, hA, he]; zs c2 [nx hr1, hA, he]; zs c3 [nx hr1, hA, he]; zs c4 [hA, he]
  zs c5 [hA, he]; zs c6 [hA, he]; zs c7 [hA, he]; zs c8 [hA, he, MA]; zs c9 [hA, he]
  zs c10 [hrd]; zs c11 [hA, he]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have l0 := fun x => lt (tr := tr) (t := t) r x
  have := l apR; have := l bigR; have := l cb; have := l0 apR; have := l0 bigR; have := l0 cb
  have := l0 a0g; have := l0 hasC; have := l0 cx; have := l0 fair; have := l0 cy; have := l0 cbit
  have := l0 fwg; have := l0 cg
  refine ⟨hr1, by omega, by omega, by omega, fun h => ?_, by omega, bh, by omega, by unfold MA; omega,
    by omega, by omega, hrd⟩
  rw [h] at c4 c5; omega

/-- **Record end** (`rend`). -/
theorem rend_row (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hrd : cv tr t r rend = 1) :
    cv tr t r fA = 1 ∧ cv tr t r e7 = 1 ∧
      (cv tr t r big ≤ 1 → cv tr t r bF = max (cv tr t r big) (cv tr t r nzb)) ∧
      cv tr t r al ≤ 1 ∧ cv tr t r cb ≤ 1 ∧ cv tr t r bigR ≤ 1 ∧
      (cv tr t r bigR = 1 → cv tr t r a1 = MA) ∧
      (cv tr t r bigR = 0 → cv tr t r cb = 1 → cv tr t r a1 = MA) ∧
      (cv tr t r bigR = 0 → cv tr t r cb = 0 →
        cv tr t r a1 = (cv tr t r apR + cv tr t r fair) % 2013265921) ∧
      (cv tr t r al = 0 → cv tr t r a2 = cv tr t r a1 ∧ cv tr t r g2 = 0) ∧
      (cv tr t r al = 1 → (cv tr t r a2 + cv tr t r base) % 2013265921 = cv tr t r a1 ∧
        cv tr t r g2 = cv tr t r base) ∧
      cv tr t r apost = cv tr t r afin ∧ cv tr t r u0g = cv tr t r useC ∧
      cv tr t r fwg = cv tr t r zt ∧ cv tr t r cg = cv tr t r zt ∧
      (cv tr t r zt = 1 → cv tr t r cx = (cv tr t r gfin + cv tr t r gb) % 2013265921 ∧
        cv tr t r cy = (cv tr t r (fb 0) + 256 * cv tr t r (fb 1) + 65536 * cv tr t r (fb 2)) %
          2013265921 ∧
        cv tr t r cbit = 1 ∧ cv tr t r pm0 = cv tr t r klo ∧ cv tr t r pm1 = cv tr t r khi) := by
  have K := kinds hL hr
  have hre := rend_eq hL hr
  have b7 := bool_of hL hr (x := e7) (by simp [boolCols])
  have hA : cv tr t r fA = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.2.2.2.2.2.2.2.1 with h | h
    · rw [h, Nat.zero_mul] at hre; omega
    · exact h
  have h7 : cv tr t r e7 = 1 := by rw [hA, Nat.one_mul] at hre; omega
  have hk : cv tr t r kR = 1 := by omega
  have he2 : cv tr t r e2 = 0 := by
    have E := (e2_iff hL hr).1 hA
    have := bool_of hL hr (x := e2) (by simp [boolCols])
    have hg := ((e7_iff hL hr).1 hk).1 h7
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
    · exact h
    · have := E.1 h; omega
  have ba := rbool_of hL hr hk (x := al) (by simp [recBoolCols])
  have bc := rbool_of hL hr hk (x := cb) (by simp [recBoolCols])
  have bg := rbool_of hL hr hk (x := bigR) (by simp [recBoolCols])
  have bn := rbool_of hL hr hk (x := nzb) (by simp [recBoolCols])
  have bz := bool_of hL hr (x := zt) (by simp [boolCols])
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (c rend) (sub (c bF) (.add (c big) (.mul (notE (c big)) (c nzb)))))
    (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (c rend) (sub (c a1) (.add (smul MA (c bigR))
      (.mul (notE (c bigR)) (.add (smul MA (c cb)) (.mul (notE (c cb)) (.add (c apR) (c fair))))))))
    (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (c rend) (sub (c a2) (sub (c a1) (.mul (c al) (c base)))))
    (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := .mul (c rend) (sub (c g2) (.mul (c al) (c base))))
    (by simp [constraints, cRec])
  obtain ⟨q5, c5⟩ := zd hL hr (e := .mul (c rend) (sub (c apost) (c afin))) (by simp [constraints, cRec])
  obtain ⟨q6, c6⟩ := zd hL hr (e := sub (c fwg) (.mul (c rend) (c zt))) (by simp [constraints, cRec])
  obtain ⟨q7, c7⟩ := zd hL hr (e := .mul (c fwg) (sub (c cx) (.add (c gfin) (c gb))))
    (by simp [constraints, cRec])
  obtain ⟨q8, c8⟩ := zd hL hr (e := .mul (c fwg) (sub (c cy) ftE)) (by simp [constraints, cRec])
  obtain ⟨q9, c9⟩ := zd hL hr (e := .mul (c fwg) (sub (c cbit) (k 1))) (by simp [constraints, cRec])
  obtain ⟨q10, c10⟩ := zd hL hr (e := sub (c cg) (.add (.mul (c fA) (c e2)) (c fwg)))
    (by simp [constraints, cRec])
  obtain ⟨q11, c11⟩ := zd hL hr (e := sub (c u0g) (.mul (c rend) (c useC))) (by simp [constraints, cRec])
  obtain ⟨q12, c12⟩ := zd hL hr (e := .mul (c fwg) (sub (c pm0) (c klo))) (by simp [constraints, cTrl])
  obtain ⟨q13, c13⟩ := zd hL hr (e := .mul (c fwg) (sub (c pm1) (c khi))) (by simp [constraints, cTrl])
  zs c1 [hrd]; zs c2 [hrd, MA]; zs c3 [hrd]; zs c4 [hrd]; zs c5 [hrd]; zs c6 [hrd]
  zs c10 [hA, he2]; zs c11 [hrd]; zs c7 []; zs c8 []; zs c9 []; zs c12 []; zs c13 []
  have l0 := fun x => lt (tr := tr) (t := t) r x
  have := l0 bF; have := l0 big; have := l0 a1; have := l0 apR; have := l0 fair; have := l0 a2
  have := l0 base; have := l0 g2; have := l0 apost; have := l0 afin; have := l0 fwg; have := l0 cg
  have := l0 u0g; have := l0 useC; have := l0 cx; have := l0 gfin; have := l0 gb; have := l0 cy
  have := l0 (fb 0); have := l0 (fb 1); have := l0 (fb 2); have := l0 cbit; have := l0 pm0
  have := l0 pm1; have := l0 klo; have := l0 khi
  have hfw : cv tr t r fwg = cv tr t r zt := by omega
  refine ⟨hA, h7, fun hb => ?_, ba, bc, bg, fun h => ?_, fun h h' => ?_, fun h h' => ?_,
    fun h => ?_, fun h => ?_, by omega, by omega, hfw, by omega, fun h => ?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h' | h' <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 bn with h'' | h'' <;> rw [h', h''] at c1 ⊢ <;>
      simp <;> omega
  · rw [h] at c2; unfold MA; omega
  · rw [h, h'] at c2; unfold MA; omega
  · rw [h, h'] at c2; omega
  · rw [h] at c3 c4; omega
  · rw [h] at c3 c4; omega
  · rw [hfw, h] at c7 c8 c9 c12 c13
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## The allowance field of a record -/

/-- **Allowance walk.** -/
theorem alw_walk (hL : CLocal tr t pub) {f k : Nat} (hR : ∀ o, o < 24 → RRow tr t f k o) :
    cv tr t (f + 5 + 24 * k + 23) ap = cv tr t (f + 5 + 24 * k + 16) bpre +
        256 * cv tr t (f + 5 + 24 * k + 17) bpre + 65536 * cv tr t (f + 5 + 24 * k + 18) bpre ∧
      cv tr t (f + 5 + 24 * k + 23) bF =
        (if cv tr t (f + 5 + 24 * k + 19) bpre = 0 ∧ cv tr t (f + 5 + 24 * k + 20) bpre = 0 ∧
            cv tr t (f + 5 + 24 * k + 21) bpre = 0 ∧ cv tr t (f + 5 + 24 * k + 22) bpre = 0 ∧
            cv tr t (f + 5 + 24 * k + 23) bpre = 0 then 0 else 1) ∧
      cv tr t (f + 5 + 24 * k + 23) afin = cv tr t (f + 5 + 24 * k + 16) bpost +
        256 * cv tr t (f + 5 + 24 * k + 17) bpost + 65536 * cv tr t (f + 5 + 24 * k + 18) bpost ∧
      (∀ o, 19 ≤ o → o < 24 → cv tr t (f + 5 + 24 * k + o) bpost = 0) ∧
      cv tr t (f + 5 + 24 * k + 23) apR = cv tr t (f + 5 + 24 * k + 18) apR ∧
      cv tr t (f + 5 + 24 * k + 23) bigR = cv tr t (f + 5 + 24 * k + 18) bigR ∧
      cv tr t (f + 5 + 24 * k + 23) cb = cv tr t (f + 5 + 24 * k + 18) cb := by
  -- per-row facts
  have F := fun o (ho : o < 24) => rrow_flags hL (hR o ho) ho
  have W := fun o (ho : o < 24) => (hR o ho).1
  have By := fun o (ho : o < 24) => bytes hL (W o ho) (by
    have := kinds hL (W o ho); have := (hR o ho).2.1; omega)
  generalize f + 5 + 24 * k = w at F W By
  have fA_ : ∀ o, 16 ≤ o → o < 24 → cv tr t (w + o) fA = 1 := fun o h1 h2 => by
    rw [(F o h2).2.2.1, if_pos h1]
  have rd : ∀ o, 16 ≤ o → o < 23 → cv tr t (w + o) rend = 0 := fun o h1 h2 => by
    rw [(F o (by omega)).2.2.2.2.1, if_neg (by omega)]
  have e2_ : ∀ o, 16 ≤ o → o < 23 → o ≠ 18 → cv tr t (w + o) e2 = 0 := fun o h1 h2 h3 => by
    rw [(F o (by omega)).2.2.2.2.2, if_neg h3]
  -- row 15 → 16
  have hR15 : cv tr t (w + 15) fR = 1 := by rw [(F 15 (by omega)).2.1]; rfl
  have h715 : cv tr t (w + 15) e7 = 1 := by rw [(F 15 (by omega)).2.2.2.1]; rfl
  obtain ⟨-, ap16, big16, apo16, wt16, lf16⟩ := alw_init hL (W 15 (by omega)) hR15 h715
  -- 16 → 17 → 18 → 19
  obtain ⟨-, wt17, L16, -⟩ := alw_next hL (W 16 (by omega)) (fA_ 16 (by omega) (by omega)) (rd 16 (by omega) (by omega))
  obtain ⟨ap17, apo17, big17, lf17⟩ := L16 lf16
  rw [e2_ 16 (by omega) (by omega) (by omega)] at lf17
  obtain ⟨-, wt18, L17, -⟩ := alw_next hL (W 17 (by omega)) (fA_ 17 (by omega) (by omega)) (rd 17 (by omega) (by omega))
  obtain ⟨ap18, apo18, big18, lf18⟩ := L17 lf17
  rw [e2_ 17 (by omega) (by omega) (by omega)] at lf18
  have e218 : cv tr t (w + 18) e2 = 1 := by rw [(F 18 (by omega)).2.2.2.2.2]; rfl
  obtain ⟨-, apR19, bigR19, cb19, -⟩ := b2_row hL (W 18 (by omega)) (fA_ 18 (by omega) (by omega)) e218
  obtain ⟨-, -, L18, -⟩ := alw_next hL (W 18 (by omega)) (fA_ 18 (by omega) (by omega)) (rd 18 (by omega) (by omega))
  obtain ⟨ap19, apo19, big19, lf19⟩ := L18 lf18
  rw [e218] at lf19
  -- 19 … 23: lowf = 0
  have AR := fun o (h16 : 16 ≤ o) (ho : o < 24) => alw_row hL (W o ho) (fA_ o h16 ho)
  obtain ⟨-, -, -, L19⟩ := alw_next hL (W 19 (by omega)) (fA_ 19 (by omega) (by omega)) (rd 19 (by omega) (by omega))
  obtain ⟨ap20, apo20, B19, lf20, apR20, bigR20, cb20⟩ := L19 lf19
  obtain ⟨-, -, -, L20⟩ := alw_next hL (W 20 (by omega)) (fA_ 20 (by omega) (by omega)) (rd 20 (by omega) (by omega))
  obtain ⟨ap21, apo21, B20, lf21, apR21, bigR21, cb21⟩ := L20 lf20
  obtain ⟨-, -, -, L21⟩ := alw_next hL (W 21 (by omega)) (fA_ 21 (by omega) (by omega)) (rd 21 (by omega) (by omega))
  obtain ⟨ap22, apo22, B21, lf22, apR22, bigR22, cb22⟩ := L21 lf21
  obtain ⟨-, -, -, L22⟩ := alw_next hL (W 22 (by omega)) (fA_ 22 (by omega) (by omega)) (rd 22 (by omega) (by omega))
  obtain ⟨ap23, apo23, B22, lf23, apR23, bigR23, cb23⟩ := L22 lf22
  have hrd23 : cv tr t (w + 23) rend = 1 := by rw [(F 23 (by omega)).2.2.2.2.1]; rfl
  obtain ⟨-, -, hbF, -⟩ := rend_row hL (W 23 (by omega)) hrd23
  have apo_afin := (rend_row hL (W 23 (by omega)) hrd23).2.2.2.2.2.2.2.2.2.2.2.1
  -- normalize the row indices
  simp only [show w + 15 + 1 = w + 16 from rfl, show w + 16 + 1 = w + 17 from rfl,
    show w + 17 + 1 = w + 18 from rfl, show w + 18 + 1 = w + 19 from rfl,
    show w + 19 + 1 = w + 20 from rfl, show w + 20 + 1 = w + 21 from rfl,
    show w + 21 + 1 = w + 22 from rfl, show w + 22 + 1 = w + 23 from rfl] at *
  -- values
  have b16 := (By 16 (by omega)); have b17 := (By 17 (by omega)); have b18 := (By 18 (by omega))
  have wt17' : cv tr t (w + 17) wt = 256 := by rw [wt17, wt16]
  have wt18' : cv tr t (w + 18) wt = 65536 := by rw [wt18, wt17']
  have ap17' : cv tr t (w + 17) ap = cv tr t (w + 16) bpre := by rw [ap17, ap16, wt16]; omega
  have ap18' : cv tr t (w + 18) ap = cv tr t (w + 16) bpre + 256 * cv tr t (w + 17) bpre := by
    rw [ap18, ap17', wt17']; omega
  have ap19' : cv tr t (w + 19) ap = cv tr t (w + 16) bpre + 256 * cv tr t (w + 17) bpre +
      65536 * cv tr t (w + 18) bpre := by
    rw [ap19, ap18', wt18']; omega
  have apo17' : cv tr t (w + 17) apost = cv tr t (w + 16) bpost := by rw [apo17, apo16, wt16]; omega
  have apo18' : cv tr t (w + 18) apost = cv tr t (w + 16) bpost + 256 * cv tr t (w + 17) bpost := by
    rw [apo18, apo17', wt17']; omega
  have apo19' : cv tr t (w + 19) apost = cv tr t (w + 16) bpost + 256 * cv tr t (w + 17) bpost +
      65536 * cv tr t (w + 18) bpost := by
    rw [apo19, apo18', wt18']; omega
  have nz := fun o (ho : o < 24) (h16 : 16 ≤ o) => (AR o h16 ho).2.2.1
  have bn := fun o (ho : o < 24) (h16 : 16 ≤ o) => (AR o h16 ho).2.1
  have z0 := fun o (ho : o < 24) (h16 : 16 ≤ o) => (AR o h16 ho).2.2.2
  have big19' : cv tr t (w + 19) big = 0 := by rw [big19, big18, big17, big16]
  rw [big19'] at B19
  have b20 := B19 (by omega)
  have m2 : ∀ a b : Nat, a ≤ 1 → b ≤ 1 → max a b ≤ 1 := fun a b ha hb => Nat.max_le.2 ⟨ha, hb⟩
  have u20 : cv tr t (w + 20) big ≤ 1 := by rw [b20]; exact m2 _ _ (by omega) (bn 19 (by omega) (by omega))
  have b21 := B20 u20
  have u21 : cv tr t (w + 21) big ≤ 1 := by rw [b21]; exact m2 _ _ u20 (bn 20 (by omega) (by omega))
  have b22 := B21 u21
  have u22 : cv tr t (w + 22) big ≤ 1 := by rw [b22]; exact m2 _ _ u21 (bn 21 (by omega) (by omega))
  have b23 := B22 u22
  have u23 : cv tr t (w + 23) big ≤ 1 := by rw [b23]; exact m2 _ _ u22 (bn 22 (by omega) (by omega))
  have hbF' := hbF u23
  refine ⟨?_, ?_, ?_, fun o h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [ap23, ap22, ap21, ap20, ap19']
  · rw [hbF', b23, b22, b21, b20]
    have n19 := nz 19 (by omega) (by omega); have n20 := nz 20 (by omega) (by omega)
    have n21 := nz 21 (by omega) (by omega); have n22 := nz 22 (by omega) (by omega)
    have n23 := nz 23 (by omega) (by omega)
    have m19 := bn 19 (by omega) (by omega); have m20 := bn 20 (by omega) (by omega)
    have m21 := bn 21 (by omega) (by omega); have m22 := bn 22 (by omega) (by omega)
    have m23 := bn 23 (by omega) (by omega)
    split
    · next h =>
      obtain ⟨h19, h20, h21, h22, h23⟩ := h
      have : cv tr t (w + 19) nzb ≠ 1 := fun e => n19.1 e h19
      have : cv tr t (w + 20) nzb ≠ 1 := fun e => n20.1 e h20
      have : cv tr t (w + 21) nzb ≠ 1 := fun e => n21.1 e h21
      have : cv tr t (w + 22) nzb ≠ 1 := fun e => n22.1 e h22
      have : cv tr t (w + 23) nzb ≠ 1 := fun e => n23.1 e h23
      omega
    · next h =>
      have : cv tr t (w + 19) nzb = 1 ∨ cv tr t (w + 20) nzb = 1 ∨ cv tr t (w + 21) nzb = 1 ∨
          cv tr t (w + 22) nzb = 1 ∨ cv tr t (w + 23) nzb = 1 := by
        by_cases a : cv tr t (w + 19) bpre = 0
        · by_cases b : cv tr t (w + 20) bpre = 0
          · by_cases c' : cv tr t (w + 21) bpre = 0
            · by_cases d : cv tr t (w + 22) bpre = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (n23.2 (fun e => h ⟨a, b, c', d, e⟩)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (n22.2 d))))
            · exact Or.inr (Or.inr (Or.inl (n21.2 c')))
          · exact Or.inr (Or.inl (n20.2 b))
        · exact Or.inl (n19.2 a)
      omega
  · rw [← apo_afin, apo23, apo22, apo21, apo20, apo19']
  · rcases (by omega : o = 19 ∨ o = 20 ∨ o = 21 ∨ o = 22 ∨ o = 23) with h | h | h | h | h <;> subst h
    · exact z0 19 (by omega) (by omega) lf19
    · exact z0 20 (by omega) (by omega) lf20
    · exact z0 21 (by omega) (by omega) lf21
    · exact z0 22 (by omega) (by omega) lf22
    · exact z0 23 (by omega) (by omega) lf23
  · rw [apR23, apR22, apR21, apR20, apR19]
  · rw [bigR23, bigR22, bigR21, bigR20, bigR19]
  · rw [cb23, cb22, cb21, cb20, cb19]

end

end ZkFormal.NearV3.Sched.Codec

import ZkFormal.NearV3.Sched.View.Codec

/-!
# ZkFormal.NearV3.Sched.View.CodecStep — one-row steps of the codec table `schV3`

From `CLocal`, what the next row of a row of each kind is:

* header (`kH`): inside the header (`ehp = 0`) another header row, register shifted; at its end
  (`ehp = 1`) the first record row (`fS`, `kidx = 0`, `g = 0`, `rs`);
* record (`kR`): inside a field (`e7 = 0`) the same field, `g + 1`; at a field end (`e7 = 1`)
  sender → receiver → allowance with the same `kidx`, `g = 0`; at the record end (`rend`, the
  allowance field's end) the next record (`kidx + 1`, `rs`) unless it is the last one
  (`ekl`), then the first hash row (`sj = 0`, `dgg`);
* hash (`kZ`) and ash (`kA`): `sj + 1`, the digest register shifted on hash rows; after the
  32nd hash row the ash rows; after the last ash row padding or a new instance (`kF`).

The byte position advances on encoding rows and the instance constants are carried on every
active row but the last ash row (`Codec.pos_next`, `Codec.inst_next`).
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- **First row of an instance.** -/
theorem first_row (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hf : cv tr t r kF = 1) :
    cv tr t r kH = 1 ∧ cv tr t r pos = 0 ∧ cv tr t r (reg 0) = 0 ∧ cv tr t r (reg 3) = 0 ∧
      cv tr t r (reg 4) = 0 ∧
      cv tr t r NN = (cv tr t r (reg 1) + 256 * cv tr t r (reg 2)) % 2013265921 ∧
      cv tr t r NN = (cv tr t r nn * cv tr t r nn) % 2013265921 ∧
      cv tr t r base = (cv tr t r (reg 5) + 256 * cv tr t r (reg 6) + 65536 * cv tr t r (reg 7)) %
        2013265921 ∧
      cv tr t r fair = (cv tr t r (reg 8) + 256 * cv tr t r (reg 9) + 65536 * cv tr t r (reg 10)) %
        2013265921 := by
  have K := kinds hL hr
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (c kF) (c pos)) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (c kF) (c (reg 0))) (by simp [constraints, cKind])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (c kF) (c (reg 3))) (by simp [constraints, cKind])
  obtain ⟨q4, c4⟩ := zd hL hr (e := .mul (c kF) (c (reg 4))) (by simp [constraints, cKind])
  obtain ⟨q5, c5⟩ := zd hL hr (e := .mul (c kF) (sub (c NN) (.add (c (reg 1)) (smul 256 (c (reg 2))))))
    (by simp [constraints, cKind])
  obtain ⟨q6, c6⟩ := zd hL hr (e := .mul (c kF) (sub (c NN) (.mul (c nn) (c nn))))
    (by simp [constraints, cKind])
  obtain ⟨q7, c7⟩ := zd hL hr (e := .mul (c kF) (sub (c base) (.add (c (reg 5))
    (.add (smul 256 (c (reg 6))) (smul 65536 (c (reg 7))))))) (by simp [constraints, cKind])
  obtain ⟨q8, c8⟩ := zd hL hr (e := .mul (c kF) (sub (c fair) (.add (c (reg 8))
    (.add (smul 256 (c (reg 9))) (smul 65536 (c (reg 10))))))) (by simp [constraints, cKind])
  zs c1 [hf]; zs c2 [hf]; zs c3 [hf]; zs c4 [hf]; zs c5 [hf]; zs c6 [hf]; zs c7 [hf]; zs c8 [hf]
  have l := fun x => lt (tr := tr) (t := t) r x
  have := l pos; have := l (reg 0); have := l (reg 3); have := l (reg 4); have := l NN
  have := l (reg 1); have := l (reg 2); have := l base; have := l fair
  have := l (reg 5); have := l (reg 6); have := l (reg 7); have := l (reg 8); have := l (reg 9)
  have := l (reg 10)
  have hnn : ((cv tr t r nn * cv tr t r nn : Nat) : Int) = (cv tr t r nn : Int) * cv tr t r nn := by
    push_cast; rfl
  rw [← hnn] at c6
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **Header row**: `bpost` is the register head, `bpre = pres·bpost`. -/
theorem hdr_row (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kH = 1) :
    cv tr t r bpost = cv tr t r (reg 0) ∧
      cv tr t r bpre = (if cv tr t r pres = 1 then cv tr t r bpost else 0) := by
  have K := kinds hL hr
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (c kH) (sub (c bpost) (c (reg 0)))) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (c kH) (sub (c bpre) (.mul (c pres) (c bpost))))
    (by simp [constraints, cKind])
  zs c1 [hk]; zs c2 [hk]
  have l := fun x => lt (tr := tr) (t := t) r x
  have := l bpost; have := l (reg 0); have := l bpre
  refine ⟨by omega, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.2.2.2.2.2.2.2.2.1 with h | h <;> rw [h] at c2 ⊢ <;>
    simp <;> omega

/-- **Header step** (`ehp = 0`). -/
theorem hdr_step (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kH = 1)
    (he : cv tr t r ehp = 0) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) kH = 1 ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r ∧
      ∀ i, i < 31 → cv tr t (r + 1) (reg i) = cv tr t r (reg (i + 1)) := by
  have K := kinds hL hr
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c kH) (notE (c ehp)) (notE (n kH))) (by simp [constraints, cKind])
  zs c1 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) kH
  refine ⟨hr1, by omega, hpos, hic, fun i hi => ?_⟩
  obtain ⟨q2, c2⟩ := zd hL hr (mem_hshift hi)
  zs c2 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) (reg i); have := lt (tr := tr) (t := t) r (reg (i + 1))
  omega

/-- **Header end** (`ehp = 1`): the first record row. -/
theorem hdr_end (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kH = 1)
    (he : cv tr t r ehp = 1) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) kR = 1 ∧ cv tr t (r + 1) fS = 1 ∧
      cv tr t (r + 1) g = 0 ∧ cv tr t (r + 1) kidx = 0 ∧ cv tr t (r + 1) rs = 1 ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  have K1 := kinds hL hr1
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (c ehp) (notE (n fS))) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (c ehp) (n kidx)) (by simp [constraints, cKind])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (c ehp) (n g)) (by simp [constraints, cKind])
  obtain ⟨q4, c4⟩ := zd hL hr (e := .mul (c ehp) (notE (n rs))) (by simp [constraints, cKind])
  zs c1 [nx hr1, he]; zs c2 [nx hr1, he]; zs c3 [nx hr1, he]; zs c4 [nx hr1, he]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have := l fS; have := l kidx; have := l g; have := l rs
  refine ⟨hr1, by omega, by omega, by omega, by omega, by omega, hpos, hic⟩

/-- `rend = fA·e7`. -/
theorem rend_eq (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    cv tr t r rend = cv tr t r fA * cv tr t r e7 := by
  have K := kinds hL hr
  have hb := bool_of hL hr (x := e7) (by simp [boolCols])
  have hb' := bool_of hL hr (x := rend) (by simp [boolCols])
  obtain ⟨q, c1⟩ := zd hL hr (e := sub (c rend) (.mul (c fA) (c e7))) (by simp [constraints, cRec])
  zs c1 []
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.2.2.2.2.2.2.2.1 with h | h <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h' | h' <;> rw [h, h'] at c1 ⊢ <;> omega

/-- **Inside a field** (`e7 = 0`). -/
theorem kr_mid (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kR = 1)
    (he : cv tr t r e7 = 0) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) kR = 1 ∧
      cv tr t (r + 1) g = (cv tr t r g + 1) % 2013265921 ∧
      cv tr t (r + 1) fS = cv tr t r fS ∧ cv tr t (r + 1) fR = cv tr t r fR ∧
      cv tr t (r + 1) fA = cv tr t r fA ∧ cv tr t (r + 1) kidx = cv tr t r kidx ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  have K1 := kinds hL hr1
  have hc : ∀ x ∈ [fS, fR, fA, kidx], cv tr t (r + 1) x = cv tr t r x := by
    intro x hx
    have hm : mul3 (c kR) (notE (c e7)) (sub (n x) (c x)) ∈ constraints := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [constraints, cRec]
    obtain ⟨q, c1⟩ := zd hL hr hm
    zs c1 [nx hr1, hk, he]
    have := lt (tr := tr) (t := t) (r + 1) x; have := lt (tr := tr) (t := t) r x
    omega
  obtain ⟨q, c1⟩ := zd hL hr (e := mul3 (c kR) (notE (c e7)) (sub (n g) (.add (c g) (k 1))))
    (by simp [constraints, cRec])
  zs c1 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) g; have := lt (tr := tr) (t := t) r g
  have e1 := hc fS (by simp); have e2 := hc fR (by simp); have e3 := hc fA (by simp)
  refine ⟨hr1, by omega, by omega, e1, e2, e3, hc kidx (by simp), hpos, hic⟩

/-- **Sender field end.** -/
theorem kr_endS (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r fS = 1)
    (he : cv tr t r e7 = 1) :
    cv tr t r rend = 0 ∧ r + 1 < tr.height t ∧ cv tr t (r + 1) kR = 1 ∧ cv tr t (r + 1) fR = 1 ∧
      cv tr t (r + 1) g = 0 ∧ cv tr t (r + 1) kidx = cv tr t r kidx ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  have hrd := rend_eq hL hr
  have hfA : cv tr t r fA = 0 := by omega
  rw [hfA, Nat.zero_mul] at hrd
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  have K1 := kinds hL hr1
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (sub (c e7) (.mul (c rend) (c ekl))) (n g))
    (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c e7) (c fS) (notE (n fR))) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := mul3 (c e7) (c fS) (sub (n kidx) (c kidx)))
    (by simp [constraints, cRec])
  zs c1 [nx hr1, he, hrd]; zs c2 [nx hr1, he, hk]; zs c3 [nx hr1, he, hk]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have := l g; have := l fR; have := l kidx; have := lt (tr := tr) (t := t) r kidx
  refine ⟨hrd, hr1, by omega, by omega, by omega, by omega, hpos, hic⟩

/-- **Receiver field end.** -/
theorem kr_endR (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r fR = 1)
    (he : cv tr t r e7 = 1) :
    cv tr t r rend = 0 ∧ r + 1 < tr.height t ∧ cv tr t (r + 1) kR = 1 ∧ cv tr t (r + 1) fA = 1 ∧
      cv tr t (r + 1) g = 0 ∧ cv tr t (r + 1) kidx = cv tr t r kidx ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  have hrd := rend_eq hL hr
  have hfA : cv tr t r fA = 0 := by omega
  rw [hfA, Nat.zero_mul] at hrd
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  have K1 := kinds hL hr1
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (sub (c e7) (.mul (c rend) (c ekl))) (n g))
    (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c e7) (c fR) (notE (n fA))) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := mul3 (c e7) (c fR) (sub (n kidx) (c kidx)))
    (by simp [constraints, cRec])
  zs c1 [nx hr1, he, hrd]; zs c2 [nx hr1, he, hk]; zs c3 [nx hr1, he, hk]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have := l g; have := l fA; have := l kidx; have := lt (tr := tr) (t := t) r kidx
  refine ⟨hrd, hr1, by omega, by omega, by omega, by omega, hpos, hic⟩

/-- **Record end, not the last record.** -/
theorem kr_endA (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r fA = 1)
    (he : cv tr t r e7 = 1) (hl : cv tr t r ekl = 0) :
    cv tr t r rend = 1 ∧ r + 1 < tr.height t ∧ cv tr t (r + 1) kR = 1 ∧ cv tr t (r + 1) fS = 1 ∧
      cv tr t (r + 1) g = 0 ∧ cv tr t (r + 1) kidx = (cv tr t r kidx + 1) % 2013265921 ∧
      cv tr t (r + 1) rs = 1 ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  have hrd := rend_eq hL hr
  rw [hk, he] at hrd
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  have K1 := kinds hL hr1
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (sub (c e7) (.mul (c rend) (c ekl))) (n g))
    (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c rend) (notE (c ekl)) (notE (n fS))) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := mul3 (c rend) (notE (c ekl)) (sub (n kidx) (.add (c kidx) (k 1))))
    (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := mul3 (c rend) (notE (c ekl)) (notE (n rs))) (by simp [constraints, cRec])
  zs c1 [nx hr1, he, hrd, hl]; zs c2 [nx hr1, hrd, hl]; zs c3 [nx hr1, hrd, hl]
  zs c4 [nx hr1, hrd, hl]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have := l g; have := l fS; have := l kidx; have := l rs; have := lt (tr := tr) (t := t) r kidx
  refine ⟨hrd, hr1, by omega, by omega, by omega, by omega, by omega, hpos, hic⟩

/-- **Last record end**: the first hash row. -/
theorem kr_endZ (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r fA = 1)
    (he : cv tr t r e7 = 1) (hl : cv tr t r ekl = 1) :
    cv tr t r rend = 1 ∧ r + 1 < tr.height t ∧ cv tr t (r + 1) kZ = 1 ∧ cv tr t (r + 1) sj = 0 ∧
      cv tr t (r + 1) dgg = 1 ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  have hrd := rend_eq hL hr
  rw [hk, he] at hrd
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inl (by omega))).2
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c rend) (c ekl) (notE (n kZ))) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := mul3 (c rend) (c ekl) (n sj)) (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := mul3 (c rend) (c ekl) (notE (n dgg))) (by simp [constraints, cRec])
  zs c2 [nx hr1, hrd, hl]; zs c3 [nx hr1, hrd, hl]; zs c4 [nx hr1, hrd, hl]
  have l := fun x => lt (tr := tr) (t := t) (r + 1) x
  have := l kZ; have := l sj; have := l dgg
  refine ⟨hrd, hr1, by omega, by omega, by omega, hpos, hic⟩

/-- `rs ⇒ fS ∧ g = 0`; `dgg ⇒ kZ ∧ sj = 0`. -/
theorem rs_dgg (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (cv tr t r rs = 1 → cv tr t r fS = 1 ∧ cv tr t r g = 0) ∧
      (cv tr t r dgg = 1 → cv tr t r kZ = 1 ∧ cv tr t r sj = 0) := by
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul (c rs) (notE (c fS))) (by simp [constraints, cRec])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul (c rs) (c g)) (by simp [constraints, cRec])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (c dgg) (notE (c kZ))) (by simp [constraints, cRec])
  obtain ⟨q4, c4⟩ := zd hL hr (e := .mul (c dgg) (c sj)) (by simp [constraints, cRec])
  zs c1 []; zs c2 []; zs c3 []; zs c4 []
  have l := fun x => lt (tr := tr) (t := t) r x
  have := l fS; have := l g; have := l kZ; have := l sj
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at c1 c2; omega
  · rw [h] at c3 c4; omega

/-- **Hash step** (`esj = 0`). -/
theorem z_step (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kZ = 1)
    (he : cv tr t r esj = 0) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) kZ = 1 ∧
      cv tr t (r + 1) sj = (cv tr t r sj + 1) % 2013265921 ∧
      cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 ∧ IC tr t (r + 1) r ∧
      ∀ i, i < 31 → cv tr t (r + 1) (reg i) = cv tr t r (reg (i + 1)) := by
  have K := kinds hL hr
  obtain ⟨hr1, hpos⟩ := pos_next hL hr (by omega)
  have hic := (inst_next hL hr (by omega) (Or.inr he)).2
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c kZ) (notE (c esj)) (notE (n kZ))) (by simp [constraints, cTrl])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c kZ) (notE (c esj)) (sub (n sj) (.add (c sj) (k 1))))
    (by simp [constraints, cTrl])
  zs c1 [nx hr1, hk, he]; zs c2 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) kZ; have := lt (tr := tr) (t := t) (r + 1) sj
  have := lt (tr := tr) (t := t) r sj
  refine ⟨hr1, by omega, by omega, hpos, hic, fun i hi => ?_⟩
  obtain ⟨q3, c3⟩ := zd hL hr (mem_zshift hi)
  zs c3 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) (reg i); have := lt (tr := tr) (t := t) r (reg (i + 1))
  omega

/-- **Hash end** (`esj = 1`): the first ash row. -/
theorem z_end (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kZ = 1)
    (he : cv tr t r esj = 1) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) kA = 1 ∧ cv tr t (r + 1) sj = 32 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  obtain ⟨hr1, hic⟩ := inst_next hL hr (by omega) (Or.inl (by omega))
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c kZ) (c esj) (notE (n kA))) (by simp [constraints, cTrl])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c kZ) (c esj) (sub (n sj) (k 32))) (by simp [constraints, cTrl])
  zs c1 [nx hr1, hk, he]; zs c2 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) kA; have := lt (tr := tr) (t := t) (r + 1) sj
  refine ⟨hr1, by omega, by omega, hic⟩

/-- **Ash step** (`esj = 0`). -/
theorem a_step (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kA = 1)
    (he : cv tr t r esj = 0) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) kA = 1 ∧
      cv tr t (r + 1) sj = (cv tr t r sj + 1) % 2013265921 ∧ IC tr t (r + 1) r := by
  have K := kinds hL hr
  obtain ⟨hr1, hic⟩ := inst_next hL hr (by omega) (Or.inr he)
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c kA) (notE (c esj)) (notE (n kA))) (by simp [constraints, cTrl])
  obtain ⟨q2, c2⟩ := zd hL hr (e := mul3 (c kA) (notE (c esj)) (sub (n sj) (.add (c sj) (k 1))))
    (by simp [constraints, cTrl])
  zs c1 [nx hr1, hk, he]; zs c2 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) (r + 1) kA; have := lt (tr := tr) (t := t) (r + 1) sj
  have := lt (tr := tr) (t := t) r sj
  refine ⟨hr1, by omega, by omega, hic⟩

/-- **Last ash row**: padding or a new instance next. -/
theorem a_end (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kA = 1)
    (he : cv tr t r esj = 1) :
    r + 1 < tr.height t ∧ (cv tr t (r + 1) act = 0 ∨ cv tr t (r + 1) kF = 1) := by
  have K := kinds hL hr
  have hr1 := act_next hL hr (by omega)
  have K1 := kinds hL hr1
  obtain ⟨q1, c1⟩ := zd hL hr (e := mul3 (c kA) (c esj) (.mul (n act) (notE (n kF))))
    (by simp [constraints, cKind])
  zs c1 [nx hr1, hk, he]
  refine ⟨hr1, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K1.1 with h | h <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K1.2.2.2.2.2.1 with h' | h' <;> rw [h, h'] at c1 <;> omega

end

end ZkFormal.NearV3.Sched.Codec

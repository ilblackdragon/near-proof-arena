import ZkFormal.NearV3.Extract.Ups.UpsKey

/-!
# ZkFormal.NearV3.Extract.Ups.UpsTerm — the moved key's length (M7e, step 3)

Which of `ESx0` / `ESx1` (`xs ≠ []` / `xs = []`) a split extension is, read off the parts:

* **`mveLong`**: a shortened extension (`MVE`) keeps a non-empty key, `I + 1 < |k|`: with `I + 1 = |k|` its node
  would be `.ext []`, whose `hplen` byte `1` forces `nokey`, hence `qodd = 1` (`pf·kMVE·nokey·(1 − qodd) = 0`),
  and the flag byte `16·qodd + …` could not be the empty key's `0`;
* **`esx1Len`**: an `ESx1` split branch's extension has `|k| = I + 1`: `2·phk + podd = I + 3`
  (`pf·xcp·(…)`), with `phk = |hp(k)|` read on its first bitmap row and `podd = |k| mod 2` from byte 5.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem rowsB_get (s : UpsSeg) (r0 n d : Nat) (hd : d < n) : (rowsB s r0 n).getD d 0 = s.row (r0 + d) b := by
  simp [rowsB, List.getD_eq_getElem?_getD, hd]

theorem extNil_bytes (c : NearSpec.PTrie) (m : Nat) (hc : c.hashOf.length = 32) :
    ((nodeEnc (.ext [] c m)).map UInt8.toNat).getD 1 0 = 1 ∧ ((nodeEnc (.ext [] c m)).map UInt8.toNat).getD 5 0 = 0 := by
  simp [nodeEnc, NearSpec.hexPrefix, NearSpec.packNibbles, toNats_u32, List.getD_eq_getElem?_getD]

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **A shortened extension keeps a non-empty key.** -/
theorem mveLong (k : Nat) (hk : k < ps.length) (hkd : kd k = 7) (key : List Nat) (cc : NearSpec.PTrie) (m : Nat)
    (hc : cc.hashOf.length = 32)
    (hrows : rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qMVE key cc m ti)).map UInt8.toNat)
    (hI : ti + 1 ≤ key.length) : ti + 1 < key.length := by
  apply Classical.byContradiction; intro hne
  have he : key.drop (ti + 1) = [] := by simp; omega
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  rw [hkd] at K
  generalize ps[k].1 = o at K U hrows
  generalize ps[k].2 = ℓ at K U hrows
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  have hte := (head_MVE ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd).2.2.1
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  obtain ⟨hℓ, hnk, -, -, ⟨U1, s1⟩, KR, -⟩ := extShape hw hs U hte hq0 K.pf
  have hsc := hL.segc
  -- the node's bytes 1 and 5
  have hE : UpsSpec.qMVE key cc m ti = .ext [] cc (NearSpec.extOwnMem [] + (m - NearSpec.extOwnMem key)) := by
    simp [UpsSpec.qMVE, he]
  obtain ⟨n1, n5⟩ := extNil_bytes cc _ hc
  rw [← hE, ← hrows] at n1 n5
  rw [rowsB_get s o ℓ 1 (by omega)] at n1
  rw [rowsB_get s o ℓ 5 (by omega)] at n5
  -- `hplen = 1`
  have b1 : 1 = s.row o qhk := by
    have hl := congrArg List.length hrows
    rw [hE] at hl
    simp only [rowsB, List.length_map, List.length_range, nodeEnc, List.length_append,
      List.length_cons, List.length_nil, u32_length, u64_length, hc, UpsSpec.hp_len, List.length_nil] at hl
    omega
  have hnok : s.row o nokey = 1 := hnk.2 b1.symm
  simp only [← b1] at KR
  -- `qodd = 1`
  have f := factN ok0 (rowLt hw hs _) (nextLt hw hs _)
    (e := mul3 (c pf) (c kMVE) (.mul (c nokey) (not (c qodd)))) (memPlan (by simp [cPlan]))
  have hk7 : s.row o kMVE = 1 := I0.kd 7 (by omega)
  have hqo := partBoolN ok0 (rowLt hw hs _) K.pf (x := qodd) (by decide)
  nev_simp at f
  simp [K.pf, hk7, hnok] at f
  have hodd : s.row o qodd = 1 := by
    have := rowLt hw hs o qodd; rw [P_lit] at this
    rcases (show s.row o qodd = 0 ∨ s.row o qodd = 1 by omega) with h | h
    · simp [h] at f
    · exact h
  -- the flag byte
  have F5 := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at F5
  obtain ⟨oh5, st5, lt5, I5, pc5, -⟩ := F5
  have h5 := (stOf_inv oh5).2.2.1 st5
  have ok5 := okRow hw hs lt5
  have g := bHPFm ok5 (rowLt hw hs _) oh5.sum h5
  have a6 : s.row (o + 5) kMVL = 0 := I5.kd 6 (by omega)
  have a7 : s.row (o + 5) kMVE = 1 := I5.kd 7 (by omega)
  have bt := nibBits ok5 (rowLt hw hs _) (nextLt hw hs _) (by have := oh5.sum; have := oh5.bs; omega)
  have := bt 4 (by omega); have := bt 5 (by omega); have := bt 6 (by omega); have := bt 7 (by omega)
  rw [a6, a7, pc5 qtl (by decide), pc5 qodd (by decide), hodd, show s.row o qtl = 0 by omega] at g
  simp only [lb] at g
  have e : s.row (o + 5) b = 16 + (s.row (o + 5) (reg 4) + 2 * s.row (o + 5) (reg 5) +
      4 * s.row (o + 5) (reg 6) + 8 * s.row (o + 5) (reg 7)) :=
    natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by simp only [natCast_add, natCast_mul]; grind)
  omega


/-- **An `ESx1` split branch's extension has `|k| = I + 1`.** -/
theorem esx1Len (k : Nat) (hk : k < ps.length) (hkd : kd k = 10) (hX : spXN ci = 1) (Pb : Nat → List Nat)
    (hR : UpbReads s Pb)
    (key : List Nat) (hkl : key.length < 2^23) (h1 : (Pb (s.row ps[k].1 sN)).length = 45 + (key.length / 2 + 1))
    (h5 : (Pb (s.row ps[k].1 sN)).getD 5 0 / 16 = key.length % 2) : key.length = ti + 1 := by
  obtain ⟨n5, hpo, -, hq0'⟩ := tagNib5 hw hs hL hP Pb (fun i hi hr => (hR i hi hr).1) k hk (Or.inr (Or.inr ⟨hkd, hX⟩))
  have hqtl := hq0' (by omega)
  rw [h5, hqtl] at n5
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U0⟩ := hL.part k hk
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  obtain ⟨hc4, hc10⟩ := (termCase hw hs hL hP k hk (Or.inr hkd)).2 hkd
  rw [hkd] at K
  generalize ps[k].1 = o at K U h1 h5 n5 hpo hqtl
  generalize ps[k].2 = ℓ at K U
  have hsc := hL.segc
  obtain ⟨i1, i2, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨htl, hte, -, -, hx0, -⟩ := head_SPB ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd I0.cs hc4 hc10
  obtain ⟨c0, B⟩ := brLay hw hs hsc K U htl hte
  have hc0 : c0 = 3 ∨ c0 = 39 := by rcases B.c0v with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  -- `phk` on the first bitmap row
  obtain ⟨a1, a2, a3, a4, a5, a6, -, -, -, a10, -, a12⟩ := B.pre (c0 - 2) (by omega)
  have hok := okRow hw hs a2
  have hbm : s.row (o + (c0 - 2)) sBM = 1 := a10.2 (by omega)
  have hfs : s.row (o + (c0 - 2)) fs = 1 := a12 hbm (by omega)
  have hxc : s.row (o + (c0 - 2)) xcp = 1 := by rw [a4 xcp (by decide), hx0, hX]
  have hcp : s.row (o + (c0 - 2)) cp = 0 := cpZero hw hs (by
    rw [cpBM hok (rowLt hw hs _) a1.sum hbm, show s.row (o + (c0 - 2)) kRDB = 0 from a3.kd 0 (by omega),
      show s.row (o + (c0 - 2)) kRBR = 0 from a3.kd 3 (by omega), show s.row (o + (c0 - 2)) kRBV = 0 from a3.kd 4 (by omega),
      show s.row (o + (c0 - 2)) kRBI = 0 from a3.kd 5 (by omega)]; rfl)
  have hrd := rdBMx hok (rowLt hw hs _) (nextLt hw hs _) a5 hbm hfs hxc hcp
    (rdcOff hok (rowLt hw hs _) (nextLt hw hs _) a6) a1
  have hsp : s.row (o + (c0 - 2)) spos = 1 := by
    have f := pSB hok (rowLt hw hs _) a1.sum hrd hbm
    rw [show s.row (o + (c0 - 2)) kSPB = 1 from a3.kd 10 (by omega), cast1] at f
    exact natv (rowLt hw hs _ _) one_lt (by rw [cast1]; grind)
  have hphk : s.row o phk = key.length / 2 + 1 := by
    have f := rBM hok (rowLt hw hs _) a1.sum hbm hfs
    have hl := (hR _ a2 hrd).2
    rw [a4 sN (by decide), h1] at hl
    rw [hxc, cast1, hl, a4 qtl (by decide), htl, a4 phk (by decide)] at f
    apply natv (rowLt hw hs _ _) (by rw [P_lit]; omega)
    have he : ((45+(key.length/2+1):Nat):Fp)=45+((key.length/2+1:Nat):Fp) := by simp only [natCast_add]; rfl
    rw [he] at f
    grind
  -- `2·phk + podd = I + 3`
  have f := factN ok0 (rowLt hw hs _) (nextLt hw hs _)
    (e := .mul (c pf) (.mul (c xcp) (sub (.add (smul 2 (c phk)) (c podd)) (.add tIE (Dsl.k 3)))))
    (memPlan (by simp [cPlan]))
  have t1 : s.row o ti1 = if 1 = ti then 1 else 0 := I0.ti 1 (by omega)
  have t2 : s.row o ti2 = if 2 = ti then 1 else 0 := I0.ti 2 (by omega)
  have hxo : s.row o xcp = 1 := by rw [hx0, hX]
  simp only [tIE] at f
  nev_simp at f
  rw [K.pf, hxo, hphk, t1, t2] at f
  rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;> simp at f <;> omega

end

end ZkFormal.NearV3.UpsRows

import ZkFormal.NearV3.Extract.Ups.UpsTermT

/-!
# ZkFormal.NearV3.Extract.Ups.UpsCid — the child-id reads of the upper parts (M7e, step 3, upper chain)

An upper part (`RDB`, `RDE`, `PT`) reads, on the first row of its target window, the source record's window
child id (`rdc = fs·tgt·up`, `rcid = cN`); `UPB` then gives `rcid = ucid[spos]`, which `kidCidOk` pins to the real
child on a revealed window.  Here, the row facts:

* **`extCid`** (`RDE`, `PT`): the read is at `spos = 5 + Pb[1]` (byte 1 of the source is `|hp|`, copied on the
  `HPL` row);
* **`rdbCid`** (`RDB`): the part is `c0 + 32·w + 8` bytes (`c0 ∈ {3, 39}`), its `MEM` row reads `plen = c0 + 32·w + 8`,
  and (`w > 0`) the read is at `spos = c0 + 32·e*` with `e* = w − 1` for slot 15 (`sd = 1`), else `0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A window row that reads its child id and copies nothing is read. -/
theorem rdCH (hq : C qb = 1) (hch : C sCH = 1) (hoh : OneHot C) (hcp : C cp = 0) (hrdc : C rdc = 1) :
    C rd = 1 := by
  have f := factN ok hC hD (e := .mul (c qb) (sub (c rd) (.add (c cp) (sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF)), c rdc])))) (memBytes (by simp [cBytes]))
  have hS := hoh.sum
  have hb := hoh.bs
  have hz : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sMEM = 0 := by
    omega
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have := hC rd
  simp only [P_lit] at *
  simp only [sumc, kM, List.map_cons, List.map_nil] at f
  nev_simp at f
  simp [hq, hcp, hrdc, z0, z1, z2, z3, z4, z5, z6, z7] at f
  omega

end

theorem zero_ltP : (0 : Nat) < P := by have := P_gt; omega

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The child-id read of an extension descend / pass-through.** -/
theorem extCid (k : Nat) (hk : k < ps.length) (hkd : kd k = 1 ∨ kd k = 11) (hup : s.row ps[k].1 UpsV3.up = 1)
    (Pb : Nat → List Nat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0) :
    ∃ i, i < s.rows.length ∧ s.row i rd = 1 ∧ s.row i sN = s.row ps[k].1 sN ∧
      s.row i spos = 5 + le256 ((List.range 4).map (fun j => (Pb (s.row ps[k].1 sN)).getD (1+j) 0)) ∧ s.row i rcid = s.row ps[k].1 cN := by
  have cH := copiedHpl hw hs hL hP Pb hR k hk hkd
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  generalize hkk : kd k = ki at K hkd
  generalize ps[k].1 = o at K U hup cH ⊢
  generalize ps[k].2 = ℓ at K U ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, i5, i6⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  have hte : s.row o qte = 1 := by
    rcases hkd with rfl | rfl
    · exact (head_RDE ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd).2.2.1
    · exact (head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd).2.2.1
  obtain ⟨hℓ, -, -, -, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, -⟩ := extShape hw hs U hte hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ KR U3 s3
  subst hℓ
  have hle := K.le
  have hq : le256 ((List.range 4).map (fun j => (Pb (s.row o sN)).getD (1+j) 0))=q := by
    rw [hqq] at cH
    rw [cH,u32Bytes_value (by have := rowLt hw hs o qhk; rw [hqq,P_lit] at this; omega)]
  -- the window's first row
  have FC := kField hw hs hsc K U3 s3 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at FC
  obtain ⟨ohW, stW, ltW, ixW, pcW, qbW⟩ := FC
  have hch : s.row (o + 5 + q) sCH = 1 := (stOf_inv ohW).2.2.2.2.2.2.2.1 stW
  have okW := okRow hw hs ltW
  have sl := kSel hw hs hsc K (r := o + 5 + q) (by omega) (by omega)
  have R := winRole okW (rowLt hw hs _) (nextLt hw hs _) ixW i1 i4 i5 i6 hch sl.2.2.2.2.1 sl.2.2.2.2.2 sl.2.1
  obtain ⟨Rt, -, Rw, -, -, -, Rd, Rc⟩ := R
  have hwfr : s.row (o + 5 + q) wfr = 1 := Rw (by omega)
  have hs15 : s15V ki (sdx k) si = 0 := by
    unfold s15V; rcases hkd with rfl | rfl <;> simp [kdOf, UKind.all, b2n]
  -- `fw = 1`: the row before is `HPF` or `KEY`
  have hprev : s.row (o + 4 + q) sCH = 0 := by
    have KP : OneHot (s.row (o + 4 + q)) ∧ stOf (s.row (o + 4 + q)) ≠ 7 := by
      rcases Nat.lt_or_ge 1 q with h | h
      · obtain ⟨Uk, sk⟩ := KR.key h
        have F := kField hw hs hsc K Uk sk (by omega) (by omega) (q - 2) (by omega)
        rw [show o + 5 + 1 + (q - 2) = o + 4 + q by omega] at F
        exact ⟨F.1, by rw [F.2.1]; decide⟩
      · have F := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by have := KR.pos; omega)
        rw [show o + 5 + 0 = o + 4 + q by have := KR.pos; omega] at F
        exact ⟨F.1, by rw [F.2.1]; decide⟩
    obtain ⟨oh, hst⟩ := KP
    have h7 := (stOf_one oh).2.2.2.2.2.2.2.1
    have := oh.bs
    rcases (show s.row (o + 4 + q) sCH = 0 ∨ s.row (o + 4 + q) sCH = 1 by omega) with h | h
    · exact h
    · exact absurd (h7 h) hst
  have hfw : s.row (o + 5 + q) fw = 1 := by
    have hlt : o + 4 + q + 1 < s.rows.length := by omega
    have := (winStep (okRow hw hs (i := o + 4 + q) (by omega)) (rowLt hw hs _) (nextLt hw hs _)).1 hprev
      (by rw [next_eq hw hs hlt, show o + 4 + q + 1 = o + 5 + q by omega]; exact hch)
    rwa [next_eq hw hs hlt, show o + 4 + q + 1 = o + 5 + q by omega] at this
  have htgt : s.row (o + 5 + q) tgt = 1 := by simp [Rt, hs15, hfw]
  have hfs : s.row (o + 5 + q) fs = 1 := by simpa using (U3.fs 0 (by omega)).2 rfl
  have hupW : s.row (o + 5 + q) UpsV3.up = 1 := by rw [pcW _ (by decide), hup]
  have hrdc : s.row (o + 5 + q) rdc = 1 := by rw [Rd, hfs, htgt, hupW]
  have hcp : s.row (o + 5 + q) cp = 0 := by
    apply natv (rowLt hw hs _ _) zero_ltP
    rw [cpCH okW (rowLt hw hs _) ohW.sum hch, hwfr]; simp only [cast0, cast1]; grind
  have hrd := rdCH okW (rowLt hw hs _) (nextLt hw hs _) qbW hch ohW hcp hrdc
  refine ⟨o + 5 + q, ltW, hrd, pcW sN (by decide), ?_, by rw [Rc hrdc, pcW cN (by decide)]⟩
  rw [dirRow okW (rowLt hw hs _) (nextLt hw hs _) ixW (by omega) hrd, hq,
    show o + 5 + q = o + (5 + q) by omega, (U.rows (5 + q) (by omega)).2.1]

/-- **The child-id read of a branch descend.** -/
theorem rdbCid (k : Nat) (hk : k < ps.length) (hkd : kd k = 0) (hup : s.row ps[k].1 UpsV3.up = 1) :
    ∃ c0 ww, (c0 = 3 ∨ c0 = 39) ∧
      (∃ i, i < s.rows.length ∧ s.row i rd = 1 ∧ s.row i sN = s.row ps[k].1 sN ∧
        s.row i plen = c0 + 32 * ww + 8) ∧
      (0 < ww → ∃ i, i < s.rows.length ∧ s.row i rd = 1 ∧ s.row i sN = s.row ps[k].1 sN ∧
        s.row i spos = c0 + 32 * (if sdx k = 1 then ww - 1 else 0) ∧ s.row i rcid = s.row ps[k].1 cN) := by
  have K := partK hw hs hL hP k hk
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  rw [hkd] at K
  generalize hsd : sdx k = sd at K ⊢
  generalize ps[k].1 = o at K U hup ⊢
  generalize ps[k].2 = ℓ at K U ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, isd⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨-, -, htl, hte, -⟩ := head_RDB ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨c0, B⟩ := brLay hw hs hsc K U htl hte
  have hℓ := B.len
  subst hℓ
  have hle := K.le
  have hc0 : c0 = 3 ∨ c0 = 39 := by rcases B.c0v with h | h <;> omega
  have hlen22 := lenLe hw hs
  -- the `MEM` read
  have hMEM0 := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at hMEM0
  have hm8 : s.row (o + c0 + 32 * ww) sMEM = 1 := (stOf_inv hMEM0.1).2.2.2.2.2.2.2.2 hMEM0.2.1
  have hrdM : s.row (o + (c0 + 32 * ww)) rd = 1 := by
    rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]
    exact rdMem (okRow hw hs hMEM0.2.2.1) (rowLt hw hs _) (nextLt hw hs _) hMEM0.2.2.2.2.2 hm8
      (hMEM0.2.2.2.1.kd 8 (by omega)) hMEM0.1
  have hpM := pMEM (okRow hw hs (i := o + (c0 + 32 * ww)) (by omega)) (rowLt hw hs _)
    (by rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; exact hMEM0.1.sum) hrdM
    (by rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; exact hm8)
  have hidx : s.row (o + (c0 + 32 * ww)) idx = 0 := by
    have := B.memU.1.idx 0 (by omega); rwa [show o + c0 + 32 * ww + 0 = o + (c0 + 32 * ww) by omega] at this
  have hsp0 : s.row (o + (c0 + 32 * ww)) spos = c0 + 32 * ww := by
    rw [dirRow (okRow hw hs (i := o + (c0 + 32 * ww)) (by omega)) (rowLt hw hs _) (nextLt hw hs _)
      (K.ix (c0 + 32 * ww) (by omega)) (by omega) hrdM, (U.rows (c0 + 32 * ww) (by omega)).2.1]
  rw [hidx, hsp0] at hpM
  have hplen : s.row (o + (c0 + 32 * ww)) plen = c0 + 32 * ww + 8 := by
    have e : ((c0 + 32 * ww + 8 : Nat) : Fp) = ((s.row (o + (c0 + 32 * ww)) plen : Nat) : Fp) := by
      rw [natCast_add]
      rw [cast0] at hpM
      grind
    exact (natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e).symm
  refine ⟨c0, ww, hc0, ⟨o + (c0 + 32 * ww), by omega, hrdM, K.pc _ (by omega) sN (by decide), hplen⟩, fun hww => ?_⟩
  -- the target window `e*`
  have WF := winFlags hw hs (r := o + c0) hww (by omega) (by omega)
    (by have := (B.pre (c0 - 1) (by omega)).2.2.2.2.2.1; rwa [show o + (c0 - 1) = o + c0 - 1 by omega] at this)
    (fun e he => ⟨(B.winU e he).1, fun d hd => by
      have := (B.win (32 * e + d) (by omega)).2.2.2.2.2; rwa [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at this⟩)
    hm8 (by have := hMEM0.1.bs; have := hMEM0.1.sum; omega)
  let es := if sd = 1 then ww - 1 else 0
  have hes : es < ww := by simp only [es]; split <;> omega
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * es) (by omega)
  have sl := kSel hw hs hsc K (r := o + c0 + 32 * es) (by omega) (by omega)
  have okE := okRow hw hs a2
  have R := winRole okE (rowLt hw hs _) (nextLt hw hs _) a3 i1 i4 (by omega) isd a6 sl.2.2.2.2.1
    sl.2.2.2.2.2 sl.2.1
  obtain ⟨Rt, Rw, -, -, -, -, Rd, Rc⟩ := R
  obtain ⟨f1, f2⟩ := WF es hes 0 (by omega)
  simp only [Nat.add_zero] at f1 f2
  rw [show o + c0 + 32 * es = o + c0 + 32 * es from rfl] at f1 f2
  have htgt : s.row (o + c0 + 32 * es) tgt = 1 := by
    rw [Rt, f1, f2]
    simp only [s15V, kdOf, UKind.all, b2n, es]
    by_cases h1 : sd = 1 <;> simp [h1] <;> omega
  have hwfr : s.row (o + c0 + 32 * es) wfr = 1 := by rw [Rw (Or.inl rfl), htgt]
  have hWe := B.winU es hes
  have hfs : s.row (o + c0 + 32 * es) fs = 1 := by simpa using (hWe.1.fs 0 (by omega)).2 rfl
  have hupW : s.row (o + c0 + 32 * es) UpsV3.up = 1 := by rw [a4 _ (by decide), hup]
  have hrdc : s.row (o + c0 + 32 * es) rdc = 1 := by rw [Rd, hfs, htgt, hupW]
  have hcp : s.row (o + c0 + 32 * es) cp = 0 := by
    apply natv (rowLt hw hs _ _) zero_ltP
    rw [cpCH okE (rowLt hw hs _) a1.sum a6, hwfr]; simp only [cast0, cast1]; grind
  have hrd := rdCH okE (rowLt hw hs _) (nextLt hw hs _) a5 a6 a1 hcp hrdc
  refine ⟨o + c0 + 32 * es, a2, hrd, a4 sN (by decide), ?_, by rw [Rc hrdc, a4 cN (by decide)]⟩
  rw [dirRow okE (rowLt hw hs _) (nextLt hw hs _) a3 (by omega) hrd,
    show o + c0 + 32 * es = o + (c0 + 32 * es) by omega, (U.rows (c0 + 32 * es) (by omega)).2.1]

end

end ZkFormal.NearV3.UpsRows

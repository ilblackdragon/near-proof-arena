import ZkFormal.NearV3.Extract.Ups.SpbRows

/-!
# ZkFormal.NearV3.Extract.Ups.SpbBytes — the split branch, `SPB` (layer 2)

A part of kind `SPB` (index 10) is the branch of a leaf or extension split, `qSPB ci src cx x si v`
(`SpbSpec`), case by case (`ci = 4 … 10`: `LSa LSb LSc ESl0 ESl1 ESn0 ESn1`):

* `TAG` is fresh: `2` with a value (`LSa LSb ESl0 ESl1`), else `1`;
* the value slot is the source leaf's (`LSa`: copied from `P[len − 44 …]`) or fresh `u32 L ‖ H(v)`;
* the bitmap bytes are the segment's `bmL`/`bmH`: `2^x` (unless `LSa`) `+ 2^y` (with a new leaf);
* windows in slot order (`y = 0` first, else `x` first): the new leaf's window is the `DIGEST` of
  the part below at length 50; the moved node's (`LSb LSc ESl0 ESn0`) is the `DIGEST` of part
  `j = 1` at `clen`; the old child's (`ESl1 ESn1`) is copied from `P[len − 40 …]`;
* `memory_usage = Kc + L + [LSa]·slen + [ESx1]·(m − (50 + 2·phk)) + [moved]·N_{Q_1}`.

Hypotheses: `UpbReads s Pb` with the source `nodeEnc src` (`< 2^20` bytes; for `LSa` a leaf with a
36-byte slot, `slen < 2^32`; for `ESl1`/`ESn1` an extension with a 32-byte child hash, `m < 2^64`,
`|k| < 400`); for `LSb LSc ESl0 ESn0` the `DIGEST` of part `1` at `clen` is `cx.hashOf` and the
`MEMD` limbs (`< 2^12`) have value `cx.memD`; with a new leaf, the `DIGEST` of the part below at 50
is `(qNLF si v).hashOf` and `x ≠ y` when there are two windows; `|v| = L` with `L`'s bytes `< 256` and
the value's `DIGEST`; the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- A terminal part of kind `SPB` belongs to a split case. -/
theorem spbCase : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∀ k, k < 4 →
    (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB = .SPB → 4 ≤ ci ∧ ci ≤ 10 := by decide

/-- A terminal part of kind `RBI` belongs to the case `BI`. -/
theorem rbiCase : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∀ k, k < 4 →
    (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB = .RBI → ci = 3 := by decide


section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- The first bitmap row of a split branch that keeps the old child reads (the source's `hplen`). -/
theorem rdBMx (hq : C qb = 1) (hbm : C sBM = 1) (hfs : C fs = 1) (hx : C xcp = 1) (hcp : C cp = 0)
    (hrdc : C rdc = 0) (hoh : OneHot C) : C rd = 1 := by
  have f := factN ok hC hD (e := .mul (c qb) (sub (c rd) (.add (c cp) (sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF)), c rdc])))) (memBytes (by simp [cBytes]))
  have hS := hoh.sum
  have hb := hoh.bs
  have := hC rd
  simp only [P_lit] at *
  simp only [sumc, kM, List.map_cons, List.map_nil] at f
  nev_simp at f
  have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
    omega
  simp [hq, hbm, hfs, hx, hcp, hrdc, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
    z.2.2.2.2.2.2.2] at f
  omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- The case of a part of kind `kd k ∈ {RBI, SPB}` (a terminal part). -/
theorem termCase (k : Nat) (hk : k < ps.length) (hkd : kd k = 5 ∨ kd k = 10) :
    (kd k = 5 → ci = 3) ∧ (kd k = 10 → 4 ≤ ci ∧ ci ≤ 10) := by
  have hkT : k < nTof ci ti := by
    rcases Nat.lt_or_ge k (nTof ci ti) with h | h
    · exact h
    · have := (hP.upper k hk h).1; omega
  have hT := (hP.term k hk hkT).1
  have h4 : k < 4 := by have := nTof_le ci hP.ix.1 ti hP.ix.2.1; omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at hT; exact rbiCase ci hP.ix.1 ti hP.ix.2.1 k h4 hT.symm
  · rw [h] at hT; exact spbCase ci hP.ix.1 ti hP.ix.2.1 k h4 hT.symm

/-- **RBI's terminal row** is `W1` or `W2` (`si ≤ 1`): the case is `BI`, and `sf·ts3·cBI = 0`. -/
theorem rbiSi (k : Nat) (hk : k < ps.length) (hkd : kd k = 5) : si ≤ 1 := by
  have hci := (termCase hw hs hL hP k hk (Or.inl hkd)).1 hkd
  obtain ⟨h4r, hsf, -⟩ := hL.walk
  obtain ⟨sc, -, -, sts⟩ := hP.seg 0 (by omega)
  have ok := okRow hw hs (i := 0) (by omega)
  have f := factN ok (rowLt hw hs _) (nextLt hw hs _)
    (e := mul3 (c sf) (c ts3) (sumc [cBI, cLSa, cLSc, cESn0, cESn1])) (memSeg (by simp [cSeg]))
  have c3 : s.row 0 cBI = 1 := by have := sc 3 (by omega); rw [if_pos hci.symm] at this; exact this
  have c4 : s.row 0 cLSa = 0 := by have := sc 4 (by omega); rw [if_neg (by omega)] at this; exact this
  have c6 : s.row 0 cLSc = 0 := by have := sc 6 (by omega); rw [if_neg (by omega)] at this; exact this
  have c9 : s.row 0 cESn0 = 0 := by have := sc 9 (by omega); rw [if_neg (by omega)] at this; exact this
  have c10 : s.row 0 cESn1 = 0 := by have := sc 10 (by omega); rw [if_neg (by omega)] at this; exact this
  have s3 : s.row 0 ts3 = if 2 = si then 1 else 0 := sts 2 (by omega)
  simp only [sumc, List.map_cons, List.map_nil] at f
  nev_simp at f
  simp only [hsf, c3, c4, c6, c9, c10, s3] at f
  have := hP.ix.2.2.2
  by_cases h : 2 = si
  · simp [h] at f
  · omega

set_option maxHeartbeats 16000000 in
/-- **A split branch** (`SPB`): its bytes are `nodeEnc (qSPB ci src cx x si v)` (`x = tX`). -/
theorem ups_spbBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 10) (val : NearSpec.Bytes)
    (Pb : Nat → List Nat) (hR : UpbReads s Pb) (src cx : NearSpec.PTrie)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc src).map UInt8.toNat)
    (hsl : (nodeEnc src).length < 2 ^ 20)
    (hsrcL : ci = 4 → ∃ key sl m, src = .leaf key sl m ∧ sl.valueRef.length = 36 ∧ sl.len < 2 ^ 32)
    (hsrcE : spXN ci = 1 → ∃ key c m, src = .ext key c m ∧ c.hashOf.length = 32 ∧ m < 2 ^ 64 ∧ key.length < 400)
    (hdC : spRN ci = 1 → ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 1 →
      s.row i dL = s.row ps[k].1 clen → regN (s.row i) = cx.hashOf.map UInt8.toNat)
    (hMd : spRN ci = 1 → ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv < 4096)
    (hmB : spRN ci = 1 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mBv) 8 = cx.memD)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hLb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hdig : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 0 →
      s.row i dL = val.length → regN (s.row i) = (NearSpec.sha256 val).map UInt8.toNat)
    (hdN : spYN ci = 1 → ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = 50 → regN (s.row i) = (UpsSpec.qNLF si val).hashOf.map UInt8.toNat)
    (hxy : spYN ci = 1 → ci ≠ 4 → s.row 0 tX ≠ UpsSpec.yOf si)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qSPB ci src cx (s.row 0 tX) si val)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qSPB ci src cx (s.row 0 tX) si val).memD := by
  have K := partK hw hs hL hP k hk
  have hup := upZero hw hs hL hP k hk (by omega)
  obtain ⟨hj, -⟩ := hL.part k hk
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  obtain ⟨hc4, hc10⟩ := (termCase hw hs hL hP k hk (Or.inr hkd)).2 hkd
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hsrc hup hdC hMd hmB hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte hMd hmB ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, isd⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨htl, hte, htb2, hnc, hx0, hv0, huA, hbN, hbL, hcO, hcS, hCc0, hCc, heL, heS, hKc, hjm⟩ :=
    head_SPB ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd I0.cs hc4 hc10
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  obtain ⟨sx, sv, stw, sy1, sy2⟩ := spSem ci i1 si i4
  -- `W0`: the bitmap
  obtain ⟨h4r, hsf, -⟩ := hL.walk
  obtain ⟨sc, -, -, sts⟩ := hP.seg 0 (by omega)
  obtain ⟨hx16, hbmL, hbmH, hsiY⟩ :=
    spbSeg (okRow hw hs (i := 0) (by omega)) (rowLt hw hs _) (nextLt hw hs _) hsf sc sts hc4 hc10 i4
  -- the layout
  obtain ⟨c0, B⟩ := brLay hw hs hsc K U htl hte
  have hℓ := B.len
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  have hc0 : c0 = 3 + 36 * spVN ci := by rcases B.c0v with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩ <;> omega
  have hspV : spVN ci ≤ 1 := by unfold spVN; split <;> omega
  have hww : 0 < ww := by
    rcases Nat.eq_zero_or_pos ww with h | h
    · exact absurd ((U.windows (by omega)).1 h) (by omega)
    · exact h
  have hMEM0 := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at hMEM0
  have hm8 : s.row (o + c0 + 32 * ww) sMEM = 1 := (stOf_inv hMEM0.1).2.2.2.2.2.2.2.2 hMEM0.2.1
  have WF := winFlags hw hs (r := o + c0) hww (by omega) (by omega)
    (by have := (B.pre (c0 - 1) (by omega)).2.2.2.2.2.1; rwa [show o + (c0 - 1) = o + c0 - 1 by omega] at this)
    (fun e he => ⟨(B.winU e he).1, fun d hd => by
      have := (B.win (32 * e + d) (by omega)).2.2.2.2.2; rwa [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at this⟩)
    hm8 (by have := hMEM0.1.bs; have := hMEM0.1.sum; omega)
  -- window roles
  have role : ∀ e, e < ww → ∀ d, d < 32 →
      s.row (o + c0 + 32 * e + d) wy = (if e = 0 then spY1V ci si 10 else spY2V ci si 10) ∧
      s.row (o + c0 + 32 * e + d) wfr + (1 - s.row (o + c0 + 32 * e + d) wy) * spXN ci = 1 ∧
      s.row (o + c0 + 32 * e + d) wn = s.row (o + c0 + 32 * e + d) wy ∧
      s.row (o + c0 + 32 * e + d) rdc = 0 ∧
      (e = 0 → (if e + 1 = ww then 1 else 0) + twoV ci = 1) ∧ (e ≠ 0 → e + 1 = ww) := by
    intro e he d hd
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * e + d) (by omega)
    rw [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at a1 a2 a3 a4 a5 a6
    have sl := kSel hw hs hsc K (r := o + c0 + 32 * e + d) (by omega) (by omega)
    have R := winRole (okRow hw hs a2) (rowLt hw hs _) (nextLt hw hs _) a3 i1 i4 (by omega) isd a6
      sl.2.2.2.2.1 sl.2.2.2.2.2 sl.2.1
    obtain ⟨f1, f2⟩ := WF e he d hd
    obtain ⟨S1, S2, S3, S4⟩ := R.2.2.2.2.1 rfl
    rw [sx] at S2
    refine ⟨?_, S2, ?_, ?_, fun h => ?_, fun h => ?_⟩
    · rw [S1, f1]; by_cases h : e = 0 <;> simp [h]
    · rw [R.2.2.2.2.2.1]; simp
    · rw [R.2.2.2.2.2.2.1, a4 UpsV3.up (by decide), hup, Nat.mul_zero]
    · rw [← f2]; exact S3 (by rw [f1, if_pos h])
    · have := S4 (by rw [f1, if_neg h]); rw [f2] at this; split at this <;> omega
  have hwwv : ww = 1 + twoV ci := by
    have r0 := (role 0 hww 0 (by omega)).2.2.2.2.1 rfl
    have ht2 : twoV ci ≤ 1 := by rw [stw]; split <;> omega
    by_cases h1 : 0 + 1 = ww
    · rw [if_pos h1] at r0; omega
    · rw [if_neg h1] at r0
      have r1 := (role 1 (by omega) 0 (by omega)).2.2.2.2.2 (by omega)
      omega
  have hlenP : (Pb (s.row o sN)).length = (nodeEnc src).length := by rw [hsrc, List.length_map]
  have hPb256 : ∀ i, (Pb (s.row o sN)).getD i 0 < 256 := by rw [hsrc]; exact toNats_lt _
  -- the windows: the new leaf's (fresh, `DIGEST (j − 1, 50)`)
  have winY : ∀ e, e < ww → (if e = 0 then spY1V ci si 10 else spY2V ci si 10) = 1 →
      rowsB s (o + c0 + 32 * e) 32 = (UpsSpec.qNLF si val).hashOf.map UInt8.toNat := by
    intro e he hyv
    have hY : spYN ci = 1 := by
      rw [sy1, sy2] at hyv; unfold spYN; split at hyv <;> split at hyv <;> simp_all <;> omega
    have hWe := B.winU e he
    have FC := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega)
    have chU : ∀ d, d < 32 → s.row (o + c0 + 32 * e + d) sCH = 1 ∧ s.row (o + c0 + 32 * e + d) wfr = 1 ∧
        s.row (o + c0 + 32 * e + d) wn = 1 := by
      intro d hd
      have F := FC d hd
      obtain ⟨r1, r2, r3, -⟩ := role e he d hd
      rw [hyv] at r1
      rw [r1] at r2 r3
      exact ⟨(stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1, by simpa using r2, r3⟩
    have eW := freshWin hw hs (r0 := o + c0 + 32 * e) (by omega)
      (fun d hd => Or.inr ⟨(chU d hd).1, (chU d hd).2.1, by have := (FC d hd).1.sum; have := (chU d hd).1; omega⟩)
      (fun d hd => feZero hw hs hsc K hWe.1 (by omega) d (by omega))
    have F0 := FC 0 (by omega)
    simp only [Nat.add_zero] at F0
    have c0' := chU 0 (by omega)
    simp only [Nat.add_zero] at c0'
    have hr3 : o + c0 + 32 * e < s.rows.length := by omega
    have hgD := gDrow (okRow hw hs hr3) (rowLt hw hs _) (nextLt hw hs _) F0.2.2.2.2.2
      (by simpa using (hWe.1.fs 0 (by omega)).2 rfl) (qbWt3 hw hs hr3 F0.2.2.2.2.2)
      (Or.inr ⟨c0'.1, c0'.2.1, by have := F0.1.sum; omega⟩)
    have hdI0 := dCHn (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2
    rw [F0.2.2.2.2.1 j (by decide), hj, hsc _ hr3 tau (by decide)] at hdI0
    have hdI : s.row (o + c0 + 32 * e) dI = upsIdN (s.row 0 tau) k := by
      apply dIj_nat (rowLt hw hs _ _)
      rw [hdI0, natCast_add, cast1]; grind
    have hdL : s.row (o + c0 + 32 * e) dL = 50 :=
      natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (dCHnl (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
    rw [eW, show (List.range 32).map (fun i => s.row (o + c0 + 32 * e) (reg i)) = regN (s.row (o + c0 + 32 * e)) from rfl]
    exact hdN hY _ hr3 hgD hdI hdL
  -- the moved node's window (fresh, `DIGEST (jm = 1, clen)`)
  have winC : ∀ e, e < ww → (if e = 0 then spY1V ci si 10 else spY2V ci si 10) = 0 → spRN ci = 1 →
      rowsB s (o + c0 + 32 * e) 32 = cx.hashOf.map UInt8.toNat := by
    intro e he hyv hR1
    have hX0 : spXN ci = 0 := by unfold spRN at hR1; unfold spXN; split at hR1 <;> split <;> omega
    have hWe := B.winU e he
    have FC := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega)
    have chU : ∀ d, d < 32 → s.row (o + c0 + 32 * e + d) sCH = 1 ∧ s.row (o + c0 + 32 * e + d) wfr = 1 ∧
        s.row (o + c0 + 32 * e + d) wn = 0 := by
      intro d hd
      have F := FC d hd
      obtain ⟨r1, r2, r3, -⟩ := role e he d hd
      rw [hyv] at r1
      rw [r1, hX0] at r2
      rw [r1] at r3
      exact ⟨(stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1, by simpa using r2, r3⟩
    have eW := freshWin hw hs (r0 := o + c0 + 32 * e) (by omega)
      (fun d hd => Or.inr ⟨(chU d hd).1, (chU d hd).2.1, by have := (FC d hd).1.sum; have := (chU d hd).1; omega⟩)
      (fun d hd => feZero hw hs hsc K hWe.1 (by omega) d (by omega))
    have F0 := FC 0 (by omega)
    simp only [Nat.add_zero] at F0
    have c0' := chU 0 (by omega)
    simp only [Nat.add_zero] at c0'
    have hr3 : o + c0 + 32 * e < s.rows.length := by omega
    have hgD := gDrow (okRow hw hs hr3) (rowLt hw hs _) (nextLt hw hs _) F0.2.2.2.2.2
      (by simpa using (hWe.1.fs 0 (by omega)).2 rfl) (qbWt3 hw hs hr3 F0.2.2.2.2.2)
      (Or.inr ⟨c0'.1, c0'.2.1, by have := F0.1.sum; omega⟩)
    have hdI := dIj_nat (rowLt hw hs _ _) (dCHm (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
    have hdL := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (dCHml (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
    rw [hsc _ hr3 tau (by decide), F0.2.2.2.2.1 jm (by decide), hjm hR1] at hdI
    rw [F0.2.2.2.2.1 clen (by decide)] at hdL
    rw [eW, show (List.range 32).map (fun i => s.row (o + c0 + 32 * e) (reg i)) = regN (s.row (o + c0 + 32 * e)) from rfl]
    exact hdC hR1 _ hr3 hgD hdI hdL
  -- the old child's window (copied from `P[len − 40 …]`)
  have winO : ∀ e, e < ww → (if e = 0 then spY1V ci si 10 else spY2V ci si 10) = 0 → spXN ci = 1 →
      40 ≤ (Pb (s.row o sN)).length →
      rowsB s (o + c0 + 32 * e) 32 = ((Pb (s.row o sN)).drop ((Pb (s.row o sN)).length - 40)).take 32 := by
    intro e he hyv hX1 h40
    apply copyRun hw hs Pb (fun i hi hrd => (hR i hi hrd).1) (by omega) (by omega)
    intro d hd
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * e + d) (by omega)
    rw [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at a1 a2 a3 a4 a5 a6
    obtain ⟨r1, r2, r3, r4, -⟩ := role e he d hd
    rw [hyv] at r1
    rw [r1, hX1] at r2
    have hok := okRow hw hs a2
    have hcp : s.row (o + c0 + 32 * e + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rw [cpCH hok (rowLt hw hs _) a1.sum a6, show s.row (o + c0 + 32 * e + d) wfr = 0 by omega]; rfl
    have hb1 := a1.bs; have hs1 := a1.sum
    have hrd := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) a5 hcp a1
      (fun h => by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega) r4
    have hpl := (hR _ a2 hrd).2
    rw [a4 sN (by decide)] at hpl
    have hidx : s.row (o + c0 + 32 * e + d) idx = d := (B.winU e he).1.idx d hd
    have f := pSC hok (rowLt hw hs _) a1.sum hrd a6
    rw [show s.row (o + c0 + 32 * e + d) kSPB = 1 from a3.kd 10 (by omega), cast1, hpl, hidx] at f
    refine ⟨hcp, hrd, by omega, ?_, a4 sN (by decide)⟩
    have := sub_of_cast (rowLt hw hs _ _) (by rw [P_lit]; omega) (show 40 ≤ (Pb (s.row o sN)).length + d by omega)
      (x := s.row (o + c0 + 32 * e + d) spos) (by rw [natCast_add]; grind)
    omega
  -- the bitmap rows: the segment's `bmL`, `bmH`
  have bmB : rowsB s (o + (c0 - 2)) 2 = [s.row 0 bmL, s.row 0 bmH] := by
    have row : ∀ t, t < 2 → s.row (o + (c0 - 2 + t)) b = (if t = 0 then s.row 0 bmL else s.row 0 bmH) := by
      intro t ht
      obtain ⟨a1, a2, a3, a4, a5, a6, -, -, -, a10, a11, a12⟩ := B.pre (c0 - 2 + t) (by omega)
      have hok := okRow hw hs a2
      have hbm : s.row (o + (c0 - 2 + t)) sBM = 1 := a10.2 (by omega)
      have f := bSPB hok (rowLt hw hs _) a1.sum hbm
      rw [show s.row (o + (c0 - 2 + t)) kSPB = 1 from a3.kd 10 (by omega), cast1, hsc _ a2 bmL (by decide),
        hsc _ a2 bmH (by decide)] at f
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · have hfs : s.row (o + (c0 - 2 + 0)) fs = 1 := a12 hbm (by omega)
        rw [hfs, cast1] at f
        exact natv (rowLt hw hs _ _) (rowLt hw hs _ _) (by grind)
      · have hfs : s.row (o + (c0 - 2 + 1)) fs = 0 := by
          rcases rowBool hok (rowLt hw hs _) (x := fs) (by decide) with h | h
          · exact h
          · exact absurd (a11 h hbm) (by omega)
        rw [hfs, cast0] at f
        exact natv (rowLt hw hs _ _) (rowLt hw hs _ _) (by grind)
    simp only [rowsB, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    rw [show o + (c0 - 2) + 0 = o + (c0 - 2 + 0) by omega, show o + (c0 - 2) + 1 = o + (c0 - 2 + 1) by omega,
      row 0 (by omega), row 1 (by omega)]
    rfl
  -- the tag
  have hT0 := B.pre 0 (by omega)
  simp only [Nat.add_zero] at hT0
  obtain ⟨t1, -, -, -, -, t6, -, -, t9, -, -, -⟩ := hT0
  have htag : s.row o b = 1 + spVN ci := by
    rw [(gramRow ok0 (rowLt hw hs _) (nextLt hw hs _) t1.sum).1 (t9.2 trivial) K.pf]; omega
  -- MEM: reads, and the bytes
  have FM := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega)
  have memRd : ∀ i, i < 8 → s.row (o + c0 + 32 * ww + i) rb < 256 ∧
      (8 ≤ (Pb (s.row o sN)).length →
        s.row (o + c0 + 32 * ww + i) rb = (Pb (s.row o sN)).getD ((Pb (s.row o sN)).length - 8 + i) 0) := by
    intro i hi
    have F := FM i hi
    have hm := (stOf_inv F.1).2.2.2.2.2.2.2.2 F.2.1
    have hrd := rdMem (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) F.2.2.2.2.2 hm (F.2.2.2.1.kd 8 (by omega)) F.1
    obtain ⟨hrb, hpl⟩ := hR _ F.2.2.1 hrd
    rw [F.2.2.2.2.1 sN (by decide)] at hrb hpl
    refine ⟨by rw [hrb]; exact hPb256 _, fun h8 => ?_⟩
    have f := pMEM (okRow hw hs F.2.2.1) (rowLt hw hs _) F.1.sum hrd hm
    rw [hpl, B.memU.1.idx i hi] at f
    have := sub_of_cast (rowLt hw hs _ _) (by rw [P_lit]; omega) (show 8 ≤ (Pb (s.row o sN)).length + i by omega)
      (x := s.row (o + c0 + 32 * ww + i) spos) (by rw [natCast_add]; grind)
    rw [hrb, this, show (Pb (s.row o sN)).length + i - 8 = (Pb (s.row o sN)).length - 8 + i by omega]
  have R5 := memRegs hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega)
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => (FM i hi).2.2.2.2.1 x hx
  obtain ⟨hL0, hL1, hL2⟩ := hLb
  have hX1 : spXN ci ≤ 1 := by unfold spXN; split <;> omega
  have hR1 : spRN ci ≤ 1 := by unfold spRN; split <;> omega
  have hE1 : (if ci = 4 then 1 else 0) ≤ 1 := by split <;> omega
  have hr0 : o + (c0 + 32 * ww + 8) - 8 = o + c0 + 32 * ww := by omega
  rw [hr0] at hMd hmB
  have eMgen : (ci = 4 → ∀ i, i < 4 → s.row (o + c0 + 32 * ww) (SR i) < 256) → s.row o Cc < 600 →
      rowsB s (o + c0 + 32 * ww) 8 = (NearSpec.u64 (spKc ci + (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) +
        (if ci = 4 then 1 else 0) * (s.row (o + c0 + 32 * ww) (SR 0) + 256 * s.row (o + c0 + 32 * ww) (SR 1) +
          65536 * s.row (o + c0 + 32 * ww) (SR 2) + 16777216 * s.row (o + c0 + 32 * ww) (SR 3)) +
        (spXN ci * limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 +
          spRN ci * limbs (fun i => s.row (o + c0 + 32 * ww + i) mBv) 8 - s.row o Cc))).map UInt8.toNat ∧
      limbs (fun i => s.row (o + c0 + 32 * ww + i) rx) 8 = (spKc ci + (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) +
        (if ci = 4 then 1 else 0) * (s.row (o + c0 + 32 * ww) (SR 0) + 256 * s.row (o + c0 + 32 * ww) (SR 1) +
          65536 * s.row (o + c0 + 32 * ww) (SR 2) + 16777216 * s.row (o + c0 + 32 * ww) (SR 3)) +
        (spXN ci * limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 +
          spRN ci * limbs (fun i => s.row (o + c0 + 32 * ww + i) mBv) 8 - s.row o Cc)) := by
    intro hSR hCcB
    obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U B.memU.1 B.memU.2 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
      (fun i hi => by
        have hfs : s.row (o + c0 + 32 * ww + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
        have hLbi : bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i < 256 := by
          simp only [bAt, List.getD_eq_getElem?_getD]
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i ≥ 3 by omega) with rfl | rfl | rfl | h
          · simpa using hL0
          · simpa using hL1
          · simpa using hL2
          · simp [List.getElem?_eq_none (show [s.row 0 L0, s.row 0 L1, s.row 0 L2].length ≤ i by simp; omega)]
        have hSbi : s.row o eS * bAt [s.row (o + c0 + 32 * ww) (SR 0), s.row (o + c0 + 32 * ww) (SR 1),
            s.row (o + c0 + 32 * ww) (SR 2), s.row (o + c0 + 32 * ww) (SR 3)] i < 256 := by
          rw [heS]
          by_cases h4 : ci = 4
          · rw [if_pos h4, Nat.one_mul]
            have := hSR h4
            simp only [bAt, List.getD_eq_getElem?_getD]
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i ≥ 4 by omega) with rfl | rfl | rfl | rfl | h
            · simpa using this 0 (by omega)
            · simpa using this 1 (by omega)
            · simpa using this 2 (by omega)
            · simpa using this 3 (by omega)
            · simp [List.getElem?_eq_none (show [s.row (o + c0 + 32 * ww) (SR 0), s.row (o + c0 + 32 * ww) (SR 1),
                s.row (o + c0 + 32 * ww) (SR 2), s.row (o + c0 + 32 * ww) (SR 3)].length ≤ i by simp; omega)]
          · rw [if_neg h4, Nat.zero_mul]; omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp only [inA, pc5 i hi useA (by decide), huA]
          have := (memRd i hi).1
          rcases (show spXN ci = 0 ∨ spXN ci = 1 by omega) with h | h <;> rw [h] <;> omega
        · simp only [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
          rcases (show spRN ci = 0 ∨ spRN ci = 1 by omega) with h | h <;> rw [h]
          · omega
          · have := hMd h i hi; omega
        · simp only [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS]
          rcases (show s.row (o + c0 + 32 * ww + i) fs = 0 ∨ s.row (o + c0 + 32 * ww + i) fs = 1 by omega) with h | h <;>
            rw [h] <;> omega
        · simp only [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc, heL,
            (R5 i hi).2.1, (R5 i hi).2.2]
          have : spKc ci ≤ 202 := by unfold spKc; split <;> (try split) <;> omega
          rcases (show s.row (o + c0 + 32 * ww + i) fs = 0 ∨ s.row (o + c0 + 32 * ww + i) fs = 1 by omega) with h | h <;>
            rw [h] <;> omega
        · have := hbyte (c0 + 32 * ww + i) (by omega)
          rwa [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega] at this)
    simp only [hKc, heL, heS, huA, hbN, hbL, hcO, hcS, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at eM eX
    exact ⟨eM, eX⟩
  -- assembling a branch
  have hpre : rowsB s o c0 = rowsB s o (c0 - 2) ++ rowsB s (o + (c0 - 2)) 2 := by
    rw [← rowsB_append]; congr 1; omega
  have asm : ∀ (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (M : Nat),
      rowsB s o (c0 - 2) = brTag bv →
      NearSpec.kidsBitmap cs 0 = spBm ci (s.row 0 tX) si → spBm ci (s.row 0 tX) si < 65536 →
      rowsB s (o + c0) (32 * ww) = (NearSpec.Kids.hashes cs).map UInt8.toNat →
      rowsB s (o + c0 + 32 * ww) 8 = (NearSpec.u64 M).map UInt8.toNat →
      rowsB s o (c0 + 32 * ww + 8) = (nodeEnc (.branch bv cs M)).map UInt8.toNat := by
    intro bv cs M e1 e2 e3 e4 e5
    rw [B.bytes, hpre, e1, bmB, hbmL, hbmH, e4, e5, brEnc, brPre_eq, e2]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    rw [show spBm ci (s.row 0 tX) si / 256 % 256 = spBm ci (s.row 0 tX) si / 256 by omega]
  -- the value slot, fresh (`LSb ESl0 ESl1`)
  have slotV : spVN ci = 1 → ci ≠ 4 → rowsB s o (c0 - 2) = brTag (some (.val val)) := by
    intro hV h4
    obtain ⟨-, -, -, ⟨U1, s1⟩, ⟨U2, s2⟩, -, -, -⟩ := branchVShape hw hs U (by omega) hq0 K.pf
    have hvz : vcpV ci 10 = 0 := by rw [sv, if_neg h4]
    have eV := vlenFresh hw hs hsc K U1 s1 (by omega) (by omega) hvz
    obtain ⟨eW, hgD, hdI, hdL⟩ := vhFresh hw hs hsc K U2 s2 (by omega) (by omega) hvz ⟨hL0, hL1, hL2⟩
    have hD := hdig (o + 5) (by omega) hgD hdI (by rw [hdL, hlen])
    rw [show c0 - 2 = 1 + (4 + 32) by omega, rowsB_append, rowsB_append, rowsB_one, htag, hV, eV,
      show o + 1 + 4 = o + 5 by omega, eW, hD]
    simp only [brTag, NearSpec.Slot.valueRef, List.map_append, toNats_u32, hlen]
    rw [show (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) % 256 = s.row 0 L0 by omega,
      show (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) / 256 % 256 = s.row 0 L1 by omega,
      show (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) / 65536 % 256 = s.row 0 L2 by omega,
      show (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) / 16777216 % 256 = 0 by omega]
  -- no value (`LSc ESn0 ESn1`)
  have slot0 : spVN ci = 0 → rowsB s o (c0 - 2) = brTag none := by
    intro hV
    rw [show c0 - 2 = 1 by omega, rowsB_one, htag, hV]; rfl
  -- the value slot, copied from the source leaf (`LSa`); its length reaches `MEM` through `SR`
  have slotL : ∀ key sl m, src = .leaf key sl m → sl.valueRef.length = 36 → sl.len < 2 ^ 32 → ci = 4 →
      rowsB s o (c0 - 2) = brTag (some sl) ∧
      s.row (o + c0 + 32 * ww) (SR 0) + 256 * s.row (o + c0 + 32 * ww) (SR 1) +
        65536 * s.row (o + c0 + 32 * ww) (SR 2) + 16777216 * s.row (o + c0 + 32 * ww) (SR 3) = sl.len ∧
      ∀ i, i < 4 → s.row (o + c0 + 32 * ww) (SR i) < 256 := by
    intro key sl m hsr h36 hsl32 h4
    have hV : spVN ci = 1 := by rw [h4]; rfl
    obtain ⟨-, -, -, ⟨U1, s1⟩, ⟨U2, s2⟩, -, -, -⟩ := branchVShape hw hs U (by omega) hq0 K.pf
    let H := (NearSpec.hexPrefix key true).map UInt8.toNat
    have hPb : Pb (s.row o sN) = ([0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)) ++
        (sl.valueRef.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) := by
      rw [hsrc, hsr]; simp [nodeEnc, H]
    have hPl : (Pb (s.row o sN)).length = 49 + H.length := by
      rw [hPb]; simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length, h36,
        u64_length]; omega
    have slotRow : ∀ t, t < 36 → s.row (o + 1 + t) cp = 1 ∧ s.row (o + 1 + t) rd = 1 ∧
        s.row (o + 1 + t) sBM = 0 ∧ s.row (o + 1 + t) spos = 5 + H.length + t ∧
        s.row (o + 1 + t) sN = s.row o sN ∧ OneHot (s.row (o + 1 + t)) ∧ (t < 4 → s.row (o + 1 + t) sVLEN = 1) := by
      intro t ht
      obtain ⟨F, hst⟩ : (OneHot (s.row (o + 1 + t)) ∧ o + 1 + t < s.rows.length ∧
          IxOf (s.row (o + 1 + t)) ci ti di si 10 (sdx k) ∧ (∀ x ∈ partConst, s.row (o + 1 + t) x = s.row o x) ∧
          s.row (o + 1 + t) qb = 1) ∧ ((t < 4 → s.row (o + 1 + t) sVLEN = 1) ∧ (4 ≤ t → s.row (o + 1 + t) sVH = 1)) := by
        rcases Nat.lt_or_ge t 4 with h | h
        · have F := kField hw hs hsc K U1 s1 (by omega) (by omega) t h
          exact ⟨⟨F.1, F.2.2.1, F.2.2.2.1, F.2.2.2.2.1, F.2.2.2.2.2⟩, fun _ => (stOf_inv F.1).2.2.2.2.1 F.2.1, fun h' => by omega⟩
        · have F := kField hw hs hsc K U2 s2 (by omega) (by omega) (t - 4) (by omega)
          rw [show o + 5 + (t - 4) = o + 1 + t by omega] at F
          exact ⟨⟨F.1, F.2.2.1, F.2.2.2.1, F.2.2.2.2.1, F.2.2.2.2.2⟩, fun h' => by omega, fun _ => (stOf_inv F.1).2.2.2.2.2.1 F.2.1⟩
      obtain ⟨hoh, hlt, hI, hpc, hq⟩ := F
      have okd := okRow hw hs hlt
      have hb := hoh.bs; have hs1 := hoh.sum
      have hv1 : s.row (o + 1 + t) vcp = 1 := by rw [hpc vcp (by decide), hv0, if_pos h4]
      have hcp : s.row (o + 1 + t) cp = 1 := by
        apply natv (rowLt hw hs _ _) one_lt
        rcases Nat.lt_or_ge t 4 with h | h
        · rw [cpVLEN okd (rowLt hw hs _) hs1 (hst.1 h), hv1]
        · rw [cpVH okd (rowLt hw hs _) hs1 (hst.2 h), hv1]
      have hst' : s.row (o + 1 + t) sVLEN + s.row (o + 1 + t) sVH = 1 := by
        rcases Nat.lt_or_ge t 4 with h | h
        · have := hst.1 h; omega
        · have := hst.2 h; omega
      have hrd := rdCopy okd (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh (fun h => by omega) (fun h => by omega)
        (fun _ => hI.kd 3 (by omega)) (fun h => by omega) (rdcOff okd (rowLt hw hs _) (nextLt hw hs _) (by omega))
      have hqp : s.row (o + 1 + t) qpos = 1 + t := by
        have := (U.rows (1 + t) (by omega)).2.1; rwa [show o + (1 + t) = o + 1 + t by omega] at this
      have hpl := (hR _ hlt hrd).2
      rw [hpc sN (by decide), hPl] at hpl
      refine ⟨hcp, hrd, by omega, ?_, hpc sN (by decide), hoh, hst.1⟩
      have f : ((s.row (o + 1 + t) kSPB : Nat) : Fp) * (((s.row (o + 1 + t) spos : Nat) : Fp) + 45 -
          (((s.row (o + 1 + t) plen : Nat) : Fp) + ((s.row (o + 1 + t) qpos : Nat) : Fp))) = 0 := by
        rcases Nat.lt_or_ge t 4 with h | h
        · exact pSVVLEN okd (rowLt hw hs _) hs1 hrd (hst.1 h)
        · exact pSVVH okd (rowLt hw hs _) hs1 hrd (hst.2 h)
      rw [show s.row (o + 1 + t) kSPB = 1 from hI.kd 10 (by omega), cast1, hpl, hqp] at f
      have := sub_of_cast (rowLt hw hs _ _) (by rw [P_lit]; omega) (show 45 ≤ 49 + H.length + (1 + t) by omega)
        (x := s.row (o + 1 + t) spos) (by rw [natCast_add, natCast_add]; grind)
      omega
    have cV := copyRun hw hs Pb (fun i hi hrd => (hR i hi hrd).1) (r := o + 1) (n := 36) (δ := 5 + H.length)
      (N := s.row o sN) (by omega) (by omega)
      (fun t ht => ⟨(slotRow t ht).1, (slotRow t ht).2.1, (slotRow t ht).2.2.1, (slotRow t ht).2.2.2.1,
        (slotRow t ht).2.2.2.2.1⟩)
    have hVR : ((Pb (s.row o sN)).drop (5 + H.length)).take 36 = sl.valueRef.map UInt8.toNat := by
      rw [hPb, show 5 + H.length = ([0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)).length by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length]; omega,
        List.drop_left', List.take_left' (by simp [h36])]
      all_goals rfl
    rw [hVR] at cV
    -- the old length through `SR`
    have hSR := srChain hw hs (r := o + 1) (r0 := o + c0 + 32 * ww) (by omega) (by omega)
      (fun t ht => ⟨(slotRow t (by omega)).2.2.2.2.2.2 ht, (slotRow t (by omega)).2.1, (slotRow t (by omega)).2.2.2.2.2.1⟩)
      (fun i h1 h2 => by
        have hd : i - o < c0 + 32 * ww + 8 := by omega
        have hq := (U.rows (i - o) hd).1
        have hpl1 := (U.rows (i - o) hd).2.2.2.1
        rw [show o + (i - o) = i by omega] at hq hpl1
        have hoh := oneHot hw hs (by omega) hq
        have := hoh.bs; have := hoh.sum
        have hpl0 : s.row i pl = 0 := by
          rcases plBool hw hs (r := i) (by omega) with h | h
          · exact h
          · have := hpl1.1 h; omega
        rcases Nat.lt_or_ge (i - o) 37 with h | h
        · have F := kField hw hs hsc K U2 s2 (by omega) (by omega) (i - o - 5) (by omega)
          rw [show o + 5 + (i - o - 5) = i by omega] at F
          have := (stOf_inv F.1).2.2.2.2.2.1 F.2.1
          exact ⟨hq, hpl0, by omega, by omega⟩
        · rcases Nat.lt_or_ge (i - o) c0 with h' | h'
          · obtain ⟨-, -, -, -, -, -, a7, -, -, a10, -, -⟩ := B.pre (i - o) h'
            rw [show o + (i - o) = i by omega] at a7 a10
            have := a10.2 (by omega)
            exact ⟨hq, hpl0, by omega, a7⟩
          · have := (B.win (i - o - c0) (by omega)).2.2.2.2.2
            rw [show o + c0 + (i - o - c0) = i by omega] at this
            exact ⟨hq, hpl0, by omega, by omega⟩)
    have hvr : (sl.valueRef.map UInt8.toNat).take 4 = (NearSpec.u32 sl.len).map UInt8.toNat := by
      cases sl <;> simp [NearSpec.Slot.valueRef, NearSpec.Slot.len, List.take_append_of_le_length, u32_length]
    have hSj : ∀ j, j < 4 → s.row (o + c0 + 32 * ww) (SR j) = ((NearSpec.u32 sl.len).map UInt8.toNat).getD j 0 := by
      intro j hj
      obtain ⟨c1, -, c3, -, -, -, -⟩ := slotRow j (by omega)
      rw [hSR j hj, ← bCopyN (okRow hw hs (i := o + 1 + j) (by omega)) (rowLt hw hs _) (nextLt hw hs _) c1 c3]
      have := congrArg (fun l => l.getD j 0) cV
      simp only [rowsB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < 36 by omega),
        Option.map_some, Option.getD_some] at this
      rw [this, ← hvr]
      simp [List.getElem?_take, hj]
    refine ⟨?_, ?_, fun i hi => ?_⟩
    · rw [show c0 - 2 = 1 + 36 by omega, rowsB_append, rowsB_one, htag, hV, cV]; rfl
    · rw [hSj 0 (by omega), hSj 1 (by omega), hSj 2 (by omega), hSj 3 (by omega)]
      simp [toNats_u32]; omega
    · rw [hSj i hi]; exact toNats_lt _ _
  -- the extension source of `ESl1` / `ESn1`: `phk`, the old memory and the old child hash
  have extX : ∀ key c m, src = .ext key c m → c.hashOf.length = 32 → m < 2 ^ 64 → key.length < 400 → spXN ci = 1 →
      s.row o Cc = 50 + 2 * (NearSpec.hexPrefix key false).length ∧
      limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 = m ∧
      ((Pb (s.row o sN)).drop ((Pb (s.row o sN)).length - 40)).take 32 = c.hashOf.map UInt8.toNat ∧
      40 ≤ (Pb (s.row o sN)).length := by
    intro key c m hsr hc32 hm hkl hX
    let H := (NearSpec.hexPrefix key false).map UInt8.toNat
    have hHl : H.length = key.length / 2 + 1 := by simp [H, UpsSpec.hp_len]
    have hPb : Pb (s.row o sN) = ([3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)) ++
        (c.hashOf.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) := by
      rw [hsrc, hsr]; simp [nodeEnc, H]
    have hPl : (Pb (s.row o sN)).length = 45 + H.length := by
      rw [hPb]; simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length, hc32,
        u64_length]; omega
    -- `phk` from the first bitmap row
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
    have hph : s.row (o + (c0 - 2)) rb = s.row (o + (c0 - 2)) phk := by
      have f := rBM hok (rowLt hw hs _) a1.sum hbm hfs
      rw [hxc, cast1] at f
      exact natv (rowLt hw hs _ _) (rowLt hw hs _ _) (by grind)
    have hrb := (hR _ a2 hrd).1
    rw [hsp, a4 sN (by decide), hPb] at hrb
    have hphk : s.row o phk = H.length := by
      rw [← a4 phk (by decide), ← hph, hrb]
      simp [toNats_u32, List.getD_eq_getElem?_getD]; omega
    refine ⟨?_, ?_, ?_, by omega⟩
    · rw [hCc (by rw [hphk]; omega), hX, hphk]; simp [H]
    · rw [limbs8]
      have hr : ∀ i, i < 8 → s.row (o + c0 + 32 * ww + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
        intro i hi
        rw [(memRd i hi).2 (by omega), hPl, hPb, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp [u32_length]; omega), List.getElem?_append_right (by simp [hc32]; omega)]
        simp [u32_length, hc32]
        rw [show 45 + H.length - 8 + i - (4 + H.length + 1) - 32 = i by omega]
      rw [hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hr 3 (by omega), hr 4 (by omega), hr 5 (by omega),
        hr 6 (by omega), hr 7 (by omega), toNats_u64]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      omega
    · rw [hPl, show 45 + H.length - 40 = ([3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)).length by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length]; omega, hPb,
        List.drop_left', List.take_left' (by simp [hc32])]
      all_goals rfl
  -- the cases
  have hLv : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2 := hlen
  have hlm : NearSpec.leafMem (UpsSpec.ysOf si) val.length = 102 + val.length := by
    unfold NearSpec.leafMem; rw [ysOf_hpLen si i4]; omega
  have hx15 : 2 ^ s.row 0 tX ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  have w2 : ∀ (A B : List Nat), rowsB s (o + c0 + 32 * 0) 32 = A → rowsB s (o + c0 + 32 * 1) 32 = B →
      rowsB s (o + c0) (32 * 2) = A ++ B := by
    intro A B h1 h2
    rw [show 32 * 2 = 32 + 32 from rfl, rowsB_append, ← h1, ← h2]; rfl
  have w1 : ∀ (A : List Nat), rowsB s (o + c0 + 32 * 0) 32 = A → rowsB s (o + c0) (32 * 1) = A := by
    intro A h1; rw [← h1]; rfl
  rcases (show ci = 4 ∨ ci = 5 ∨ ci = 6 ∨ ci = 7 ∨ ci = 8 ∨ ci = 9 ∨ ci = 10 by omega) with h | h | h | h | h | h | h
  · -- `LSa`: the leaf's value, the new leaf at `y`
    subst h
    obtain ⟨key, sl, m, hsr, h36, hsl32⟩ := hsrcL rfl
    obtain ⟨eP, eS, eSb⟩ := slotL key sl m hsr h36 hsl32 rfl
    have hwv : ww = 1 := by rw [hwwv, stw]; rfl
    have hsi1 := hsiY rfl
    have hy : UpsSpec.yOf si < 16 := by rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide
    have hk1 := UpsSpec.kids1_bm (UpsSpec.yOf si) (UpsSpec.qNLF si val) hy
    have hW := winY 0 (by omega) (by rw [if_pos rfl, sy1, if_pos (Or.inl rfl)])
    subst hsr hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 1) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun _ => eSb) (by rw [hCc0 rfl]; omega)).2, eS]
      simp [spKc, spXN, spRN, NearSpec.valueMem, hlm, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    apply asm _ _ _ eP (by rw [hk1.1]; simp [spBm, spYN])
      (by have : 2 ^ UpsSpec.yOf si ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
          simp [spBm, spYN]; omega)
      (by rw [hk1.2]; exact w1 _ hW)
    rw [(eMgen (fun _ => eSb) (by rw [hCc0 rfl]; omega)).1, eS]
    congr 2
    simp [spKc, spXN, spRN, NearSpec.valueMem, hlm]
    omega
  · -- `LSb`: the new value, the moved leaf at `x`
    subst h
    have hwv : ww = 1 := by rw [hwwv, stw]; rfl
    have hk1 := UpsSpec.kids1_bm (s.row 0 tX) cx hx16
    have hW := winC 0 (by omega) (by rw [if_pos rfl, sy1]; simp) (by decide)
    subst hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 1) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).2, hmB (by decide), hCc0 (by decide)]
      simp [spKc, spXN, spRN, NearSpec.valueMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    apply asm _ _ _ (slotV (by decide) (by decide)) (by rw [hk1.1]; simp [spBm, spYN])
      (by simp [spBm, spYN]; omega) (by rw [hk1.2]; exact w1 _ hW)
    rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).1, hmB (by decide), hCc0 (by decide)]
    congr 2
    simp [spKc, spXN, spRN, NearSpec.valueMem]
    omega
  · -- `LSc`: the moved leaf at `x`, the new leaf at `y`
    subst h
    have hwv : ww = 2 := by rw [hwwv, stw]; rfl
    have hsi1 := hsiY (by decide)
    have hne := hxy (by decide) (by decide)
    have hy16 : UpsSpec.yOf si < 16 := by rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide
    have hk2 := UpsSpec.kids2_bm (s.row 0 tX) (UpsSpec.yOf si) cx (UpsSpec.qNLF si val) hx16 hy16 hne
    subst hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 2) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).2, hmB (by decide), hCc0 (by decide)]
      simp [spKc, spXN, spRN, hlm, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    have eM : rowsB s (o + c0 + 32 * 2) 8 = (NearSpec.u64 (50 + cx.memD + NearSpec.leafMem (UpsSpec.ysOf si) val.length)).map UInt8.toNat := by
      rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).1, hmB (by decide), hCc0 (by decide)]
      congr 2
      simp [spKc, spXN, spRN, hlm]
      omega
    rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl
    · have hWy := winY 0 (by omega) (by rw [if_pos rfl, sy1]; simp)
      have hWc := winC 1 (by omega) (by rw [if_neg (by omega), sy2]; simp) (by decide)
      have hx0' : s.row 0 tX ≠ 0 := hne
      apply asm _ _ _ (slot0 (by decide)) (by rw [hk2.1]; simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key])
        (by simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key]; omega)
        (by rw [hk2.2, if_neg (by simp [UpsSpec.yOf, UpsSpec.key]), List.map_append]; exact w2 _ _ hWy hWc) eM
    · have hWc := winC 0 (by omega) (by rw [if_pos rfl, sy1]; simp) (by decide)
      have hWy := winY 1 (by omega) (by rw [if_neg (by omega), sy2]; simp)
      have hx14 : s.row 0 tX ≤ 14 := by have : s.row 0 tX ≠ 15 := hne; omega
      have : 2 ^ s.row 0 tX ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) hx14
      apply asm _ _ _ (slot0 (by decide)) (by rw [hk2.1]; simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key])
        (by simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key]; omega)
        (by rw [hk2.2, if_pos (by simp [UpsSpec.yOf, UpsSpec.key]; omega), List.map_append]; exact w2 _ _ hWc hWy) eM
  · -- `ESl0`: the new value, the shortened extension at `x`
    subst h
    have hwv : ww = 1 := by rw [hwwv, stw]; rfl
    have hk1 := UpsSpec.kids1_bm (s.row 0 tX) cx hx16
    have hW := winC 0 (by omega) (by rw [if_pos rfl, sy1]; simp) (by decide)
    subst hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 1) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).2, hmB (by decide), hCc0 (by decide)]
      simp [spKc, spXN, spRN, NearSpec.valueMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    apply asm _ _ _ (slotV (by decide) (by decide)) (by rw [hk1.1]; simp [spBm, spYN])
      (by simp [spBm, spYN]; omega) (by rw [hk1.2]; exact w1 _ hW)
    rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).1, hmB (by decide), hCc0 (by decide)]
    congr 2
    simp [spKc, spXN, spRN, NearSpec.valueMem]
    omega
  · -- `ESl1`: the new value, the old child at `x`
    subst h
    obtain ⟨key, c, m, hsr, hc32, hm, hkl⟩ := hsrcE (by decide)
    obtain ⟨hCcv, hA, hOld, h40⟩ := extX key c m hsr hc32 hm hkl (by decide)
    have hwv : ww = 1 := by rw [hwwv, stw]; rfl
    have hk1 := UpsSpec.kids1_bm (s.row 0 tX) c hx16
    have hW := winO 0 (by omega) (by rw [if_pos rfl, sy1]; simp) (by decide) h40
    rw [hOld] at hW
    have hHk : (NearSpec.hexPrefix key false).length = key.length / 2 + 1 := UpsSpec.hp_len key false
    subst hsr hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 1) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCcv]; omega)).2, hA, hCcv]
      simp [spKc, spXN, spRN, NearSpec.valueMem, NearSpec.extOwnMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    apply asm _ _ _ (slotV (by decide) (by decide)) (by rw [hk1.1]; simp [spBm, spYN])
      (by simp [spBm, spYN]; omega) (by rw [hk1.2]; exact w1 _ hW)
    rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCcv]; omega)).1, hA, hCcv]
    congr 2
    simp [spKc, spXN, spRN, NearSpec.valueMem, NearSpec.extOwnMem]
    omega
  · -- `ESn0`: the shortened extension at `x`, the new leaf at `y`
    subst h
    have hwv : ww = 2 := by rw [hwwv, stw]; rfl
    have hsi1 := hsiY (by decide)
    have hne := hxy (by decide) (by decide)
    have hy16 : UpsSpec.yOf si < 16 := by rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide
    have hk2 := UpsSpec.kids2_bm (s.row 0 tX) (UpsSpec.yOf si) cx (UpsSpec.qNLF si val) hx16 hy16 hne
    subst hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 2) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).2, hmB (by decide), hCc0 (by decide)]
      simp [spKc, spXN, spRN, hlm, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    have eM : rowsB s (o + c0 + 32 * 2) 8 = (NearSpec.u64 (50 + cx.memD + NearSpec.leafMem (UpsSpec.ysOf si) val.length)).map UInt8.toNat := by
      rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCc0 (by decide)]; omega)).1, hmB (by decide), hCc0 (by decide)]
      congr 2
      simp [spKc, spXN, spRN, hlm]
      omega
    rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl
    · have hWy := winY 0 (by omega) (by rw [if_pos rfl, sy1]; simp)
      have hWc := winC 1 (by omega) (by rw [if_neg (by omega), sy2]; simp) (by decide)
      have hx0' : s.row 0 tX ≠ 0 := hne
      apply asm _ _ _ (slot0 (by decide)) (by rw [hk2.1]; simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key])
        (by simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key]; omega)
        (by rw [hk2.2, if_neg (by simp [UpsSpec.yOf, UpsSpec.key]), List.map_append]; exact w2 _ _ hWy hWc) eM
    · have hWc := winC 0 (by omega) (by rw [if_pos rfl, sy1]; simp) (by decide)
      have hWy := winY 1 (by omega) (by rw [if_neg (by omega), sy2]; simp)
      have hx14 : s.row 0 tX ≤ 14 := by have : s.row 0 tX ≠ 15 := hne; omega
      have : 2 ^ s.row 0 tX ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) hx14
      apply asm _ _ _ (slot0 (by decide)) (by rw [hk2.1]; simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key])
        (by simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key]; omega)
        (by rw [hk2.2, if_pos (by simp [UpsSpec.yOf, UpsSpec.key]; omega), List.map_append]; exact w2 _ _ hWc hWy) eM
  · -- `ESn1`: the old child at `x`, the new leaf at `y`
    subst h
    obtain ⟨key, c, m, hsr, hc32, hm, hkl⟩ := hsrcE (by decide)
    obtain ⟨hCcv, hA, hOld, h40⟩ := extX key c m hsr hc32 hm hkl (by decide)
    have hwv : ww = 2 := by rw [hwwv, stw]; rfl
    have hsi1 := hsiY (by decide)
    have hne := hxy (by decide) (by decide)
    have hy16 : UpsSpec.yOf si < 16 := by rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl <;> decide
    have hk2 := UpsSpec.kids2_bm (s.row 0 tX) (UpsSpec.yOf si) c (UpsSpec.qNLF si val) hx16 hy16 hne
    have hHk : (NearSpec.hexPrefix key false).length = key.length / 2 + 1 := UpsSpec.hp_len key false
    subst hsr hwv
    simp only [UpsSpec.qSPB]
    refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * 2) (by omega) rx).trans ?_⟩
    rotate_left
    · rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCcv]; omega)).2, hA, hCcv]
      simp [spKc, spXN, spRN, hlm, NearSpec.extOwnMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
      all_goals omega
    have eM : rowsB s (o + c0 + 32 * 2) 8 = (NearSpec.u64 (50 + (m - NearSpec.extOwnMem key) +
        NearSpec.leafMem (UpsSpec.ysOf si) val.length)).map UInt8.toNat := by
      rw [(eMgen (fun h => absurd h (by decide)) (by rw [hCcv]; omega)).1, hA, hCcv]
      congr 2
      simp [spKc, spXN, spRN, hlm, NearSpec.extOwnMem]
      omega
    rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl
    · have hWy := winY 0 (by omega) (by rw [if_pos rfl, sy1]; simp)
      have hWo := winO 1 (by omega) (by rw [if_neg (by omega), sy2]; simp) (by decide) h40
      rw [hOld] at hWo
      have hx0' : s.row 0 tX ≠ 0 := hne
      apply asm _ _ _ (slot0 (by decide)) (by rw [hk2.1]; simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key])
        (by simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key]; omega)
        (by rw [hk2.2, if_neg (by simp [UpsSpec.yOf, UpsSpec.key]), List.map_append]; exact w2 _ _ hWy hWo) eM
    · have hWo := winO 0 (by omega) (by rw [if_pos rfl, sy1]; simp) (by decide) h40
      have hWy := winY 1 (by omega) (by rw [if_neg (by omega), sy2]; simp)
      rw [hOld] at hWo
      have hx14 : s.row 0 tX ≤ 14 := by have : s.row 0 tX ≠ 15 := hne; omega
      have : 2 ^ s.row 0 tX ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) hx14
      apply asm _ _ _ (slot0 (by decide)) (by rw [hk2.1]; simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key])
        (by simp [spBm, spYN, UpsSpec.yOf, UpsSpec.key]; omega)
        (by rw [hk2.2, if_pos (by simp [UpsSpec.yOf, UpsSpec.key]; omega), List.map_append]; exact w2 _ _ hWo hWy) eM

end

end ZkFormal.NearV3.UpsRows

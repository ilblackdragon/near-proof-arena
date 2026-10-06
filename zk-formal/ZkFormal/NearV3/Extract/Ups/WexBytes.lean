import ZkFormal.NearV3.Extract.Ups.RdeBytes

/-!
# ZkFormal.NearV3.Extract.Ups.WexBytes — the wrapping extension `WEX` is `nodeEnc (qWEX p b)` (layer 2)

A part of kind `WEX` (index 9) is the extension `wrapExt p b` over the common prefix `p` of a
split (`I = ti ≥ 1` nibbles of the key ending before the terminal nibble `t* = si + 1`, so
`p = [0, 15].drop (si − ti) |>.take ti`, one of `[0]`, `[15]`, `[0, 15]`) above the split branch
`b` (the part below).  All its bytes are fresh: tag `3`, `u32 |hp p|`, the hex prefix of `p`
(`0x10`, `0x1f` or `0x00 0x0f`), the digest of the part below and
`memory_usage = 50 + 2·|hp p| + b.memD`.

Hypotheses: `1 ≤ ti ≤ si` (the walk: the prefix lies in the terminal record before the terminal
nibble); the `DIGEST` of the part below at `clen` is `b.hashOf`; the `MEMD` limbs received on
the `MEM` rows are `< 2^12` with value `b.memD`; the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The prefix a wrapping extension covers. -/
def wexKey (si ti : Nat) : List Nat := (UpsSpec.key.drop (si - ti)).take ti

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem wexQhk (hpf : C pf = 1) (hk : C kWEX = 1) (h3 : C ts3 ≤ 1) (h2 : C ti2 ≤ 1) :
    C qhk = 1 + C ts3 * C ti2 := by
  have f := factN ok hC hD (e := .mul (c pf) (.mul (c kWEX) (sub (c qhk) (.add (k 1) (.mul (c ts3) (c ti2))))))
    (memPlan (by simp [cPlan]))
  have := hC qhk
  simp only [P_lit] at *
  nev_simp at f
  rcases (show C ts3 = 0 ∨ C ts3 = 1 by omega) with a | a <;> rcases (show C ti2 = 0 ∨ C ti2 = 1 by omega) with b' | b' <;>
    simp [hpf, hk, a, b'] at f ⊢ <;> omega

theorem wexHpf (hh : C sHPF = 1) (hk : C kWEX = 1) (h2 : C ts2 ≤ 1) (h3 : C ts3 ≤ 1) (h1 : C ti1 ≤ 1) :
    C b = 16 * (C ts2 * C ti1) + 31 * (C ts3 * C ti1) := by
  have f := factN ok hC hD (e := mul3 (c sHPF) (c kWEX) (sub (c b) (.add (smul 16 (.mul (c ts2) (c ti1)))
    (smul 31 (.mul (c ts3) (c ti1)))))) (memBytes (by simp [cBytes]))
  have := hC b
  simp only [P_lit] at *
  nev_simp at f
  rcases (show C ts2 = 0 ∨ C ts2 = 1 by omega) with a | a <;> rcases (show C ts3 = 0 ∨ C ts3 = 1 by omega) with b' | b' <;>
    rcases (show C ti1 = 0 ∨ C ti1 = 1 by omega) with c' | c' <;> simp [hh, hk, a, b', c'] at f ⊢ <;> omega

theorem wexKeyB (hh : C sKEY = 1) (hk : C kWEX = 1) : C b = 15 := by
  have f := factN ok hC hD (e := mul3 (c sKEY) (c kWEX) (sub (c b) (k 15))) (memBytes (by simp [cBytes]))
  have := hC b
  simp only [P_lit] at *
  nev_simp at f
  simp [hh, hk] at f
  omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The wrapping extension** (`WEX`): its bytes are `nodeEnc (qWEX (wexKey si ti) b')`. -/
theorem ups_wexBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 9) (b' : NearSpec.PTrie)
    (hti : 1 ≤ ti) (hts : ti ≤ si)
    (hdC : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = s.row ps[k].1 clen → regN (s.row i) = b'.hashOf.map UInt8.toNat)
    (hMd : ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv < 4096)
    (hmB : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mBv) 8 = b'.memD)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qWEX (wexKey si ti) b')).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qWEX (wexKey si ti) b').memD := by
  have K := partK hw hs hL hP k hk
  obtain ⟨hj, U⟩ := hL.part k hk
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hdC hMd hmB hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte hMd hmB ⊢
  have hsc := hL.segc
  obtain ⟨i1, i2, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨-, -, hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_WEX ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  -- the segment indices on a row
  have tsv := fun d (hd : d < ℓ) m (hm : m < 3) => (K.ix d hd).ts m hm
  have tiv := fun d (hd : d < ℓ) m (hm : m < 3) => (K.ix d hd).ti m hm
  have hq := wexQhk ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (I0.kd 9 (by omega))
    (by have := I0.ts 2 (by omega); show s.row o 33 ≤ 1; rw [this]; split <;> omega)
    (by have := I0.ti 2 (by omega); show s.row o 36 ≤ 1; rw [this]; split <;> omega)
  have hqv : s.row o qhk = if si = 2 ∧ ti = 2 then 2 else 1 := by
    rw [hq]
    have a := I0.ts 2 (by omega); have b2 := I0.ti 2 (by omega)
    show 1 + s.row o 33 * s.row o 36 = _
    rw [a, b2]
    by_cases h1 : si = 2 <;> by_cases h2 : ti = 2 <;> simp [h1, h2, eq_comm]
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U5, s5⟩⟩ := extShape hw hs U hte hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U5 s5 hKc hqv
  subst hℓ
  have hle := K.le
  -- TAG, HPL (grammar)
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 3 by omega] at eT
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1 + d) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  rw [show s.row (o + 1) qhk = q by rw [← hqq]; exact K.pc 1 (by omega) qhk (by decide)] at eH
  -- HPF [KEY] (fresh)
  have F5 := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at F5
  have b5 := wexHpf (okRow hw hs F5.2.2.1) (rowLt hw hs _) (nextLt hw hs _) ((stOf_inv F5.1).2.2.1 F5.2.1)
    (F5.2.2.2.1.kd 9 (by omega))
    (by have := F5.2.2.2.1.ts 1 (by omega); show s.row (o + 5) 32 ≤ 1; rw [this]; split <;> omega)
    (by have := F5.2.2.2.1.ts 2 (by omega); show s.row (o + 5) 33 ≤ 1; rw [this]; split <;> omega)
    (by have := F5.2.2.2.1.ti 1 (by omega); show s.row (o + 5) 35 ≤ 1; rw [this]; split <;> omega)
  have hv5 : s.row (o + 5) b = if si = 1 ∧ ti = 1 then 16 else if si = 2 ∧ ti = 1 then 31 else 0 := by
    rw [b5]
    have a1 := F5.2.2.2.1.ts 1 (by omega); have a2 := F5.2.2.2.1.ts 2 (by omega); have a3 := F5.2.2.2.1.ti 1 (by omega)
    show 16 * (s.row (o + 5) 32 * s.row (o + 5) 35) + 31 * (s.row (o + 5) 33 * s.row (o + 5) 35) = _
    rw [a1, a2, a3]
    by_cases h1 : si = 1 <;> by_cases h2 : si = 2 <;> by_cases h3 : ti = 1 <;> simp [h1, h2, h3, eq_comm] <;> omega
  have eK : rowsB s (o + 5) q = if si = 2 ∧ ti = 2 then [0, 15] else [s.row (o + 5) b] := by
    rw [KR.bytes, rowsB_one]
    by_cases h : si = 2 ∧ ti = 2
    · rw [if_pos h] at hqv ⊢
      have hk1 := KR.key (by omega)
      have F6 := kField hw hs hsc K hk1.1 hk1.2 (by omega) (by omega) 0 (by omega)
      simp only [Nat.add_zero] at F6
      have b6 := wexKeyB (okRow hw hs F6.2.2.1) (rowLt hw hs _) (nextLt hw hs _) ((stOf_inv F6.1).2.2.2.1 F6.2.1)
        (F6.2.2.2.1.kd 9 (by omega))
      rw [hqv, show 2 - 1 = 1 from rfl, rowsB_one, b6, hv5, if_neg (by omega), if_neg (by omega)]; rfl
    · rw [if_neg h] at hqv ⊢
      rw [hqv, show 1 - 1 = 0 from rfl]
      simp [rowsB]
  -- CH (fresh: the part below's digest)
  have FC := kField hw hs hsc K U3 s3 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + 5 + q + d) sCH = 1 ∧ s.row (o + 5 + q + d) wfr = 1 ∧
      s.row (o + 5 + q + d) wn = 0 := by
    intro d hd
    have F := FC d hd
    have h7 := (stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1
    have hI := F.2.2.2.1
    exact ⟨h7, chUp (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) h7 (hI.kd 5 (by omega))
      (hI.kd 10 (by omega)) (by rw [show s.row (o + 5 + q + d) kRDE = 0 from hI.kd 1 (by omega),
        show s.row (o + 5 + q + d) kWEX = 1 from hI.kd 9 (by omega), show s.row (o + 5 + q + d) kPT = 0 from hI.kd 11 (by omega)])⟩
  have eW := freshWin hw hs (r0 := o + 5 + q) (by omega)
    (fun d hd => Or.inr ⟨(chU d hd).1, (chU d hd).2.1, by have := (FC d hd).1.sum; have := (chU d hd).1; omega⟩)
    (fun d hd => feZero hw hs hsc K U3 (by omega) d (by omega))
  have F0 := FC 0 (by omega)
  simp only [Nat.add_zero] at F0
  have c0 := chU 0 (by omega)
  simp only [Nat.add_zero] at c0
  have hr3 : o + 5 + q < s.rows.length := by omega
  have hgD := gDrow (okRow hw hs hr3) (rowLt hw hs _) (nextLt hw hs _) F0.2.2.2.2.2
    (by simpa using (U3.fs 0 (by omega)).2 rfl) (qbWt3 hw hs hr3 F0.2.2.2.2.2)
    (Or.inr ⟨c0.1, c0.2.1, by have := F0.1.sum; omega⟩)
  have hjm : s.row o jm = k := by
    rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by
      rw [show s.row o kRDB = 0 from I0.kd 0 (by omega), show s.row o kRDE = 0 from I0.kd 1 (by omega),
        show s.row o kWEX = 1 from I0.kd 9 (by omega), show s.row o kPT = 0 from I0.kd 11 (by omega)]) (by omega), hj]
    omega
  have hdI := dIj_nat (rowLt hw hs _ _) (dCHm (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0.1 c0.2.2)
  have hdL := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (dCHml (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0.1 c0.2.2)
  rw [hsc _ hr3 tau (by decide), show s.row (o + 5 + q) jm = s.row o jm by
    have := K.pc (5 + q) (by omega) jm (by decide); rwa [show o + (5 + q) = o + 5 + q by omega] at this, hjm] at hdI
  rw [show s.row (o + 5 + q) clen = s.row o clen by
    have := K.pc (5 + q) (by omega) clen (by decide); rwa [show o + (5 + q) = o + 5 + q by omega] at this] at hdL
  have hDC := hdC (o + 5 + q) hr3 hgD hdI hdL
  -- MEM
  have R5 := memRegs hw hs hsc K U5 s5 (by omega) (by omega)
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (37 + q + i) (by omega) x hx; rwa [show o + (37 + q + i) = o + 37 + q + i by omega] at this
  have hr0 : o + (45 + q) - 8 = o + 37 + q := by omega
  rw [hr0] at hMd hmB
  have hq2 : q ≤ 2 := by split at hqv <;> omega
  have hKc' := hKc (by omega)
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U U5 s5 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + 37 + q + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [inA, pc5 i hi useA (by decide), huA]
      · simp only [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
        have := hMd i hi; omega
      · simp [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc]
      · simp only [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc', heL, heS]
        rcases (show s.row (o + 37 + q + i) fs = 0 ∨ s.row (o + 37 + q + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · have := hbyte (37 + q + i) (by omega); rwa [show o + (37 + q + i) = o + 37 + q + i by omega] at this)
  simp only [hKc', heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hmB] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + 37 + q) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    have hcase : (si = 1 ∧ ti = 1) ∨ (si = 2 ∧ ti = 1) ∨ (si = 2 ∧ ti = 2) := by omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp at hqv
      subst hqv
      simp [UpsSpec.qWEX, wexKey, UpsSpec.key, NearSpec.wrapExt, NearSpec.extOwnMem, NearSpec.hexPrefix,
        NearSpec.packNibbles, NearSpec.PTrie.memD, NearSpec.PTrie.mem?]
  -- assemble
  rw [hBy, eT, eH, eK, eW, eM]
  rw [show (List.range 32).map (fun i => s.row (o + 5 + q) (reg i)) = regN (s.row (o + 5 + q)) from rfl, hDC, hv5]
  -- the three prefixes
  have hcase : (si = 1 ∧ ti = 1) ∨ (si = 2 ∧ ti = 1) ∨ (si = 2 ∧ ti = 2) := by omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [if_pos, if_neg] at hqv ⊢
    subst hqv
    simp [UpsSpec.qWEX, wexKey, UpsSpec.key, NearSpec.wrapExt, nodeEnc, toNats_u32, NearSpec.extOwnMem,
      NearSpec.hexPrefix, NearSpec.packNibbles]
  · simp only [if_pos, if_neg] at hqv ⊢
    subst hqv
    simp [UpsSpec.qWEX, wexKey, UpsSpec.key, NearSpec.wrapExt, nodeEnc, toNats_u32, NearSpec.extOwnMem,
      NearSpec.hexPrefix, NearSpec.packNibbles]
  · simp only [if_pos, if_neg] at hqv ⊢
    subst hqv
    simp [UpsSpec.qWEX, wexKey, UpsSpec.key, NearSpec.wrapExt, nodeEnc, toNats_u32, NearSpec.extOwnMem,
      NearSpec.hexPrefix, NearSpec.packNibbles]

/-- A `WEX` part looks up its child's digest (id `jm = k`, length `clen`) on its window. -/
theorem wexLook (k : Nat) (hk : k < ps.length) (hkd : kd k = 9) (b' : NearSpec.PTrie)
    (hti : 1 ≤ ti) (hts : ti ≤ si)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    ∃ i, i < s.rows.length ∧ s.row i gD = 1 ∧ s.row i dI = upsIdN (s.row 0 tau) k ∧ s.row i dL = s.row ps[k].1 clen := by
  have K := partK hw hs hL hP k hk
  obtain ⟨hj, U⟩ := hL.part k hk
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, i2, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨-, -, hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_WEX ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  -- the segment indices on a row
  have tsv := fun d (hd : d < ℓ) m (hm : m < 3) => (K.ix d hd).ts m hm
  have tiv := fun d (hd : d < ℓ) m (hm : m < 3) => (K.ix d hd).ti m hm
  have hq := wexQhk ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (I0.kd 9 (by omega))
    (by have := I0.ts 2 (by omega); show s.row o 33 ≤ 1; rw [this]; split <;> omega)
    (by have := I0.ti 2 (by omega); show s.row o 36 ≤ 1; rw [this]; split <;> omega)
  have hqv : s.row o qhk = if si = 2 ∧ ti = 2 then 2 else 1 := by
    rw [hq]
    have a := I0.ts 2 (by omega); have b2 := I0.ti 2 (by omega)
    show 1 + s.row o 33 * s.row o 36 = _
    rw [a, b2]
    by_cases h1 : si = 2 <;> by_cases h2 : ti = 2 <;> simp [h1, h2, eq_comm]
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U5, s5⟩⟩ := extShape hw hs U hte hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U5 s5 hKc hqv
  subst hℓ
  have hle := K.le
  -- TAG, HPL (grammar)
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 3 by omega] at eT
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1 + d) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  rw [show s.row (o + 1) qhk = q by rw [← hqq]; exact K.pc 1 (by omega) qhk (by decide)] at eH
  -- HPF [KEY] (fresh)
  have F5 := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at F5
  have b5 := wexHpf (okRow hw hs F5.2.2.1) (rowLt hw hs _) (nextLt hw hs _) ((stOf_inv F5.1).2.2.1 F5.2.1)
    (F5.2.2.2.1.kd 9 (by omega))
    (by have := F5.2.2.2.1.ts 1 (by omega); show s.row (o + 5) 32 ≤ 1; rw [this]; split <;> omega)
    (by have := F5.2.2.2.1.ts 2 (by omega); show s.row (o + 5) 33 ≤ 1; rw [this]; split <;> omega)
    (by have := F5.2.2.2.1.ti 1 (by omega); show s.row (o + 5) 35 ≤ 1; rw [this]; split <;> omega)
  have hv5 : s.row (o + 5) b = if si = 1 ∧ ti = 1 then 16 else if si = 2 ∧ ti = 1 then 31 else 0 := by
    rw [b5]
    have a1 := F5.2.2.2.1.ts 1 (by omega); have a2 := F5.2.2.2.1.ts 2 (by omega); have a3 := F5.2.2.2.1.ti 1 (by omega)
    show 16 * (s.row (o + 5) 32 * s.row (o + 5) 35) + 31 * (s.row (o + 5) 33 * s.row (o + 5) 35) = _
    rw [a1, a2, a3]
    by_cases h1 : si = 1 <;> by_cases h2 : si = 2 <;> by_cases h3 : ti = 1 <;> simp [h1, h2, h3, eq_comm] <;> omega
  have eK : rowsB s (o + 5) q = if si = 2 ∧ ti = 2 then [0, 15] else [s.row (o + 5) b] := by
    rw [KR.bytes, rowsB_one]
    by_cases h : si = 2 ∧ ti = 2
    · rw [if_pos h] at hqv ⊢
      have hk1 := KR.key (by omega)
      have F6 := kField hw hs hsc K hk1.1 hk1.2 (by omega) (by omega) 0 (by omega)
      simp only [Nat.add_zero] at F6
      have b6 := wexKeyB (okRow hw hs F6.2.2.1) (rowLt hw hs _) (nextLt hw hs _) ((stOf_inv F6.1).2.2.2.1 F6.2.1)
        (F6.2.2.2.1.kd 9 (by omega))
      rw [hqv, show 2 - 1 = 1 from rfl, rowsB_one, b6, hv5, if_neg (by omega), if_neg (by omega)]; rfl
    · rw [if_neg h] at hqv ⊢
      rw [hqv, show 1 - 1 = 0 from rfl]
      simp [rowsB]
  -- CH (fresh: the part below's digest)
  have FC := kField hw hs hsc K U3 s3 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + 5 + q + d) sCH = 1 ∧ s.row (o + 5 + q + d) wfr = 1 ∧
      s.row (o + 5 + q + d) wn = 0 := by
    intro d hd
    have F := FC d hd
    have h7 := (stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1
    have hI := F.2.2.2.1
    exact ⟨h7, chUp (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) h7 (hI.kd 5 (by omega))
      (hI.kd 10 (by omega)) (by rw [show s.row (o + 5 + q + d) kRDE = 0 from hI.kd 1 (by omega),
        show s.row (o + 5 + q + d) kWEX = 1 from hI.kd 9 (by omega), show s.row (o + 5 + q + d) kPT = 0 from hI.kd 11 (by omega)])⟩
  have eW := freshWin hw hs (r0 := o + 5 + q) (by omega)
    (fun d hd => Or.inr ⟨(chU d hd).1, (chU d hd).2.1, by have := (FC d hd).1.sum; have := (chU d hd).1; omega⟩)
    (fun d hd => feZero hw hs hsc K U3 (by omega) d (by omega))
  have F0 := FC 0 (by omega)
  simp only [Nat.add_zero] at F0
  have c0 := chU 0 (by omega)
  simp only [Nat.add_zero] at c0
  have hr3 : o + 5 + q < s.rows.length := by omega
  have hgD := gDrow (okRow hw hs hr3) (rowLt hw hs _) (nextLt hw hs _) F0.2.2.2.2.2
    (by simpa using (U3.fs 0 (by omega)).2 rfl) (qbWt3 hw hs hr3 F0.2.2.2.2.2)
    (Or.inr ⟨c0.1, c0.2.1, by have := F0.1.sum; omega⟩)
  have hjm : s.row o jm = k := by
    rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by
      rw [show s.row o kRDB = 0 from I0.kd 0 (by omega), show s.row o kRDE = 0 from I0.kd 1 (by omega),
        show s.row o kWEX = 1 from I0.kd 9 (by omega), show s.row o kPT = 0 from I0.kd 11 (by omega)]) (by omega), hj]
    omega
  have hdI := dIj_nat (rowLt hw hs _ _) (dCHm (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0.1 c0.2.2)
  have hdL := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (dCHml (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0.1 c0.2.2)
  rw [hsc _ hr3 tau (by decide), show s.row (o + 5 + q) jm = s.row o jm by
    have := K.pc (5 + q) (by omega) jm (by decide); rwa [show o + (5 + q) = o + 5 + q by omega] at this, hjm] at hdI
  rw [show s.row (o + 5 + q) clen = s.row o clen by
    have := K.pc (5 + q) (by omega) clen (by decide); rwa [show o + (5 + q) = o + 5 + q by omega] at this] at hdL
  exact ⟨_, hr3, hgD, hdI, hdL⟩

end

end ZkFormal.NearV3.UpsRows

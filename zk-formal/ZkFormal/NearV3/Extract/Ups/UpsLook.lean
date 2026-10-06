import ZkFormal.NearV3.Extract.Ups.UpsInd

/-!
# ZkFormal.NearV3.Extract.Ups.UpsLook — every part's digest is looked up at its length (M7e, step 1)

**`ups_look`**: `UpsExt0`, SHA (`UpsShaSeg`) and the `MEMD` match (`UpsMemdSeg`) give `UpsLookSeg`: the
digest of every part is looked up at exactly its length, so SHA hashes exactly its bytes.

* the root part: on `W3` (`DIGEST (msgId 12 (512τ + nQ), rlen)`, `nQ = j` and `rlen = qlen` on the root
  part; `rootLook`);
* the new leaf: by its parent (`RBI`, or a split branch with a new leaf: `rbiLook`, `spbLookY`) at 50, and the
  new leaf's part has 50 rows (`nlfLen`);
* every other part: by the part receiving its `MEMD` (`rdbLook`, `extUpLook`, `wexLook`, `spbLookC`) at
  `clen`, which is the child's length (`memdMatch`).

The parent's look lemma needs the parent's bytes (`< 256`), which SHA gives once the parent's own digest is
looked up: the induction runs down from the root (`parentOf`: the plan gives every part but the root a parent
above it).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## `W3`: the root digest lookup -/

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P)
include ok hC

theorem w3dI (hw3 : C wt3 = 1) :
    ((C dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((C tau : Nat) : Fp) + ((C nQ : Nat) : Fp)) := by
  have f := fact ok (e := .mul (c wt3) (sub (c dI) (upsId (c nQ)))) (memDigest (by simp [cDigest]))
  try simp only [upsId, mid] at f
  uev_simp
  simp only [cast_ofNat, hw3, cast1] at f
  grind

theorem w3dL (hw3 : C wt3 = 1) : ((C dL : Nat) : Fp) = ((C rlen : Nat) : Fp) := by
  have f := fact ok (e := .mul (c wt3) (sub (c dL) (c rlen))) (memDigest (by simp [cDigest]))
  uev_simp
  simp only [cast_ofNat, hw3, cast1] at f
  grind

end

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem w3gD (hw3 : C wt3 = 1) (hq : C qb = 0) : C gD = 1 := by
  have f := factN ok hC hD (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3))) (memDigest (by simp [cDigest]))
  simp only [winFr] at f
  nev_simp at f
  have := hC gD
  rw [P_lit] at this
  simp [hq, hw3] at f
  omega

end

/-! ## Plan facts -/

theorem kdRBI : ∀ m, m < 12 → UKind.all.getD m .RDB = .RBI → m = 5 := by decide
theorem kdNLF' : ∀ m, m < 12 → UKind.all.getD m .RDB = .NLF → m = 8 := by decide
theorem kdWEX : ∀ m, m < 12 → UKind.all.getD m .RDB = .WEX → m = 9 := by decide
theorem kdSPB : ∀ m, m < 12 → UKind.all.getD m .RDB = .SPB → m = 10 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The parent of a terminal part (but the last): the new leaf is under `RBI` or a split branch with a new
leaf; the moved node (part 0) under the split branch; any other under the next part, a wrapping extension. -/
theorem termPar : ∀ c, c < 11 → ∀ t, t < 3 → ∀ x, x < 4 → x + 1 < nTof c t →
    ((termPlan (UCase.all.getD c .LP) t).getD x .RDB = .NLF →
      (termPlan (UCase.all.getD c .LP) t).getD (x + 1) .RDB = .RBI ∨
      ((termPlan (UCase.all.getD c .LP) t).getD (x + 1) .RDB = .SPB ∧ spYN c = 1)) ∧
    ((termPlan (UCase.all.getD c .LP) t).getD x .RDB ≠ .NLF →
      (termPlan (UCase.all.getD c .LP) t).getD (x + 1) .RDB = .WEX ∨
      (x = 0 ∧ spRN c = 1 ∧ (((termPlan (UCase.all.getD c .LP) t).getD 1 .RDB = .SPB ∧ 1 < nTof c t) ∨
        ((termPlan (UCase.all.getD c .LP) t).getD 2 .RDB = .SPB ∧ 2 < nTof c t)))) := by
  decide

/-- The last terminal part is not the new leaf. -/
theorem termLast : ∀ c, c < 11 → ∀ t, t < 3 →
    (termPlan (UCase.all.getD c .LP) t).getD (nTof c t - 1) .RDB ≠ .NLF := by decide

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- The new leaf's part has 50 rows. -/
theorem nlfLen (k : Nat) (hk : k < ps.length) (hkd : kd k = 8) : ps[k].2 = 50 := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  rw [hkd] at K
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  obtain ⟨hlt0, hq0, hpf⟩ := pFirst hw hs hL k hk
  have hx : s.row ps[k].1 xcp = 0 := by
    have := (K.sel 0 K.pos).2.1
    simp only [Nat.add_zero] at this
    rw [this]; simp [xcpV, kdOf, UKind.all, b2n]
  obtain ⟨htl, hqhk, -⟩ := nlfHead (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd hx
  have := (leafShape hw hs U htl hq0 K.pf).1
  rw [this, hqhk]

/-- The root part's digest is looked up on `W3` at its length. -/
theorem rootLook (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    ∃ i, i < s.rows.length ∧ s.row i gD = 1 ∧ s.row i dI = upsIdN (s.row 0 tau) (k + 1) ∧ s.row i dL = ps[k].2 := by
  obtain ⟨h4, -, -, -, hw3⟩ := hL.walk
  have hlt : 3 < s.rows.length := by omega
  have ok3 := okRow hw hs hlt
  have hwk := hL.wk 3 (by omega)
  have hq : s.row 3 qb = 0 := by
    obtain ⟨ha, hact, -⟩ := kinds ok3 (rowLt hw hs _) (nextLt hw hs _)
    omega
  obtain ⟨hlt0, hq0, hpf⟩ := pFirst hw hs hL k hk
  have hr := (hP.root k hk).2 hroot
  obtain ⟨-, hjn, hql⟩ := rootPart (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _) hq0 hr
  have hj : s.row ps[k].1 j = k + 1 := (hL.part k hk).1
  have sc := hL.segc
  have hnQ : s.row 3 nQ = k + 1 := by
    rw [sc 3 hlt nQ (by decide), ← sc _ hlt0 nQ (by decide), ← hjn, hj]
  have hrl : s.row 3 rlen = ps[k].2 := by
    rw [sc 3 hlt rlen (by decide), ← sc _ hlt0 rlen (by decide), ← hql, qlenPart hw hs hL hP k hk]
  refine ⟨3, hlt, w3gD ok3 (rowLt hw hs _) (nextLt hw hs _) hw3 hq, ?_, ?_⟩
  · have := dIj_nat (rowLt hw hs _ _) (w3dI ok3 (rowLt hw hs _) hw3)
    rw [this, hnQ, sc 3 hlt tau (by decide)]
  · rw [natv (rowLt hw hs _ _) (rowLt hw hs _ _) (w3dL ok3 (rowLt hw hs _) hw3), hrl]

/-- **The parent of a part below the root**: the new leaf's is the next part (`RBI`, or a split branch with a
new leaf); any other part's is a part receiving its `MEMD`. -/
theorem parentOf (k : Nat) (hk1 : k + 1 < ps.length) :
    (kd k = 8 → kd (k + 1) = 5 ∨ (kd (k + 1) = 10 ∧ spYN ci = 1)) ∧
    (kd k ≠ 8 → ∃ p, ∃ hp : p < ps.length, k < p ∧ recvK ci (kd p) ∧ childK (kd p) p = k) := by
  obtain ⟨i1, i2, -, -⟩ := hP.ix
  have hT4 := nTof_le ci i1 ti i2
  rcases Nat.lt_or_ge (k + 1) (nTof ci ti) with hT | hT
  · obtain ⟨t0, -⟩ := hP.term k (by omega) (by omega)
    obtain ⟨t1, -⟩ := hP.term (k + 1) hk1 hT
    have k0 := (hP.part k (by omega)).1
    have k1 := (hP.part (k + 1) hk1).1
    obtain ⟨A, B⟩ := termPar ci i1 ti i2 k (by omega) hT
    rw [← t0, ← t1] at A
    rw [← t0, ← t1] at B
    refine ⟨fun h8 => ?_, fun h8 => ?_⟩
    · have := A (by rw [h8]; rfl)
      rcases this with h | ⟨h, hy⟩
      · exact .inl (kdRBI _ k1 h)
      · exact .inr ⟨kdSPB _ k1 h, hy⟩
    · have hne : UKind.all.getD (kd k) .RDB ≠ .NLF := fun h => h8 (kdNLF' _ k0 h)
      rcases B hne with h | ⟨hk0, hR, hp⟩
      · refine ⟨k + 1, hk1, by omega, .inr (.inr (.inl (kdWEX _ k1 h))), ?_⟩
        simp [childK, kdWEX _ k1 h]
      · have hex : ∃ p, 1 ≤ p ∧ p < nTof ci ti ∧ UKind.all.getD (kd p) .RDB = .SPB := by
          rcases hp with ⟨h, h'⟩ | ⟨h, h'⟩
          · refine ⟨1, Nat.le_refl _, h', ?_⟩
            rw [(hP.term 1 (by have := hP.len; omega) h').1]; exact h
          · refine ⟨2, by omega, h', ?_⟩
            rw [(hP.term 2 (by have := hP.len; omega) h').1]; exact h
        obtain ⟨p, hp1, hpT, hpS⟩ := hex
        have hpl : p < ps.length := by have := hP.len; omega
        have h10 := kdSPB _ (hP.part p hpl).1 hpS
        refine ⟨p, hpl, by omega, .inr (.inr (.inr (.inr ⟨h10, hR⟩))), ?_⟩
        simp [childK, h10, hk0]
  · have hU := (hP.upper (k + 1) hk1 hT).1
    refine ⟨fun h8 => ?_, fun h8 => ?_⟩
    · exfalso
      have hkT : k < nTof ci ti := by
        rcases Nat.lt_or_ge k (nTof ci ti) with h | h
        · exact h
        · have := (hP.upper k (by omega) h).1; omega
      have hkl : k = nTof ci ti - 1 := by omega
      obtain ⟨t0, -⟩ := hP.term k (by omega) hkT
      have := termLast ci i1 ti i2
      rw [← hkl, ← t0, h8] at this
      exact this rfl
    · refine ⟨k + 1, hk1, by omega, ?_, ?_⟩
      · rcases hU with h | h
        · rcases (show kd (k + 1) = 0 ∨ kd (k + 1) = 1 by omega) with h' | h'
          · exact .inl h'
          · exact .inr (.inl h')
        · exact .inr (.inr (.inr (.inl h)))
      · have : kd (k + 1) ≠ 10 := by omega
        simp [childK, this]


/-- **Every part's digest is looked up at its length** (from SHA and the `MEMD` match; downward from the
root). -/
theorem ups_look {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val) (HS : UpsShaSeg s ps) (HM : UpsMemdSeg s) :
    UpsLookSeg s ps := by
  suffices H : ∀ m, ∀ k (hk : k < ps.length), ps.length - k = m → ∃ i, i < s.rows.length ∧ s.row i gD = 1 ∧
      s.row i dI = upsIdN (s.row 0 tau) (k + 1) ∧ s.row i dL = ps[k].2 by
    intro k hk; exact H _ k hk rfl
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro k hk hm
  rcases Nat.lt_or_ge (k + 1) ps.length with hk1 | hk1
  rotate_left
  · exact rootLook hw hs hL hP k hk (by omega)
  have bytesOf : ∀ p (hp : p < ps.length), k < p → ∀ d, d < ps[p].2 → s.row (ps[p].1 + d) b < 256 := by
    intro p hp hkp
    obtain ⟨i, hi, hg, hI, hLn⟩ := ih (ps.length - p) (by omega) p hp rfl
    exact (HS i hi hg p hp hI hLn).1
  have hRd : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0 :=
    fun i hi hrd => (X0.reads i hi hrd).1
  obtain ⟨hA, hB⟩ := parentOf hw hs hL hP k hk1
  by_cases h8 : kd k = 8
  · have hl50 := nlfLen hw hs hL hP k hk h8
    obtain ⟨hsl, -, -, -, -, -, o5, -, -, o10, -⟩ := X0.srcOk (k + 1) hk1
    have hsrc := X0.srcEnc (k + 1) hk1
    rcases hA h8 with h5 | ⟨h10, hY⟩
    · obtain ⟨bv, cs, mm, hP', hbv, hmm, hkl, hslot⟩ := o5 h5
      rw [hP'] at hsrc hsl
      obtain ⟨i, hi, hg, hI, hLn⟩ := rbiLook hw hs hL hP (k + 1) hk1 h5 val (rbiSi hw hs hL hP (k + 1) hk1 h5) Pb bv cs mm
        X0.reads hsrc hsl hbv hmm hkl hslot X0.vlen X0.vbytes (bytesOf (k + 1) hk1 (by omega))
      exact ⟨i, hi, hg, hI, by rw [hLn, hl50]⟩
    · obtain ⟨oL, oE⟩ := o10 h10
      obtain ⟨i, hi, hg, hI, hLn⟩ := spbLookY hw hs hL hP (k + 1) hk1 h10 val Pb X0.reads (src (k + 1)) (.hash [])
        hsrc hsl oL oE X0.vlen X0.vbytes X0.digV X0.xy (bytesOf (k + 1) hk1 (by omega)) hY
      exact ⟨i, hi, hg, hI, by rw [hLn, hl50]⟩
  · obtain ⟨p, hp, hkp, hr, hcK⟩ := hB h8
    obtain ⟨c, hcc, hc, -, -, -, -, hcl⟩ := memdMatch hw hs hL hP HM p hp hr 0 (by omega)
    have hck : c = k := by rw [hcc, hcK]
    subst hck
    have hbp := bytesOf p hp hkp
    obtain ⟨hsl, o0, o1, -, -, -, -, -, -, o10, o11⟩ := X0.srcOk p hp
    have hsrc := X0.srcEnc p hp
    rcases hr with h | h | h | h | ⟨h, hR⟩
    · have hp1 : p = c + 1 := by simp [childK, h] at hcK; omega
      subst hp1
      obtain ⟨bv, cs, mm, cc, hP', hbv, hmm, hkl, hslot, hc32⟩ := o0 h
      rw [hP'] at hsrc
      obtain ⟨i, hi, hg, hI, hLn⟩ := rdbLook hw hs hL hP (c + 1) hp h Pb bv cs cc cc mm 0 X0.reads hsrc hbv hmm hkl
        hslot hc32 hbp
      exact ⟨i, hi, hg, hI, by rw [hLn, hcl]⟩
    · have hp1 : p = c + 1 := by simp [childK, h] at hcK; omega
      subst hp1
      obtain ⟨key, cc, mm, hP', hc32, hmm⟩ := o1 h
      rw [hP'] at hsrc hsl
      obtain ⟨i, hi, hg, hI, hLn⟩ := extUpLook hw hs hL hP (c + 1) hp (Or.inl h) Pb key cc cc mm 0 hRd hsrc
        (by omega) hc32 hmm hbp
      exact ⟨i, hi, hg, hI, by rw [hLn, hcl]⟩
    · have hp1 : p = c + 1 := by simp [childK, h] at hcK; omega
      subst hp1
      obtain ⟨i, hi, hg, hI, hLn⟩ := wexLook hw hs hL hP (c + 1) hp h (.hash [])
        ((partPlan hw hs hL hP (c + 1) hp).2.2 h) X0.tiLe hbp
      exact ⟨i, hi, hg, hI, by rw [hLn, hcl]⟩
    · have hp1 : p = c + 1 := by simp [childK, h] at hcK; omega
      subst hp1
      obtain ⟨cc, mm, hP', hc32, hmm⟩ := o11 h
      rw [hP'] at hsrc hsl
      obtain ⟨i, hi, hg, hI, hLn⟩ := extUpLook hw hs hL hP (c + 1) hp (Or.inr h) Pb [] cc cc mm 0 hRd hsrc
        (by omega) hc32 hmm hbp
      exact ⟨i, hi, hg, hI, by rw [hLn, hcl]⟩
    · have hc0 : c = 0 := by simp [childK, h] at hcK; omega
      subst hc0
      obtain ⟨oL, oE⟩ := o10 h
      obtain ⟨i, hi, hg, hI, hLn⟩ := spbLookC hw hs hL hP p hp h val Pb X0.reads (src p) (.hash [])
        hsrc hsl oL oE X0.vlen X0.vbytes X0.digV X0.xy hbp hR
      exact ⟨i, hi, hg, hI, by rw [hLn, hcl]⟩


/-- **The parts of a segment** from `UpsExt0`, SHA and the `MEMD` match: every part `k` emits
`nodeEnc (upsQ … k)` with exact `MEMD` limbs. -/
theorem ups_partsS {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val)
    (hsrcM : ∀ k, k < ps.length → isNode (src k) = true ∧ (src k).memD < 2 ^ 64)
    (HS : UpsShaSeg s ps) (HM : UpsMemdSeg s) :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) val kd sdx src k).memD) :=
  ups_partsI hw hs hL hP X0 hsrcM HS HM (ups_look hw hs hL hP X0 HS HM)

end

end ZkFormal.NearV3.UpsRows

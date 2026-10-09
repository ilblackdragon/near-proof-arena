import ZkFormal.NearV3.Extract.Ups.UpsShapeK

/-!
# ZkFormal.NearV3.Extract.Ups.UpsVb — `W0`'s value-length limbs are bytes (M7e, step 2; no AIR change)

`L0 L1 L2` are segment constants that no constraint range-checks on `W0`.  Every case has a part that emits a
fresh `VLEN` field `L0 L1 L2 0` (`vlenFresh`): `RLP` (`LP`), `RBR` (`BR`), `RBV` (`BV`), the new leaf `NLF`
(`BI LSa LSc ESn0 ESn1`), the split branch's value slot (`LSb ESl0 ESl1`) — `valKind`, by `decide`.  That part's
bytes go to SHA on `BYTES` and its digest is looked up at its length, so SHA's byte contract bounds **each limb
individually** by `256` (`vbPart`: the limbs are three of the part's emitted bytes).

The lookups do not use the limbs: `ups_look0` (`UpsLook`) needs only the reads, the sources and the walk facts
(the look lemmas `rbiLook`, `spbLookY`, `spbLookC` no longer take `vlen`/`vbytes`/`digV`).  So:

* **`ups_vbytes`**: segment SHA facts and lookups ⇒ `L0 L1 L2 < 256`;
* **`ups_vbytesE`**: from `UpsEnv` (`sha_seg`, `memd_seg`, `ups_look0`, `ups_shape`);
* **`ups_ext0V`** / **`ups_partsAllV`**: `UpsExt0` of every segment and its parts' bytes with exact `MEMD` limbs,
  from `UpsEnv` alone.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- A value-carrying kind: a fresh `VLEN` field. -/
def valK (c : Nat) (K : UKind) : Bool :=
  K == .RLP || K == .RBR || K == .RBV || K == .NLF || (K == .SPB && (c == 5 || c == 7 || c == 8))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Every case has a value-carrying part** (among its first two terminal parts). -/
theorem valKind : ∀ c, c < 11 → ∀ t, t < 3 →
    ∃ k, k < 2 ∧ k < nTof c t ∧ valK c ((termPlan (UCase.all.getD c .LP) t).getD k .RDB) = true := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem valK_kd : ∀ c, c < 11 → ∀ m, m < 12 → valK c (UKind.all.getD m .RDB) = true →
    m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 8 ∨ (m = 10 ∧ (c = 5 ∨ c = 7 ∨ c = 8)) := by decide

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **A value-carrying part's bytes bound the limbs**: its fresh `VLEN` rows are `L0 L1 L2 0`. -/
theorem vbPart (k : Nat) (hk : k < ps.length)
    (hkd : kd k = 2 ∨ kd k = 3 ∨ kd k = 4 ∨ kd k = 8 ∨ (kd k = 10 ∧ (ci = 5 ∨ ci = 7 ∨ ci = 8)))
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  have hsc := hL.segc
  obtain ⟨hlt0, hq0, hpf⟩ := pFirst hw hs hL k hk
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have ok0 := okRow hw hs hlt0
  have hkI : ∀ j, kd k = j → ∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = j then 1 else 0 :=
    fun j h m hm => by rw [I0.kd m hm, h]
  generalize hkk : kd k = ki at K hkd hkI
  generalize ps[k].1 = o at K U hbyte hlt0 hq0 hpf I0 ok0 hkI
  generalize ps[k].2 = ℓ at K U hbyte
  have hle := K.le
  -- the fresh `VLEN` field at `r`: its rows are bytes of the part
  have fromV : ∀ r, o ≤ r → r + 4 ≤ o + ℓ → rowsB s r 4 = [s.row 0 L0, s.row 0 L1, s.row 0 L2, 0] →
      s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
    intro r h1 h2 eV
    simp only [rowsB_four, List.cons.injEq, and_true] at eV
    obtain ⟨v0, v1, v2, -⟩ := eV
    have b0 := hbyte (r - o) (by omega); have b1 := hbyte (r - o + 1) (by omega)
    have b2 := hbyte (r - o + 2) (by omega)
    rw [show o + (r - o) = r by omega] at b0
    rw [show o + (r - o + 1) = r + 1 by omega] at b1
    rw [show o + (r - o + 2) = r + 2 by omega] at b2
    exact ⟨by rw [← v0]; exact b0, by rw [← v1]; exact b1, by rw [← v2]; exact b2⟩
  -- a leaf part (`RLP`, `NLF`): `VLEN` after the key
  have leafV : s.row o qtl = 1 → vcpV ci ki = 0 → s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
    intro htl hvz
    obtain ⟨hℓ, -, -, -, -, -, ⟨U3, s3⟩, -, -⟩ := leafShape hw hs U htl hq0 hpf
    exact fromV _ (by omega) (by omega) (vlenFresh hw hs hsc K U3 s3 (by omega) (by omega) hvz)
  -- a branch part with a value (`RBR`, `RBV`, `SPB`): `VLEN` after the tag
  have brV : s.row o qtb2 = 1 → vcpV ci ki = 0 → s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
    intro htb hvz
    obtain ⟨hℓ, -, -, ⟨U1, s1⟩, -⟩ := branchVShape hw hs U htb hq0 hpf
    exact fromV _ (by omega) (by omega) (vlenFresh hw hs hsc K U1 s1 (by omega) (by omega) hvz)
  rcases hkd with rfl | rfl | rfl | rfl | ⟨rfl, hc⟩
  · exact leafV (head_RLP ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (hkI 2 rfl)).2.2.1
      (by simp [vcpV, kdOf, UKind.all, b2n])
  · exact brV (head_RBR ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (hkI 3 rfl)).2.2.2.2.1
      (by simp [vcpV, kdOf, UKind.all, b2n])
  · exact brV (head_RBV ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (hkI 4 rfl)).2.2.1
      (by simp [vcpV, kdOf, UKind.all, b2n])
  · exact leafV (head_NLF ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (hkI 8 rfl)).2.2.1
      (by simp [vcpV, kdOf, UKind.all, b2n])
  · have hc' : 4 ≤ ci ∧ ci ≤ 10 := by omega
    obtain ⟨-, -, htb2, -⟩ := head_SPB ok0 (rowLt hw hs _) (nextLt hw hs _) hpf (hkI 10 rfl) I0.cs hc'.1 hc'.2
    refine brV (by rw [htb2]; unfold spVN; rcases hc with rfl | rfl | rfl <;> rfl) ?_
    simp only [vcpV, kdOf, UKind.all, b2n, csOf]
    rcases hc with rfl | rfl | rfl <;> rfl

/-- **`vbytes`**: the segment's SHA facts and lookups bound `W0`'s value-length limbs. -/
theorem ups_vbytes (HS : UpsShaSeg s ps) (HL : UpsLookSeg s ps) :
    s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
  obtain ⟨i1, i2, -, -⟩ := hP.ix
  obtain ⟨k, -, hkT, hK⟩ := valKind ci i1 ti i2
  have hk : k < ps.length := by have := hP.len; omega
  have hkd := (hP.term k hk hkT).1
  rw [← hkd] at hK
  obtain ⟨i, hi, hg, hI, hLn⟩ := HL k hk
  exact vbPart hw hs hL hP k hk (valK_kd ci i1 (kd k) (hP.part k hk).1 hK) (HS i hi hg k hk hI hLn).1

end

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s L ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include E hs hL hP

/-- **`vbytes` from the other tables.** -/
theorem ups_vbytesE : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256 := by
  have hw := E.ups
  have HS := sha_seg hw (Link3.ShaHyp.sha E.sha) othersU E.bytesU E.othU E.digU E.tauD
    (ups_idBound E.node E.head E.par E.ups E.upb E.tauB) s hs L ps fls wsl hL
  have HM := memd_seg hw E.memd E.tauD s hs
  have HL := ups_look0 hw hs hL hP (upb_reads E.node E.ups E.upb hs)
    (fun k hk => (ups_srcEnc E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP k hk).1)
    (ups_srcOk E.node E.head E.val E.par E.vpar E.sha E.vpost E.vpostLen E.ups E.upb hs hL hP (ups_shape E hs hL hP))
    (ups_tiLe E.walk E.ups hs hL hP) (ups_xy E.ups hs hL hP) HS HM
  exact ups_vbytes hw hs hL hP HS HL

/-- **`UpsExt0` of every segment** from the other tables alone. -/
theorem ups_ext0V :
    UpsExt0 s ps ci ti si kd sdx (postB vs) (srcOf (Rpost vs es) (Vpost vs es pv) s ps) (sv (s.row 0 tau)) :=
  ups_ext0S E hs hL hP (ups_vbytesE E hs hL hP)

/-- **The parts of every segment** from the other tables alone: every part `k` emits `nodeEnc (upsQ … k)` and
(not the new leaf) sends its node's exact `memory_usage` on `MEMD`. -/
theorem ups_partsAllV :
    ∀ k (hk : k < ps.length),
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx
        (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx (srcOf (Rpost vs es) (Vpost vs es pv) s ps) k).memD) :=
  ups_partsAllS E hs hL hP (ups_vbytesE E hs hL hP)

end

end ZkFormal.NearV3.UpsRows

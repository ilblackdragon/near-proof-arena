import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsLook
import ZkFormal.NearV3.Extract.Ups.UpsVb
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
attribute [local irreducible] UpsSeg.row UpsSeg.next
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
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

end ZkFormal.NearV3.Render.UpsRelay.Extract

import ZkFormal.NearV3.Render.Ups.CompactExtract.RbvBytes
import ZkFormal.NearV3.Extract.Ups.RbrBytes
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- `SR` rotates on `VLEN` rows. -/
theorem srRot (hv : C sVLEN = 1) :
    D (SR 0) = C (SR 1) ∧ D (SR 1) = C (SR 2) ∧ D (SR 2) = C (SR 3) ∧ D (SR 3) = C (SR 0) := by
  have g := fun i (hi : i < 4) => factN ok hC hD (e := Expr.mul (c sVLEN) (sub (n (SR i)) (c (SR ((i + 1) % 4)))))
    (memMem (by
      unfold cMem; simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))))
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega); have g3 := g 3 (by omega)
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a (SR 0); have := a (SR 1); have := a (SR 2); have := a (SR 3)
  have := d (SR 0); have := d (SR 1); have := d (SR 2); have := d (SR 3)
  nev_simp at g0 g1 g2 g3
  simp [hv] at g0 g1 g2 g3
  omega

/-- `SR` is constant on the other rows inside a part. -/
theorem srConst (hq : C qb = 1) (hpl : C pl = 0) (hv : C sVLEN = 0) (hm : C sMEM = 0) :
    ∀ i, i < 4 → D (SR i) = C (SR i) := by
  intro i hi
  have g := factN ok hC hD (e := Expr.mul (mul3 (c qb) (not (c pl)) (not (.add (c sVLEN) (c sMEM))))
    (sub (n (SR i)) (c (SR i)))) (memMem (by
      unfold cMem; simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩))
  have := hC (SR i); have := hD (SR i)
  simp only [P_lit] at *
  nev_simp at g
  simp [hq, hpl, hv, hm] at g
  omega

/-- An `RBR` part reads the old value length on its `VLEN` rows. -/
theorem rdVlenRBR (hq : C qb = 1) (hv : C sVLEN = 1) (hk : C kRBR = 1) (hcp : C cp = 0) (hoh : OneHot C) :
    C rd = 1 := by
  have f := factN ok hC hD (e := .mul (c qb) (sub (c rd) (.add (c cp) (sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF)), c rdc])))) (memBytes (by simp [cBytes]))
  have hS := hoh.sum
  have hb := hoh.bs
  have hz : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
    omega
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have hrdc := rdcOff ok hC hD z6
  have := hC rd
  simp only [P_lit] at *
  simp only [sumc, kM, List.map_cons, List.map_nil] at f
  nev_simp at f
  simp [hq, hv, hk, hcp, hrdc, z0, z1, z2, z3, z4, z5, z6, z7] at f
  omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **A branch value replaced** (`RBR`): its bytes are `nodeEnc (qRBR sl cs m val)`. -/
theorem ups_rbrBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 3) (val : NearSpec.Bytes)
    (Pb : Nat → List Nat) (sl : NearSpec.Slot) (cs : NearSpec.Kids) (m : Nat)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hdig : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 0 →
      s.row i dL = val.length → regN (s.row i) = (NearSpec.sha256 val).map UInt8.toNat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.branch (some sl) cs m)).map UInt8.toNat)
    (hsl : sl.valueRef.length = 36) (hslen : sl.len < 2 ^ 32) (hm : m < 2 ^ 64)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRBR sl cs m val)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRBR sl cs m val).memD := by
  have K := partK hw hs hL hP k hk
  have hup := upZero hw hs hL hP k hk (by omega)
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hsrc hup ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨hx0, hv0, -, -, htb2, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_RBR ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  obtain ⟨hℓ, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, ⟨U2, s2⟩, ⟨U3, s3⟩, W, ⟨U5, s5⟩⟩ := branchVShape hw hs U htb2 hq0 K.pf
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  -- TAG
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 2 by omega] at eT
  -- VLEN, VH (fresh)
  have hvz : vcpV ci 3 = 0 := by simp [vcpV, kdOf, UKind.all, b2n]
  have eV := vlenFresh hw hs hsc K U1 s1 (by omega) (by omega) hvz
  have eV' := eV
  rw [rowsB_four] at eV'
  simp only [List.cons.injEq, and_true] at eV'
  obtain ⟨v0, v1, v2, -⟩ := eV'
  have hL0 : s.row 0 L0 < 256 := by rw [← v0]; simpa using hbyte 1 (by omega)
  have hL1 : s.row 0 L1 < 256 := by rw [← v1]; have := hbyte 2 (by omega); rwa [show o + 2 = o + 1 + 1 by omega] at this
  have hL2 : s.row 0 L2 < 256 := by rw [← v2]; have := hbyte 3 (by omega); rwa [show o + 3 = o + 1 + 2 by omega] at this
  obtain ⟨eW, hgD, hdI, hdL⟩ := vhFresh hw hs hsc K U2 s2 (by omega) (by omega) hvz ⟨hL0, hL1, hL2⟩
  have hD := hdig (o + 5) (by omega) hgD hdI (by rw [hdL, hlen])
  -- the row states
  have stAt : ∀ d, 1 ≤ d → d < 47 + 32 * ww → OneHot (s.row (o + d)) ∧ o + d < s.rows.length ∧
      IxOf (s.row (o + d)) ci ti di si 3 (sdx k) ∧ (∀ x ∈ partConst, s.row (o + d) x = s.row o x) ∧
      s.row (o + d) qb = 1 ∧ (d < 5 → s.row (o + d) sVLEN = 1) ∧ (5 ≤ d → d < 37 → s.row (o + d) sVH = 1) ∧
      (37 ≤ d → d < 39 → s.row (o + d) sBM = 1) ∧ (39 ≤ d → d < 39 + 32 * ww → s.row (o + d) sCH = 1) ∧
      (39 + 32 * ww ≤ d → s.row (o + d) sMEM = 1) := by
    intro d h1 h2
    rcases Nat.lt_or_ge d 5 with h | h
    · have F := kField hw hs hsc K U1 s1 (by omega) (by omega) (d - 1) (by omega)
      rw [show o + 1 + (d - 1) = o + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, fun _ => (stOf_inv a1).2.2.2.2.1 a2, fun h' => by omega, fun h' => by omega,
        fun h' => by omega, fun h' => by omega⟩
    rcases Nat.lt_or_ge d 37 with h' | h'
    · have F := kField hw hs hsc K U2 s2 (by omega) (by omega) (d - 5) (by omega)
      rw [show o + 5 + (d - 5) = o + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, fun h'' => by omega, fun _ _ => (stOf_inv a1).2.2.2.2.2.1 a2, fun h'' => by omega,
        fun h'' => by omega, fun h'' => by omega⟩
    rcases Nat.lt_or_ge d 39 with h'' | h''
    · have F := kField hw hs hsc K U3 s3 (by omega) (by omega) (d - 37) (by omega)
      rw [show o + 37 + (d - 37) = o + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, fun h3 => by omega, fun h3 => by omega, fun _ _ => (stOf_inv a1).2.2.2.2.2.2.1 a2,
        fun h3 => by omega, fun h3 => by omega⟩
    rcases Nat.lt_or_ge d (39 + 32 * ww) with h3 | h3
    · have hWe := W ((d - 39) / 32) (by omega)
      have F := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega) ((d - 39) % 32) (by omega)
      rw [show o + 39 + 32 * ((d - 39) / 32) + (d - 39) % 32 = o + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, fun h4 => by omega, fun h4 => by omega, fun h4 => by omega,
        fun _ _ => (stOf_inv a1).2.2.2.2.2.2.2.1 a2, fun h4 => by omega⟩
    · have F := kField hw hs hsc K U5 s5 (by omega) (by omega) (d - (39 + 32 * ww)) (by omega)
      rw [show o + 39 + 32 * ww + (d - (39 + 32 * ww)) = o + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, fun h4 => by omega, fun h4 => by omega, fun h4 => by omega, fun h4 => by omega,
        fun _ => (stOf_inv a1).2.2.2.2.2.2.2.2 a2⟩
  -- direct reads: `rb = Pb[qpos]`
  have readAt : ∀ d, 1 ≤ d → d < 47 + 32 * ww → s.row (o + d) rd = 1 →
      s.row (o + d) rb = (Pb (s.row o sN)).getD d 0 ∧ s.row (o + d) plen = (Pb (s.row o sN)).length := by
    intro d h1 h2 hrd
    obtain ⟨hoh, hlt, hI, hpc, -⟩ := stAt d h1 h2
    have hsp := dirRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hI (by omega) hrd
    rw [(U.rows d (by omega)).2.1] at hsp
    have := hR (o + d) hlt hrd
    rwa [hsp, hpc sN (by decide)] at this
  -- the old value length: read on the `VLEN` rows into `SR`
  have rdV : ∀ t, t < 4 → s.row (o + 1 + t) rd = 1 ∧
      s.row (o + 1 + t) rb = (Pb (s.row o sN)).getD (1 + t) 0 ∧ s.row (o + 1 + t) rb = s.row (o + 1 + t) (SR 0) := by
    intro t ht
    obtain ⟨hoh, hlt, hI, hpc, hq, hV, -⟩ := stAt (1 + t) (by omega) (by omega)
    rw [show o + (1 + t) = o + 1 + t by omega] at hoh hlt hI hpc hq hV
    have hvl := hV (by omega)
    have hcp : s.row (o + 1 + t) cp = 0 := cpZero hw hs (by
      rw [cpVLEN (okRow hw hs hlt) (rowLt hw hs _) hoh.sum hvl, hpc vcp (by decide), hv0])
    have hrd := rdVlenRBR (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq hvl (hI.kd 3 (by omega)) hcp hoh
    have hr := readAt (1 + t) (by omega) (by omega) (by rwa [show o + (1 + t) = o + 1 + t by omega])
    rw [show o + (1 + t) = o + 1 + t by omega] at hr
    refine ⟨hrd, hr.1, natv (rowLt hw hs _ _) (rowLt hw hs _ _) (rVLEN (okRow hw hs hlt) (rowLt hw hs _) hoh.sum hrd hvl)⟩
  -- `SR` along the part
  have nx := fun d (hd : d + 1 < 47 + 32 * ww) => compactNext (s:=s) (i := o + d) (by omega)
  have rot := fun t (ht : t < 4) => by
    obtain ⟨-, hlt, -, -, -, hV, -⟩ := stAt (1 + t) (by omega) (by omega)
    have := srRot (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (hV (by omega))
    rw [nx (1 + t) (by omega), show o + (1 + t) + 1 = o + 1 + (t + 1) by omega,
      show o + (1 + t) = o + 1 + t by omega] at this
    exact this
  have r1 := rot 0 (by omega); have r2 := rot 1 (by omega); have r3 := rot 2 (by omega); have r4 := rot 3 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at r1 r2 r3 r4
  have Sv : ∀ t, t < 4 → s.row (o + 1 + t) (SR 0) = s.row (o + 1) (SR t) := by
    intro t ht
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
    · rfl
    · rw [r1.1]
    · rw [r2.1, r1.2.1]
    · rw [r3.1, r2.2.1, r1.2.2.1]
  have S5 : ∀ j, j < 4 → s.row (o + 5) (SR j) = s.row (o + 1) (SR j) := by
    intro j hj
    rw [show o + 5 = o + 1 + 4 by omega]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [r4.1, r3.2.1, r2.2.2.1, r1.2.2.2]
    · rw [r4.2.1, r3.2.2.1, r2.2.2.2, r1.1]
    · rw [r4.2.2.1, r3.2.2.2, r2.1, r1.2.1]
    · rw [r4.2.2.2, r3.1, r2.2.1, r1.2.2.1]
  have Sk : ∀ d, 5 ≤ d → d ≤ 39 + 32 * ww → ∀ j, j < 4 → s.row (o + d) (SR j) = s.row (o + 1) (SR j) := by
    intro d
    induction d with
    | zero => intro h; omega
    | succ d ih =>
      intro h1 h2 j hj
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact S5 j hj
      · obtain ⟨hoh, hlt, -, hpc, hq, hV, hH, hB, hC', hM⟩ := stAt d (by omega) (by omega)
        have hpl : s.row (o + d) pl = 0 := by
          rcases plBool hw hs hlt with h' | h'
          · exact h'
          · have := ((U.rows d (by omega)).2.2.2.1).1 h'; omega
        have hv0' : s.row (o + d) sVLEN = 0 := by
          have := hoh.bs; have := hoh.sum
          rcases Nat.lt_or_ge d 37 with a | a
          · have := hH (by omega) a; omega
          rcases Nat.lt_or_ge d 39 with a' | a'
          · have := hB a a'; omega
          · have := hC' a' (by omega); omega
        have hm0 : s.row (o + d) sMEM = 0 := by
          have := hoh.bs; have := hoh.sum
          rcases Nat.lt_or_ge d 37 with a | a
          · have := hH (by omega) a; omega
          rcases Nat.lt_or_ge d 39 with a' | a'
          · have := hB a a'; omega
          · have := hC' a' (by omega); omega
        have := srConst (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq hpl hv0' hm0 j hj
        rw [nx d (by omega), show o + d + 1 = o + (d + 1) by omega] at this
        rw [this]; exact ih (by omega) (by omega) j hj
  -- the copied bitmap and windows (`spos = qpos`)
  have copyAt : ∀ d, d < 2 + 32 * ww → s.row (o + 37 + d) cp = 1 ∧ s.row (o + 37 + d) rd = 1 ∧
      (s.row (o + 37 + d) sBM = 0 ∨ (s.row (o + 37 + d) ba0 = 0 ∧ s.row (o + 37 + d) ba1 = 0)) ∧
      s.row (o + 37 + d) spos = 37 + d ∧ s.row (o + 37 + d) sN = s.row o sN := by
    intro d hd
    obtain ⟨hoh, hlt, hI, hpc, hq, -, -, hB, hC', hM⟩ := stAt (37 + d) (by omega) (by omega)
    rw [show o + (37 + d) = o + 37 + d by omega] at hoh hlt hI hpc hq hB hC' hM
    have hok := okRow hw hs hlt
    have hs1 := hoh.sum
    have hcp : s.row (o + 37 + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rcases Nat.lt_or_ge d 2 with h | h
      · rw [cpBM hok (rowLt hw hs _) hs1 (hB (by omega) (by omega)), show s.row (o + 37 + d) kRDB = 0 from hI.kd 0 (by omega),
          show s.row (o + 37 + d) kRBR = 1 from hI.kd 3 (by omega), show s.row (o + 37 + d) kRBV = 0 from hI.kd 4 (by omega),
          show s.row (o + 37 + d) kRBI = 0 from hI.kd 5 (by omega)]; rfl
      · have hch := hC' (by omega) (by omega)
        rw [cpCH hok (rowLt hw hs _) hs1 hch, chCopy hok (rowLt hw hs _) (nextLt hw hs _) hch (by
          rw [show s.row (o + 37 + d) kRBR = 1 from hI.kd 3 (by omega), show s.row (o + 37 + d) kRBV = 0 from hI.kd 4 (by omega),
            show s.row (o + 37 + d) kMVE = 0 from hI.kd 7 (by omega)])]; rfl
    have hx : s.row (o + 37 + d) xcp = 0 := by rw [hpc xcp (by decide), hx0]
    have notTV : s.row (o + 37 + d) sTAG = 0 ∧ s.row (o + 37 + d) sVLEN = 0 := by
      have := hoh.bs
      rcases Nat.lt_or_ge d 2 with h' | h'
      · have := hB (by omega) (by omega); omega
      · have := hC' (by omega) (by omega); omega
    have hrd : s.row (o + 37 + d) rd = 1 := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh
      (fun h => by omega) (fun h => ⟨hI.kd 6 (by omega), hI.kd 7 (by omega)⟩) (fun h => by omega)
      (fun _ => hx) (rdcUp0 hok (rowLt hw hs _) (nextLt hw hs _) (by rw [hpc _ (by decide), hup]))
    have hba : s.row (o + 37 + d) ba0 = 0 ∧ s.row (o + 37 + d) ba1 = 0 := by
      have := (kSel hw hs hsc K (r := o + 37 + d) (by omega) (by omega))
      rw [this.2.2.1, this.2.2.2.1]; simp [ba0V, ba1V, kdOf, UKind.all, b2n]
    refine ⟨hcp, hrd, Or.inr hba, ?_, hpc sN (by decide)⟩
    rw [dirRow hok (rowLt hw hs _) (nextLt hw hs _) hI (by omega) hrd]
    have := (U.rows (37 + d) (by omega)).2.1; rwa [show o + (37 + d) = o + 37 + d by omega] at this
  -- the source's length, from a `MEM` read
  have FM0 := stAt (39 + 32 * ww) (by omega) (by omega)
  have hrdM : s.row (o + (39 + 32 * ww)) rd = 1 :=
    rdMem (okRow hw hs FM0.2.1) (rowLt hw hs _) (nextLt hw hs _) FM0.2.2.2.2.1 (FM0.2.2.2.2.2.2.2.2.2 (by omega))
      (FM0.2.2.1.kd 8 (by omega)) FM0.1
  have hpl := (readAt (39 + 32 * ww) (by omega) (by omega) hrdM).2
  have hpM := pMEM (okRow hw hs FM0.2.1) (rowLt hw hs _) FM0.1.sum hrdM (FM0.2.2.2.2.2.2.2.2.2 (by omega))
  have hidx : s.row (o + (39 + 32 * ww)) idx = 0 := by
    have := U5.idx 0 (by omega); rwa [show o + 39 + 32 * ww + 0 = o + (39 + 32 * ww) by omega] at this
  have hsp0 : s.row (o + (39 + 32 * ww)) spos = 39 + 32 * ww := by
    rw [dirRow (okRow hw hs FM0.2.1) (rowLt hw hs _) (nextLt hw hs _) FM0.2.2.1 (by omega) hrdM,
      (U.rows (39 + 32 * ww) (by omega)).2.1]
  rw [hidx, hsp0] at hpM
  have hPlen : (Pb (s.row o sN)).length = 47 + 32 * ww := by
    rw [← hpl]
    have e : ((47 + 32 * ww : Nat) : Fp) = ((s.row (o + (39 + 32 * ww)) plen : Nat) : Fp) := by
      rw [show 47 + 32 * ww = (39 + 32 * ww) + 8 by omega, natCast_add]
      rw [cast0] at hpM
      grind
    exact (natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e).symm
  -- the source bytes
  have hsrcL : (nodeEnc (.branch (some sl) cs m)).length = 47 + (NearSpec.Kids.hashes cs).length := by
    simp [nodeEnc, NearSpec.u16, leN_length, u64_length, hsl]; omega
  have hH : (NearSpec.Kids.hashes cs).length = 32 * ww := by
    have := congrArg List.length hsrc; rw [List.length_map, hsrcL, hPlen] at this; omega
  have hvr : (sl.valueRef.map UInt8.toNat).take 4 = (NearSpec.u32 sl.len).map UInt8.toNat := by
    cases sl <;> simp [NearSpec.Slot.valueRef, NearSpec.Slot.len, List.take_append_of_le_length, u32_length]
  have cC := copyRunB hw hs Pb hR (r := o + 37) (n := 2 + 32 * ww) (δ := 37) (N := s.row o sN) (by omega)
    (by omega) copyAt
  have hP1 : ((Pb (s.row o sN)).drop 37).take (2 + 32 * ww) =
      (NearSpec.u16 (NearSpec.kidsBitmap cs 0) ++ NearSpec.Kids.hashes cs).map UInt8.toNat := by
    have e : (nodeEnc (.branch (some sl) cs m)).map UInt8.toNat = ([UInt8.toNat 2] ++ sl.valueRef.map UInt8.toNat) ++
        ((NearSpec.u16 (NearSpec.kidsBitmap cs 0)).map UInt8.toNat ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++
          (NearSpec.u64 m).map UInt8.toNat)) := by simp [nodeEnc]
    rw [hsrc, e, List.drop_left' (by simp [hsl]), ← List.append_assoc,
      List.take_left' (by simp [NearSpec.u16, leN_length, hH])]
    simp
  rw [hP1] at cC
  -- the old length register on `MEM`
  have hS : s.row (o + 39 + 32 * ww) (SR 0) + 256 * s.row (o + 39 + 32 * ww) (SR 1) +
      65536 * s.row (o + 39 + 32 * ww) (SR 2) + 16777216 * s.row (o + 39 + 32 * ww) (SR 3) = sl.len := by
    have e : ∀ j, j < 4 → s.row (o + 39 + 32 * ww) (SR j) = ((NearSpec.u32 sl.len).map UInt8.toNat).getD j 0 := by
      intro j hj
      have := Sk (39 + 32 * ww) (by omega) (by omega) j hj
      rw [show o + (39 + 32 * ww) = o + 39 + 32 * ww by omega] at this
      rw [this, ← Sv j hj, ← (rdV j hj).2.2, (rdV j hj).2.1, hsrc]
      have e : (nodeEnc (.branch (some sl) cs m)).map UInt8.toNat = ([UInt8.toNat 2] ++ sl.valueRef.map UInt8.toNat) ++
          ((NearSpec.u16 (NearSpec.kidsBitmap cs 0)).map UInt8.toNat ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++
            (NearSpec.u64 m).map UInt8.toNat)) := by simp [nodeEnc]
      rw [e]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simp [hsl]; omega), List.getElem?_append_right (by simp)]
      rw [show 1 + j - [UInt8.toNat 2].length = j by simp]
      have : (sl.valueRef.map UInt8.toNat)[j]? = ((NearSpec.u32 sl.len).map UInt8.toNat)[j]? := by
        rw [← hvr, List.getElem?_take_of_lt hj]
      rw [this]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
    simp [toNats_u32]
    omega
  -- MEM
  have R5 := memRegs hw hs hsc K U5 s5 (by omega) (by omega)
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (39 + 32 * ww + i) (by omega) x hx
    rwa [show o + (39 + 32 * ww + i) = o + 39 + 32 * ww + i by omega] at this
  have rbM : ∀ i, i < 8 → s.row (o + 39 + 32 * ww + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
    intro i hi
    obtain ⟨hoh, hlt, hI, -, hq, -, -, -, -, hM⟩ := stAt (39 + 32 * ww + i) (by omega) (by omega)
    have hrd := rdMem (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq (hM (by omega)) (hI.kd 8 (by omega)) hoh
    have := (readAt (39 + 32 * ww + i) (by omega) (by omega) hrd).1
    rw [show o + (39 + 32 * ww + i) = o + 39 + 32 * ww + i by omega] at this
    rw [this, hsrc]
    simp only [nodeEnc, List.map_append, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [NearSpec.u16, leN_length, hH, hsl]; omega)]
    simp [NearSpec.u16, leN_length, hH, hsl]
    rw [show 39 + 32 * ww + i - (36 + (2 + 32 * ww) + 1) = i by omega]
  have hA : limbs (fun i => s.row (o + 39 + 32 * ww + i) rb) 8 = m := by
    rw [show limbs (fun i => s.row (o + 39 + 32 * ww + i) rb) 8 =
        limbs (fun i => ((NearSpec.u64 m).map UInt8.toNat).getD i 0) 8 by
      simp only [limbs8]; rw [rbM 0 (by omega), rbM 1 (by omega), rbM 2 (by omega), rbM 3 (by omega),
        rbM 4 (by omega), rbM 5 (by omega), rbM 6 (by omega), rbM 7 (by omega)], limbs_u64]
    omega
  have hSb : ∀ i, bAt [s.row (o + 39 + 32 * ww) (SR 0), s.row (o + 39 + 32 * ww) (SR 1),
      s.row (o + 39 + 32 * ww) (SR 2), s.row (o + 39 + 32 * ww) (SR 3)] i < 256 := by
    intro i
    have e : ∀ j, j < 4 → s.row (o + 39 + 32 * ww) (SR j) < 256 := by
      intro j hj
      have := Sk (39 + 32 * ww) (by omega) (by omega) j hj
      rw [show o + (39 + 32 * ww) = o + 39 + 32 * ww by omega] at this
      rw [this, ← Sv j hj, ← (rdV j hj).2.2, (rdV j hj).2.1, hsrc]
      exact toNats_lt _ _
    simp only [bAt, List.getD_eq_getElem?_getD]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i ≥ 4 by omega) with rfl | rfl | rfl | rfl | h
    · simpa using e 0 (by omega)
    · simpa using e 1 (by omega)
    · simpa using e 2 (by omega)
    · simpa using e 3 (by omega)
    · simp [List.getElem?_eq_none (show [s.row (o + 39 + 32 * ww) (SR 0), s.row (o + 39 + 32 * ww) (SR 1),
        s.row (o + 39 + 32 * ww) (SR 2), s.row (o + 39 + 32 * ww) (SR 3)].length ≤ i by simp; omega)]
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U U5 s5 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + 39 + 32 * ww + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      have hLb : bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i < 256 := by
        simp only [bAt, List.getD_eq_getElem?_getD]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i ≥ 3 by omega) with rfl | rfl | rfl | h
        · simpa using hL0
        · simpa using hL1
        · simpa using hL2
        · simp [List.getElem?_eq_none (show [s.row 0 L0, s.row 0 L1, s.row 0 L2].length ≤ i by simp; omega)]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [inA, pc5 i hi useA (by decide), huA, Nat.one_mul, rbM i hi]
        have := toNats_lt (NearSpec.u64 m) i; omega
      · simp only [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL, (R5 i hi).2.1]; omega
      · simp only [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc,
          (R5 i hi).2.2]
        have := hSb i; omega
      · simp [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc, heL, heS]
      · have := hbyte (39 + 32 * ww + i) (by omega)
        rwa [show o + (39 + 32 * ww + i) = o + 39 + 32 * ww + i by omega] at this)
  simp only [hKc, heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hA, hS] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + 39 + 32 * ww) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    simp only [UpsSpec.qRBR, NearSpec.valueMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?, Option.getD_some,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    omega
  -- assemble
  rw [hBy, eT, eV, eW, hD, show rowsB s (o + 37) 2 ++ (rowsB s (o + 39) (32 * ww) ++ rowsB s (o + 39 + 32 * ww) 8) =
    rowsB s (o + 37) (2 + 32 * ww) ++ rowsB s (o + 39 + 32 * ww) 8 by
      rw [rowsB_append, List.append_assoc, show o + 37 + 2 = o + 39 by omega], cC, eM]
  simp only [UpsSpec.qRBR, nodeEnc, NearSpec.Slot.valueRef, NearSpec.valueMem, List.map_append, List.map_cons,
    List.map_nil, toNats_u32, List.append_assoc, List.cons_append, List.nil_append]
  have e1 : val.length % 256 = s.row 0 L0 := by omega
  have e2 : val.length / 256 % 256 = s.row 0 L1 := by omega
  have e3 : val.length / 65536 % 256 = s.row 0 L2 := by omega
  have e4 : val.length / 16777216 % 256 = 0 := by omega
  rw [e1, e2, e3, e4]
  simp only [List.cons.injEq, true_and, List.append_cancel_left_eq]
  refine ⟨rfl, ?_⟩
  congr 2
  simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  omega

end

end ZkFormal.NearV3.Render.UpsRelay.Extract

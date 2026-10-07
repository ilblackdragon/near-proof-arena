import ZkFormal.NearV3.Extract.Ups.UpsPath

/-!
# ZkFormal.NearV3.Extract.Ups.UpsTag — what a part reads of its source's first bytes (M7e, step 1)

The source record's constructor is read off the part's own rows:

* **`tagCopy`**: a direct-copy part (`RDB RDE RLP RBR PT`) copies the source's byte 0 onto its `TAG` row, whose
  byte is the part's node type (`qtb1 + 2·qtb2 + 3·qte`, `gramRow`): so the source's tag is the part's;
* **`ptHead`**: a pass-through also copies bytes 1 and 5 (`HPL`, `HPF`), pinned to `qhk = 1` and `0` (`bHPFp`);
* **`tagNib5`**: a moved-key part (`MVL`, `MVE`) and an `ESx1` split branch (`xcp = 1`) read the source's byte 5
  on their `TAG` row (`spos = 5`), whose high nibble is `2·qtl + podd` (`rTAG`, `rTAGh`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- The `TAG` read of a moved-key part or an `ESx1` split branch: the source's byte, `hi = 2·qtl + podd`. -/
theorem tagNib (hoh : OneHot C) (hT : C sTAG = 1)
    (hk' : ((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp) + ((C xcp : Nat) : Fp) = 1)
    (hqt : C qtl ≤ 1) (hpo : C podd ≤ 1) :
    C (reg 0) + 2 * C (reg 1) + 4 * C (reg 2) + 8 * C (reg 3) = 2 * C qtl + C podd ∧
    C rb = 16 * (C (reg 0) + 2 * C (reg 1) + 4 * C (reg 2) + 8 * C (reg 3)) +
      (C (reg 4) + 2 * C (reg 5) + 4 * C (reg 6) + 8 * C (reg 7)) := by
  have bt := nibBits ok hC hD (by have := hoh.sum; have := hoh.bs; omega)
  have b0 := bt 0 (by omega); have b1 := bt 1 (by omega); have b2 := bt 2 (by omega); have b3 := bt 3 (by omega)
  have b4 := bt 4 (by omega); have b5 := bt 5 (by omega); have b6 := bt 6 (by omega); have b7 := bt 7 (by omega)
  have f1 := rTAG ok hC hoh.sum hT
  have f2 := rTAGh ok hC hoh.sum hT
  rw [hk'] at f1 f2
  simp only [hb, lb, Nat.pow_zero, Nat.pow_succ] at f1 f2
  refine ⟨?_, ?_⟩
  · apply natv (by rw [P_lit]; omega) (by rw [P_lit]; omega)
    simp only [natCast_add, natCast_mul]
    grind
  · apply natv (hC _) (by rw [P_lit]; omega)
    simp only [natCast_add, natCast_mul]
    grind

/-- A `TAG` row of a moved-key part or an `ESx1` split branch reads. -/
theorem rdTag (hq : C qb = 1) (hoh : OneHot C) (hcp : C cp = 0) (hT : C sTAG = 1) (hkv : C kRBV = 0)
    (hk : (C kMVL = 1 ∧ C kMVE = 0 ∧ C xcp = 0) ∨ (C kMVL = 0 ∧ C kMVE = 1 ∧ C xcp = 0) ∨
      (C kMVL = 0 ∧ C kMVE = 0 ∧ C xcp = 1)) : C rd = 1 := by
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
  have z : C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
    omega
  have hrdc := rdcOff ok hC hD z.2.2.2.2.2.2.1
  rcases hk with ⟨a, b', c'⟩ | ⟨a, b', c'⟩ | ⟨a, b', c'⟩ <;>
    simp [hq, hT, hcp, hrdc, hkv, a, b', c', z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1,
      z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2] at f <;> omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

theorem shapeU_head (tl te b1 nk h w : Nat) : (shapeU tl te b1 nk h w).head? = some (0, 1) := by
  unfold shapeU
  by_cases h1 : tl = 1 <;> by_cases h2 : te = 1 <;> by_cases h3 : b1 = 1 <;> simp [h1, h2, h3, List.head?_append]

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **A part's first row is its `TAG` field.** -/
theorem firstTag {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) :
    UField s o 1 ∧ stOf (s.row o) = 0 := by
  have hne := U.nonempty
  obtain ⟨⟨a, l⟩, rest, rfl⟩ : ∃ p rest, fl = p :: rest := by
    cases fl with
    | nil => simp at hne
    | cons p r => exact ⟨p, r, rfl⟩
  have ha : a = 0 := U.consec.1
  subst ha
  have hU := (U.fields 0 (by simp)).1
  simp only [List.getElem_cons_zero, Nat.add_zero] at hU
  have hsh := congrArg List.head? U.shape
  rw [shapeU_head] at hsh
  simp only [List.map_cons, List.head?_cons, Option.some.injEq, Prod.mk.injEq, Nat.add_zero] at hsh
  obtain ⟨h1, rfl⟩ := hsh
  exact ⟨hU, h1⟩

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
  (Pb : Nat → List Nat)
  (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
include hw hs hL hP hR

/-- A copied row of a direct-copy part (`RDB RDE RLP RBR PT`) carries the source's byte at its position. -/
theorem copyRow (k : Nat) (hk : k < ps.length)
    (hkd : kd k = 0 ∨ kd k = 1 ∨ kd k = 2 ∨ kd k = 3 ∨ kd k = 11) (d : Nat) (hd : d < ps[k].2)
    (hoh : OneHot (s.row (ps[k].1 + d))) (hcp : s.row (ps[k].1 + d) cp = 1)
    (hbm : s.row (ps[k].1 + d) sBM = 0) (hch : s.row (ps[k].1 + d) sCH = 0) (hvl : s.row (ps[k].1 + d) sVLEN = 0) :
    s.row (ps[k].1 + d) b = (Pb (s.row ps[k].1 sN)).getD d 0 := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  generalize hkk : kd k = ki at K hkd
  generalize ps[k].1 = o at K U hoh hcp hbm hch hvl ⊢
  generalize ps[k].2 = ℓ at K U hd
  have hlt : o + d < s.rows.length := by have := K.le; omega
  have hok := okRow hw hs hlt
  have hI := K.ix d hd
  have hx : s.row (o + d) xcp = 0 := by
    rw [(K.sel d hd).2.1]
    rcases hkd with rfl | rfl | rfl | rfl | rfl <;> simp [xcpV, kdOf, UKind.all, b2n]
  have k4 : s.row (o + d) kRBV = 0 := by
    have := hI.kd 4 (by omega); rcases hkd with rfl | rfl | rfl | rfl | rfl <;> exact this
  have k6 : s.row (o + d) kMVL = 0 := by
    have := hI.kd 6 (by omega); rcases hkd with rfl | rfl | rfl | rfl | rfl <;> exact this
  have k7 : s.row (o + d) kMVE = 0 := by
    have := hI.kd 7 (by omega); rcases hkd with rfl | rfl | rfl | rfl | rfl <;> exact this
  have k3 : s.row (o + d) kRBR = 0 → True := fun _ => trivial
  have hrd : s.row (o + d) rd = 1 := by
    apply rdCopy hok (rowLt hw hs _) (nextLt hw hs _) (K.qb d hd) hcp hoh (fun _ => ⟨k4, k6, k7, hx⟩)
      (fun _ => ⟨k6, k7⟩) (fun h => by omega) (fun h => by omega)
      (rdcOff hok (rowLt hw hs _) (nextLt hw hs _) hch)
  rw [bCopyN hok (rowLt hw hs _) (nextLt hw hs _) hcp hbm, hR _ hlt hrd,
    dirRow hok (rowLt hw hs _) (nextLt hw hs _) hI hkd hrd, (U.rows d hd).2.1, K.pc d hd sN (by decide)]

/-- **The tag of a direct-copy part's source** is the part's node type. -/
theorem tagCopy (k : Nat) (hk : k < ps.length) (hkd : kd k = 0 ∨ kd k = 1 ∨ kd k = 2 ∨ kd k = 3 ∨ kd k = 11) :
    (Pb (s.row ps[k].1 sN)).getD 0 0 =
      s.row ps[k].1 qtb1 + 2 * s.row ps[k].1 qtb2 + 3 * s.row ps[k].1 qte := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  have hT := firstTag hw hs U
  have F := kField hw hs hL.segc K hT.1 hT.2 (Nat.le_refl _) (by have := K.pos; omega) 0 (by omega)
  simp only [Nat.add_zero] at F
  obtain ⟨hoh, hst, hlt, hI, -, hq⟩ := F
  have hTg := (stOf_inv hoh).1 hst
  have hs1 := hoh.sum
  have hok := okRow hw hs hlt
  have hcp : s.row ps[k].1 cp = 1 := by
    apply natv (rowLt hw hs _ _) one_lt
    have hI' := hI
    generalize kd k = ki at hI' hkd
    have a0 : s.row ps[k].1 kRDB = if 0 = ki then 1 else 0 := hI'.kd 0 (by omega)
    have a1 : s.row ps[k].1 kRDE = if 1 = ki then 1 else 0 := hI'.kd 1 (by omega)
    have a2 : s.row ps[k].1 kRLP = if 2 = ki then 1 else 0 := hI'.kd 2 (by omega)
    have a3 : s.row ps[k].1 kRBR = if 3 = ki then 1 else 0 := hI'.kd 3 (by omega)
    have a5 : s.row ps[k].1 kRBI = if 5 = ki then 1 else 0 := hI'.kd 5 (by omega)
    have a11 : s.row ps[k].1 kPT = if 11 = ki then 1 else 0 := hI'.kd 11 (by omega)
    rw [cpTAG hok (rowLt hw hs _) hs1 hTg, a0, a1, a2, a3, a5, a11]
    rcases hkd with rfl | rfl | rfl | rfl | rfl <;> rfl
  have e := copyRow hw hs hL hP Pb hR k hk hkd 0 K.pos (by simpa using hoh) (by simpa using hcp)
    (by simp; omega) (by simp; omega) (by simp; omega)
  simp only [Nat.add_zero] at e
  rw [← e, (gramRow hok (rowLt hw hs _) (nextLt hw hs _) hs1).1 hTg K.pf]

/-- All four copied prefix-length bytes are bound to the output header. -/
theorem copiedHpl (k : Nat) (hk : k < ps.length) (hkd : kd k=1 ∨ kd k=11) :
    (List.range 4).map (fun i => (Pb (s.row ps[k].1 sN)).getD (1+i) 0) = u32Bytes (s.row ps[k].1 qhk) := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  have hlt0 : ps[k].1<s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hte : s.row ps[k].1 qte=1 := by
    rcases hkd with h | h
    · exact (head_RDE ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by simpa [h] using I0.kd)).2.2.1
    · exact (head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by simpa [h] using I0.kd)).2.2.1
  have hqb : s.row ps[k].1 qb=1 := by simpa using K.qb 0 K.pos
  obtain ⟨hl, -, -, -, ⟨U1,s1⟩, -, -⟩ := extShape hw hs U hte hqb K.pf
  have hle := K.le
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1+d) (by omega); rwa [show ps[k].1+(1+d)=ps[k].1+1+d by omega] at this)
  rw [show ps[k].1+1+3=ps[k].1+4 by omega, K.pc 4 (by omega) qhk (by decide)] at eH
  rw [← eH]
  unfold rowsB
  apply List.map_congr_left
  intro d hd
  have hd4 : d<4 := List.mem_range.mp hd
  have F := kField hw hs hL.segc K U1 s1 (by omega) (by omega) d hd4
  have hpl := (stOf_inv F.1).2.1 F.2.1
  have hok := okRow hw hs F.2.2.1
  have hcp : s.row (ps[k].1+1+d) cp=1 := by
    apply natv (rowLt hw hs _ _) one_lt
    have a1 : s.row (ps[k].1+1+d) kRDE=if 1=kd k then 1 else 0 := F.2.2.2.1.kd 1 (by omega)
    have a2 : s.row (ps[k].1+1+d) kRLP=if 2=kd k then 1 else 0 := F.2.2.2.1.kd 2 (by omega)
    have a11 : s.row (ps[k].1+1+d) kPT=if 11=kd k then 1 else 0 := F.2.2.2.1.kd 11 (by omega)
    rw [cpHPL hok (rowLt hw hs _) F.1.sum hpl, a1,a2,a11]
    rcases hkd with h | h <;> rw [h] <;> rfl
  have hc := copyRow hw hs hL hP Pb hR k hk (by omega) (1+d) (by omega)
  rw [show ps[k].1+(1+d)=ps[k].1+1+d by omega] at hc
  exact (hc F.1 hcp (by have := F.1.sum; omega) (by have := F.1.sum; omega)
    (by have := F.1.sum; omega)).symm

/-- **A pass-through's source** has bytes `1` (hex-prefix length) at 1 and `0` (flag byte) at 5. -/
theorem ptHead (k : Nat) (hk : k < ps.length) (hkd : kd k = 11) :
    (List.range 4).map (fun i => (Pb (s.row ps[k].1 sN)).getD (1+i) 0) = [1,0,0,0] ∧
      (Pb (s.row ps[k].1 sN)).getD 5 0 = 0 := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  have hlt0 : ps[k].1 < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  rw [hkd] at I0
  obtain ⟨-, -, hte, -, -, hqhk, -⟩ := head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  have hq0 : s.row ps[k].1 qb = 1 := by simpa using K.qb 0 K.pos
  obtain ⟨hℓ, -, -, -, ⟨U1, s1⟩, KR, -⟩ := extShape hw hs U hte hq0 K.pf
  simp only [hqhk] at hℓ KR
  have hsc := hL.segc
  have e1 := copiedHpl hw hs hL hP Pb hR k hk (Or.inr hkd)
  rw [hqhk] at e1
  change (List.range 4).map (fun i => (Pb (s.row ps[k].1 sN)).getD (1+i) 0)=[1,0,0,0] at e1
  -- row `o + 5`: `HPF`
  have F5 := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at F5
  obtain ⟨oh5, st5, lt5, I5, -, -⟩ := F5
  have h5 := (stOf_inv oh5).2.2.1 st5
  have ok5 := okRow hw hs lt5
  have hcp5 : s.row (ps[k].1 + 5) cp = 1 := by
    apply natv (rowLt hw hs _ _) one_lt
    have a1 : s.row (ps[k].1 + 5) kRDE = if 1 = kd k then 1 else 0 := I5.kd 1 (by omega)
    have a2 : s.row (ps[k].1 + 5) kRLP = if 2 = kd k then 1 else 0 := I5.kd 2 (by omega)
    have a11 : s.row (ps[k].1 + 5) kPT = if 11 = kd k then 1 else 0 := I5.kd 11 (by omega)
    rw [cpHPF ok5 (rowLt hw hs _) oh5.sum h5, a1, a2, a11, hkd]; rfl
  have e5 := copyRow hw hs hL hP Pb hR k hk (by omega) 5 (by omega) oh5 hcp5 (by have := oh5.sum; omega)
    (by have := oh5.sum; omega) (by have := oh5.sum; omega)
  have b5 : s.row (ps[k].1 + 5) b = 0 := by
    have f := bHPFp ok5 (rowLt hw hs _) oh5.sum h5
    have a11 : s.row (ps[k].1 + 5) kPT = if 11 = kd k then 1 else 0 := I5.kd 11 (by omega)
    rw [a11, hkd, if_pos rfl, cast1] at f
    exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by rw [cast0]; grind)
  exact ⟨e1, by rw [← e5, b5]⟩

/-- **The source's byte 5** read on the `TAG` row of a moved-key part (`MVL`, `MVE`) or an `ESx1` split
branch: its high nibble is `2·qtl + podd`. -/
theorem tagNib5 (k : Nat) (hk : k < ps.length)
    (hkd : kd k = 6 ∨ kd k = 7 ∨ (kd k = 10 ∧ spXN ci = 1)) :
    (Pb (s.row ps[k].1 sN)).getD 5 0 / 16 = 2 * s.row ps[k].1 qtl + s.row ps[k].1 podd ∧
      s.row ps[k].1 podd ≤ 1 ∧ (kd k = 6 → s.row ps[k].1 qtl = 1) ∧ (kd k ≠ 6 → s.row ps[k].1 qtl = 0) := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  have hT := firstTag hw hs U
  have F := kField hw hs hL.segc K hT.1 hT.2 (Nat.le_refl _) (by have := K.pos; omega) 0 (by omega)
  simp only [Nat.add_zero] at F
  obtain ⟨hoh, hst, hlt, hI, -, hq⟩ := F
  have hTg := (stOf_inv hoh).1 hst
  have hok := okRow hw hs hlt
  have hpodd : s.row ps[k].1 podd ≤ 1 := partBoolN hok (rowLt hw hs _) K.pf (x := podd) (by decide)
  have hqtl : s.row ps[k].1 qtl ≤ 1 := partBoolN hok (rowLt hw hs _) K.pf (x := qtl) (by decide)
  -- the kinds and `xcp`
  have hx := (K.sel 0 K.pos).2.1
  simp only [Nat.add_zero] at hx
  have k0 : ∀ m, m < 12 → s.row ps[k].1 (kcol m) = if m = kd k then 1 else 0 := fun m hm => hI.kd m hm
  have a6 : s.row ps[k].1 kMVL = if 6 = kd k then 1 else 0 := hI.kd 6 (by omega)
  have a7 : s.row ps[k].1 kMVE = if 7 = kd k then 1 else 0 := hI.kd 7 (by omega)
  have hK : (s.row ps[k].1 kMVL = 1 ∧ s.row ps[k].1 kMVE = 0 ∧ s.row ps[k].1 xcp = 0) ∨
      (s.row ps[k].1 kMVL = 0 ∧ s.row ps[k].1 kMVE = 1 ∧ s.row ps[k].1 xcp = 0) ∨
      (s.row ps[k].1 kMVL = 0 ∧ s.row ps[k].1 kMVE = 0 ∧ s.row ps[k].1 xcp = 1) := by
    rcases hkd with h | h | ⟨h, hX⟩
    · rw [h] at a6 a7 hx; refine Or.inl ⟨a6, a7, ?_⟩; rw [hx]; simp [xcpV, kdOf, UKind.all, b2n]
    · rw [h] at a6 a7 hx; refine Or.inr (Or.inl ⟨a6, a7, ?_⟩); rw [hx]; simp [xcpV, kdOf, UKind.all, b2n]
    · have hci := (termCase hw hs hL hP k hk (Or.inr h)).2 h
      have := (head_SPB hok (rowLt hw hs _) (nextLt hw hs _) K.pf (by rw [← h]; exact k0) hI.cs hci.1 hci.2).2.2.2.2.1
      rw [h] at a6 a7; exact Or.inr (Or.inr ⟨a6, a7, by rw [this, hX]⟩)
  have hcp : s.row ps[k].1 cp = 0 := cpZero hw hs (by
    have b0 : s.row ps[k].1 kRDB = if 0 = kd k then 1 else 0 := hI.kd 0 (by omega)
    have b1 : s.row ps[k].1 kRDE = if 1 = kd k then 1 else 0 := hI.kd 1 (by omega)
    have b2 : s.row ps[k].1 kRLP = if 2 = kd k then 1 else 0 := hI.kd 2 (by omega)
    have b3 : s.row ps[k].1 kRBR = if 3 = kd k then 1 else 0 := hI.kd 3 (by omega)
    have b5 : s.row ps[k].1 kRBI = if 5 = kd k then 1 else 0 := hI.kd 5 (by omega)
    have b11 : s.row ps[k].1 kPT = if 11 = kd k then 1 else 0 := hI.kd 11 (by omega)
    rw [cpTAG hok (rowLt hw hs _) hoh.sum hTg, b0, b1, b2, b3, b5, b11]
    rcases hkd with h | h | ⟨h, -⟩ <;> rw [h] <;> rfl)
  have k4 : s.row ps[k].1 kRBV = 0 := by
    have a4 : s.row ps[k].1 kRBV = if 4 = kd k then 1 else 0 := hI.kd 4 (by omega)
    rcases hkd with h | h | ⟨h, -⟩ <;> rw [h] at a4 <;> exact a4
  have hrd := rdTag hok (rowLt hw hs _) (nextLt hw hs _) hq hoh hcp hTg k4 hK
  have hsp : s.row ps[k].1 spos = 5 := by
    rcases hkd with h | h | ⟨h, -⟩
    · have f := pMT hok (rowLt hw hs _) hoh.sum hrd hTg
      have x1 : s.row ps[k].1 kMVL = 1 := by rw [a6, h]; rfl
      have x2 : s.row ps[k].1 kMVE = 0 := by rw [a7, h]; rfl
      rw [x1, x2, cast1, cast0] at f
      exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by rw [show (5 : Nat) = 5 from rfl]; grind)
    · have f := pMT hok (rowLt hw hs _) hoh.sum hrd hTg
      have x1 : s.row ps[k].1 kMVL = 0 := by rw [a6, h]; rfl
      have x2 : s.row ps[k].1 kMVE = 1 := by rw [a7, h]; rfl
      rw [x1, x2, cast1, cast0] at f
      exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by rw [show (5 : Nat) = 5 from rfl]; grind)
    · have f := pST hok (rowLt hw hs _) hoh.sum hrd hTg
      have a10 : s.row ps[k].1 kSPB = if 10 = kd k then 1 else 0 := hI.kd 10 (by omega)
      rw [a10, h, if_pos rfl, cast1] at f
      exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by rw [show (5 : Nat) = 5 from rfl]; grind)
  have hk' : ((s.row ps[k].1 kMVL : Nat) : Fp) + ((s.row ps[k].1 kMVE : Nat) : Fp) + ((s.row ps[k].1 xcp : Nat) : Fp) = 1 := by
    have e : s.row ps[k].1 kMVL + s.row ps[k].1 kMVE + s.row ps[k].1 xcp = 1 := by
      rcases hK with ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ <;> rw [x1, x2, x3]
    rw [← natCast_add, ← natCast_add, e]; rfl
  obtain ⟨n1, n2⟩ := tagNib hok (rowLt hw hs _) (nextLt hw hs _) hoh hTg hk' hqtl hpodd
  have hrb := hR _ hlt hrd
  rw [hsp] at hrb
  have bt := nibBits hok (rowLt hw hs _) (nextLt hw hs _) (by have := hoh.sum; have := hoh.bs; omega)
  have := bt 4 (by omega); have := bt 5 (by omega); have := bt 6 (by omega); have := bt 7 (by omega)
  -- the node type
  have hty : (kd k = 6 → s.row ps[k].1 qtl = 1) ∧ (kd k ≠ 6 → s.row ps[k].1 qtl = 0) := by
    have hpf := K.pf
    rcases hkd with h | h | ⟨h, -⟩
    · have := (head_MVL hok (rowLt hw hs _) (nextLt hw hs _) hpf (by rw [← h]; exact k0)).2.2.1
      exact ⟨fun _ => this, fun h' => absurd h h'⟩
    · have hte := (head_MVE hok (rowLt hw hs _) (nextLt hw hs _) hpf (by rw [← h]; exact k0)).2.2.1
      obtain ⟨-, -, -, -, hsum, -⟩ := partHead hok (rowLt hw hs _) hpf hq
      exact ⟨fun h' => by omega, fun _ => by omega⟩
    · have hci := (termCase hw hs hL hP k hk (Or.inr h)).2 h
      have := (head_SPB hok (rowLt hw hs _) (nextLt hw hs _) hpf (by rw [← h]; exact k0) hI.cs hci.1 hci.2).1
      exact ⟨fun h' => by omega, fun _ => this⟩
  refine ⟨?_, hpodd, hty⟩
  rw [← hrb, n2, ← n1]
  omega

end

end ZkFormal.NearV3.UpsRows

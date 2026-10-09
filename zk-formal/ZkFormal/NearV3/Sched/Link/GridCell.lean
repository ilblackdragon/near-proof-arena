import ZkFormal.NearV3.Sched.Link.GridDlx

/-!
# ZkFormal.NearV3.Sched.Link.GridCell — the grid recurrences (stage F, b5)

In the section of instance τ (`SecOk`, `n = P.n`), with the final budgets `sb`, `rb` of the shard rows
(`L2`) and the sorted orders `sord = sordOf n allowed sb`, `rord = rordOf n allowed rb` (b3):

* `cell_link`: a cell receives the public link record of `l = s·n + r` and `al = allowed[l]`;
* `cell_gb`: on an allowed cell `gb = min(L1 / N1, L2 / N2)` (`cell_div` + comparator), with
  `N1, N2 ≥ 1` and `gb ≤ L1, L2`; otherwise `gb = 0`;
* **`grid_cells`**: cell `(i, j)` has `s = sord[i]`, `r = rord[j]`, sender endpoint
  `(N1, L1) = SE i j`, receiver endpoint `(N2, L2) = RE i j` (`Spec/Dist.lean`), and
  `gb = allowed ? min(SE.left / SE.links, RE.left / RE.links) : 0`, i.e. the grid grant
  `gridGrants_get`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd : Nat}

theorem ScanDist.cmp_mem (OS : ScanOwn AP tsd tp) : ScanDist.interactions[6]! ∈ AP.tables[tsd]!.interactions := by
  rw [OS.tab]; exact Scan.sd_mem 6 (by decide)

set_option maxRecDepth 8000 in
/-- Cells: `cx = q1`, `cy = q2`, `cg = al`. -/
theorem Dist.cell_cmp_cells (hD : Dist.DLocal tr tsd pub) {w : Nat} (hw : w < tr.height tsd)
    (hc : cv tr tsd w Dist.kC = 1) :
    cv tr tsd w Dist.cx = cv tr tsd w Dist.q1 ∧ cv tr tsd w Dist.cy = cv tr tsd w Dist.q2 ∧
      cv tr tsd w Dist.cg = cv tr tsd w Dist.al := by
  have K := Dist.kinds hD hw
  have hS : cv tr tsd w Dist.kSh = 0 := by omega
  have lt := fun x => cv_lt (tr := tr) (t := tsd) w x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (c Dist.kC) (sub (c Dist.cx) (c Dist.q1)))
    (by simp [Dist.constraints, Dist.cGrid])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (c Dist.kC) (sub (c Dist.cy) (c Dist.q2)))
    (by simp [Dist.constraints, Dist.cGrid])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := sub (c Dist.cg) (.add (c Dist.kSh) (.mul (c Dist.kC) (c Dist.al))))
    (by simp [Dist.constraints, Dist.cGrid])
  simp only [zev_mul, zev_sub, zev_add, zev_c, cur_cv, hc, hS] at c1 c2 c4
  push_cast at c1 c2 c4
  have := lt Dist.cx; have := lt Dist.q1; have := lt Dist.cy; have := lt Dist.q2; have := lt Dist.cg
  have := lt Dist.al
  exact ⟨by omega, by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- **A cell's grant.** -/
theorem cell_gb {tcmp : Nat} (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (CO : CmpOwn AP tcmp)
    {w : Nat} (hw : w < tr.height tsd) (hc : cv tr tsd w Dist.kC = 1) :
    (cv tr tsd w Dist.al = 0 → cv tr tsd w Dist.gb = 0) ∧
      (cv tr tsd w Dist.al = 1 → 1 ≤ cv tr tsd w Dist.N1 ∧ 1 ≤ cv tr tsd w Dist.N2 ∧
        cv tr tsd w Dist.gb = min (cv tr tsd w Dist.L1 / cv tr tsd w Dist.N1)
          (cv tr tsd w Dist.L2 / cv tr tsd w Dist.N2) ∧
        cv tr tsd w Dist.gb ≤ cv tr tsd w Dist.L1 ∧ cv tr tsd w Dist.gb ≤ cv tr tsd w Dist.L2) := by
  have hD := Dist.DLocal.of_sd (sd_local hH OS)
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · have h := hD.zc hw (e := .mul (c Dist.kC) (.mul (Dist.notE (c Dist.al)) (c Dist.gb)))
      (by simp [Dist.constraints, Dist.cGrid])
    simp only [Dist.notE, zev_mul, zev_sub, zev_k, zev_c, cur_cv, hc, h0] at h
    have := cv_lt (tr := tr) (t := tsd) w Dist.gb
    have := h (by omega) (by omega)
    omega
  · obtain ⟨E1, R1, Q1, E2, R2, Q2, G⟩ := Dist.cell_div hD hw h1
    obtain ⟨hq1, hq2, -, -⟩ := Dist.ranges hD hw
    obtain ⟨ex, ey, eg⟩ := Dist.cell_cmp_cells hD hw hc
    have hcmp := cmp_sound_le hH CO OS.lt hw (ScanDist.cmp_mem OS)
      (by rw [ScanDist.cmp_def]) (by rw [ScanDist.cmp_def])
      (by rw [Mem.multNat_c (by rw [ScanDist.cmp_def]), eg, h1]; simp)
      (x := tr.cell tsd w Dist.cx) (y := tr.cell tsd w Dist.cy) (b := tr.cell tsd w Dist.cb)
      (by rw [ScanDist.cmp_def]; rfl) (by show cv tr tsd w Dist.cx < _; omega)
      (by show cv tr tsd w Dist.cy ≤ _; omega)
    have hN1 : 1 ≤ cv tr tsd w Dist.N1 := by omega
    have hN2 : 1 ≤ cv tr tsd w Dist.N2 := by omega
    have hle1 : cv tr tsd w Dist.q1 ≤ cv tr tsd w Dist.L1 := by
      rw [E1]; have := Nat.le_mul_of_pos_right (cv tr tsd w Dist.q1) hN1; omega
    have hle2 : cv tr tsd w Dist.q2 ≤ cv tr tsd w Dist.L2 := by
      rw [E2]; have := Nat.le_mul_of_pos_right (cv tr tsd w Dist.q2) hN2; omega
    rw [← Q1, ← Q2]
    rcases hcmp with ⟨hb, hle⟩ | ⟨hb, hlt⟩
    · have hcb : cv tr tsd w Dist.cb = 1 := by unfold cv; rw [hb]; rfl
      rw [if_pos hcb] at G
      have hle' : cv tr tsd w Dist.q2 ≤ cv tr tsd w Dist.q1 := by
        have : cv tr tsd w Dist.cy ≤ cv tr tsd w Dist.cx := hle
        omega
      refine ⟨hN1, hN2, by rw [G, Nat.min_eq_right hle'], by omega, by omega⟩
    · have hcb : cv tr tsd w Dist.cb = 0 := by unfold cv; rw [hb]; rfl
      rw [if_neg (by omega)] at G
      have hlt' : cv tr tsd w Dist.q1 < cv tr tsd w Dist.q2 := by
        have : cv tr tsd w Dist.cx < cv tr tsd w Dist.cy := hlt
        omega
      refine ⟨hN1, hN2, by rw [G, Nat.min_eq_left (by omega)], by omega, by omega⟩

end

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd : Nat}
variable {Ps : List InstPub} {I : PubIdx AP pub Fp.ofNat} {fwd : List (Nat × Nat)}

namespace GridPub
variable (G : GridPub AP pub tr tsd tp Ps I fwd)
include G

set_option maxRecDepth 8000 in
/-- **The link of a cell** (public link record): `l = s·n + r`, `al = allowed[l]`. -/
theorem cell_link {τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) {w : Nat} (hw : w < tr.height tsd)
    (hc : cv tr tsd w Dist.kC = 1) (hτ : cv tr tsd w Dist.tau = τ) (hnn : cv tr tsd w Dist.nn = P.n)
    (hs : cv tr tsd w Dist.s < P.n) (hr : cv tr tsd w Dist.r < P.n) :
    cv tr tsd w Dist.s * P.n + cv tr tsd w Dist.r < P.n * P.n ∧
      cv tr tsd w Dist.llo + 256 * cv tr tsd w Dist.lhi = cv tr tsd w Dist.s * P.n + cv tr tsd w Dist.r ∧
      cv tr tsd w Dist.al = P.al (cv tr tsd w Dist.s * P.n + cv tr tsd w Dist.r) ∧
      Scan.parV tr tsd w = linkRec τ P (cv tr tsd w Dist.s * P.n + cv tr tsd w Dist.r) := by
  have hD := G.hD
  obtain ⟨hτl, l, hl, hpv⟩ := cell_rec G.hH G.OS I Ps fwd G.hrec G.h256 hw hc
  rw [hτ, hP] at hl hpv
  have hn64 := (G.hP τ (hτ ▸ hτl)).n64
  rw [hP] at hn64
  have hnn64 : P.n * P.n ≤ 4096 := Nat.mul_le_mul hn64 hn64
  have hpv' := hpv
  simp only [Scan.parV, linkRec, srcFields, b2, List.cons_append, List.nil_append, List.cons.injEq] at hpv'
  obtain ⟨-, -, -, -, -, -, -, -, p6, p7, p8, -⟩ := hpv'
  have hl0 : cv tr tsd w Dist.llo = l % 256 := p6
  have hl1 : cv tr tsd w Dist.lhi = l / 256 % 256 := p7
  have hal : cv tr tsd w Dist.alc = P.al l := p8
  have halc := Dist.cell_alc hD hw hc
  -- the link constraint
  obtain ⟨q, c1⟩ := Mem.zdvd hD hw (e := .mul (c Dist.kC) (sub Dist.linkE
    (.add (.mul (c Dist.s) (c Dist.nn)) (c Dist.r)))) (by simp [Dist.constraints, Dist.cGrid])
  simp only [Dist.linkE, zev_mul, zev_sub, zev_add, zev_smul, zev_c, cur_cv, hc, hnn] at c1
  push_cast at c1
  have hsn : cv tr tsd w Dist.s * P.n + cv tr tsd w Dist.r < P.n * P.n := link_lt hs hr
  have hli : cv tr tsd w Dist.llo + 256 * cv tr tsd w Dist.lhi = l := by rw [hl0, hl1]; omega
  have e : l = cv tr tsd w Dist.s * P.n + cv tr tsd w Dist.r := by
    have h1 : ((cv tr tsd w Dist.s * P.n : Nat) : Int) = (cv tr tsd w Dist.s : Int) * (P.n : Int) := by
      push_cast; rfl
    omega
  subst e
  exact ⟨hsn, hli, halc.symm.trans hal, hpv⟩

/-- **b5: the grid recurrences.** Given the side orders (`sideList`, b3) and the final budgets of
the shard rows, cell `(i, j)` holds `s = sord[i]`, `r = rord[j]`, `(N1, L1) = SE i j`,
`(N2, L2) = RE i j` and the grant `allowed ? min(SE.left / SE.links, RE.left / RE.links) : 0`. -/
theorem grid_cells (DX : SdlxOwn AP tsd) {tcmp : Nat} (CO : CmpOwn AP tcmp)
    {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) (S : SecOk tr tsd w0 τ P)
    (sb rb : Array Nat) (sord rord : List Nat)
    (hso : Dist.sideList tr tsd w0 P.n 0 = sord) (hro : Dist.sideList tr tsd w0 P.n 1 = rord)
    (hsb : ∀ x, x < P.n → cv tr tsd (w0 + 0 * P.n + x) Dist.L2 = sb[Dist.shardAt tr tsd w0 P.n 0 x]!)
    (hrb : ∀ x, x < P.n → cv tr tsd (w0 + 1 * P.n + x) Dist.L2 = rb[Dist.shardAt tr tsd w0 P.n 1 x]!) :
    ∀ i j, i < P.n → j < P.n →
      cv tr tsd (Dist.cellAt w0 P.n i j) Dist.s = sord[i]! ∧
      cv tr tsd (Dist.cellAt w0 P.n i j) Dist.r = rord[j]! ∧
      (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N1, cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L1) =
        SE P.n P.allowed sb rb sord rord i j ∧
      (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N2, cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2) =
        RE P.n P.allowed sb rb sord rord i j ∧
      cv tr tsd (Dist.cellAt w0 P.n i j) Dist.gb =
        (if P.allowed[sord[i]! * P.n + rord[j]!]! then
          min ((SE P.n P.allowed sb rb sord rord i j).2 / (SE P.n P.allowed sb rb sord rord i j).1)
            ((RE P.n P.allowed sb rb sord rord i j).2 / (RE P.n P.allowed sb rb sord rord i j).1)
        else 0) := by
  have hD := G.hD
  have hn1 := S.n1
  have hn64 := S.n64
  obtain ⟨SR, HR, CR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
  obtain ⟨DH, D0, DS⟩ := G.grid_dl DX hP S
  have CA : ∀ i j, i < P.n → j < P.n → Dist.cellAt w0 P.n i j < tr.height tsd ∧
      cv tr tsd (Dist.cellAt w0 P.n i j) Dist.kC = 1 ∧ cv tr tsd (Dist.cellAt w0 P.n i j) Dist.a = i ∧
      cv tr tsd (Dist.cellAt w0 P.n i j) Dist.b = j ∧
      cv tr tsd (Dist.cellAt w0 P.n i j) Dist.tau = τ ∧ cv tr tsd (Dist.cellAt w0 P.n i j) Dist.nn = P.n :=
    fun i j hi hj => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := CR i j hi hj
      exact ⟨h1, h2, h3, h4, h5.1.trans S.tau, h5.2.trans S.nn⟩
  have HA : ∀ i, i < P.n → Dist.hdrAt w0 P.n i < tr.height tsd ∧
      cv tr tsd (Dist.hdrAt w0 P.n i) Dist.kGH = 1 := fun i hi => ⟨(HR i hi).1, (HR i hi).2.1⟩
  have e0 : ∀ i, Dist.cellAt w0 P.n i 0 = Dist.hdrAt w0 P.n i + 1 := fun i => by
    unfold Dist.cellAt Dist.hdrAt; omega
  have eS : ∀ i j, Dist.cellAt w0 P.n i (j + 1) = Dist.cellAt w0 P.n i j + 1 := fun i j => by
    unfold Dist.cellAt; omega
  have hsg : ∀ i, i < P.n → sord[i]! = Dist.shardAt tr tsd w0 P.n 0 i := fun i hi => by
    rw [← hso]; exact Dist.sideList_get hi
  have hrg : ∀ j, j < P.n → rord[j]! = Dist.shardAt tr tsd w0 P.n 1 j := fun j hj => by
    rw [← hro]; exact Dist.sideList_get hj
  have SH0 := fun i (hi : i < P.n) =>
    sec_shard G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hP S (sd := 0) (by decide) hi
  have SH1 := fun j (hj : j < P.n) =>
    sec_shard G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hP S (sd := 1) (by decide) hj
  -- (a) `s` along a row
  have SS : ∀ i j, i < P.n → j < P.n → cv tr tsd (Dist.cellAt w0 P.n i j) Dist.s = sord[i]! := by
    intro i j hi
    induction j with
    | zero =>
      intro _
      obtain ⟨hw, hg⟩ := HA i hi
      obtain ⟨-, -, -, -, -, es, -⟩ := Dist.hdr_next hD hw hg
      rw [e0, es, (DH i hi).1, hsg i hi]
    | succ j ih =>
      intro hj
      obtain ⟨hw, hc, -, hb, -, hnn⟩ := CA i j hi (by omega)
      have he := Dist.e1_cell hD hw hc (by omega) (by omega) (by omega)
      rw [hb, hnn, if_neg (by omega)] at he
      obtain ⟨-, -, -, -, es, -⟩ := Dist.cell_mid hD hw hc he (by omega)
      rw [eS, es, ih (by omega)]
  -- (b) `r` down a column
  have RR : ∀ j i, j < P.n → i < P.n → cv tr tsd (Dist.cellAt w0 P.n i j) Dist.r = rord[j]! := by
    intro j i hj
    induction i with
    | zero => intro _; rw [(D0 j hj).1, hrg j hj]
    | succ i ih => intro hi; rw [(DS i j hi hj).1, ih (by omega)]
  -- (c) the link of a cell
  have AL : ∀ i j, i < P.n → j < P.n → cv tr tsd (Dist.cellAt w0 P.n i j) Dist.al =
      if P.allowed[sord[i]! * P.n + rord[j]!]! then 1 else 0 := by
    intro i j hi hj
    obtain ⟨hw, hc, -, -, hτ, hnn⟩ := CA i j hi hj
    have hs := SS i j hi hj
    have hr := RR j i hj hi
    obtain ⟨-, -, hal, -⟩ := G.cell_link hP hw hc hτ hnn
      (by rw [hs, hsg i hi]; exact (SH0 i hi).2.2.2.2.2.2.1)
      (by rw [hr, hrg j hj]; exact (SH1 j hj).2.2.2.2.2.2.1)
    rw [hal, hs, hr]; rfl
  have GB := fun i j (hi : i < P.n) (hj : j < P.n) => cell_gb G.hH G.OS CO (CA i j hi hj).1 (CA i j hi hj).2.1
  have lt := fun w x => cv_lt (tr := tr) (t := tsd) w x
  -- (d) the sender endpoints along a row, given the receiver endpoints
  have rowSE : ∀ i, i < P.n → (∀ j, j < P.n →
      (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N2, cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2) =
        RE P.n P.allowed sb rb sord rord i j) → ∀ j, j < P.n →
      (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N1, cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L1) =
        SE P.n P.allowed sb rb sord rord i j := by
    intro i hi hRE j
    induction j with
    | zero =>
      intro _
      obtain ⟨hw, hg⟩ := HA i hi
      obtain ⟨-, -, -, -, -, -, eN, eL, -⟩ := Dist.hdr_next hD hw hg
      rw [e0, eN, eL, (DH i hi).2.1, (DH i hi).2.2, (SH0 i hi).2.2.2.2.2.2.2.1, hsb i hi]
      show (cntSd P.n P.allowed 0 (Dist.shardAt tr tsd w0 P.n 0 i), _) = _
      rw [← hsg i hi]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨hw, hc, -, hb, -, hnn⟩ := CA i j hi (by omega)
      have he := Dist.e1_cell hD hw hc (by omega) (by omega) (by omega)
      rw [hb, hnn, if_neg (by omega)] at he
      obtain ⟨-, -, -, -, -, mN, mL, -⟩ := Dist.cell_mid hD hw hc he (by omega)
      have hSE := ih (by omega)
      have hRE' := hRE j (by omega)
      have hal := AL i j hi (by omega)
      obtain ⟨G0, G1⟩ := GB i j hi (by omega)
      rw [SE_succ, ← hSE, ← hRE', eS]
      have := lt (Dist.cellAt w0 P.n i j + 1) Dist.N1; have := lt (Dist.cellAt w0 P.n i j + 1) Dist.L1
      have := lt (Dist.cellAt w0 P.n i j) Dist.N1; have := lt (Dist.cellAt w0 P.n i j) Dist.L1
      by_cases ha : P.allowed[sord[i]! * P.n + rord[j]!]! = true
      · rw [if_pos ha] at hal ⊢
        obtain ⟨hN1, -, hg, hg1, -⟩ := G1 hal
        have hg' : Nat.min (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L1 / cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N1) (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2 / cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N2) = cv tr tsd (Dist.cellAt w0 P.n i j) Dist.gb := hg.symm
        rw [hal] at mN
        dsimp only
        rw [hg']
        simp only [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      · rw [if_neg ha] at hal ⊢
        have hg := G0 hal
        rw [hal] at mN
        rw [hg] at mL
        simp only [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
  -- (e) the receiver endpoints down a column
  have colRE : ∀ i, i < P.n → ∀ j, j < P.n →
      (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N2, cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2) =
        RE P.n P.allowed sb rb sord rord i j := by
    intro i
    induction i with
    | zero =>
      intro _ j hj
      rw [(D0 j hj).2.1, (D0 j hj).2.2, (SH1 j hj).2.2.2.2.2.2.2.1, hrb j hj]
      show (cntSd P.n P.allowed 1 (Dist.shardAt tr tsd w0 P.n 1 j), _) = _
      rw [← hrg j hj]
      rfl
    | succ i ih =>
      intro hi j hj
      have hRE := ih (by omega)
      have hSE := rowSE i (by omega) hRE j hj
      have hRE' := hRE j hj
      obtain ⟨hw, hc, -⟩ := CA i j (by omega) hj
      obtain ⟨-, -, -, -, mL⟩ := Dist.cell_dl hD hw hc
      have hal := AL i j (by omega) hj
      obtain ⟨G0, G1⟩ := GB i j (by omega) hj
      rw [RE_succ, ← hSE, ← hRE', (DS i j hi hj).2.1, (DS i j hi hj).2.2]
      have := lt (Dist.cellAt w0 P.n i j) Dist.sL; have := lt (Dist.cellAt w0 P.n i j) Dist.L2
      by_cases ha : P.allowed[sord[i]! * P.n + rord[j]!]! = true
      · rw [if_pos ha] at hal ⊢
        obtain ⟨-, -, hg, -, hg2⟩ := G1 hal
        have key : cv tr tsd (Dist.cellAt w0 P.n i j) Dist.sL = cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2 - cv tr tsd (Dist.cellAt w0 P.n i j) Dist.gb := by omega
        have hg' : Nat.min (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L1 / cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N1) (cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2 / cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N2) = cv tr tsd (Dist.cellAt w0 P.n i j) Dist.gb := hg.symm
        dsimp only
        rw [hg', hal, key]
      · rw [if_neg ha] at hal ⊢
        have hg := G0 hal
        rw [hg] at mL
        have key : cv tr tsd (Dist.cellAt w0 P.n i j) Dist.sL = cv tr tsd (Dist.cellAt w0 P.n i j) Dist.L2 := by omega
        rw [hal, key, Nat.sub_zero]
  intro i j hi hj
  have hRE := colRE i hi j hj
  have hSE := rowSE i hi (colRE i hi) j hj
  refine ⟨SS i j hi hj, RR j i hj hi, hSE, hRE, ?_⟩
  have hal := AL i j hi hj
  obtain ⟨G0, G1⟩ := GB i j hi hj
  rw [← hSE, ← hRE]
  by_cases ha : P.allowed[sord[i]! * P.n + rord[j]!]! = true
  · rw [if_pos ha] at hal ⊢
    dsimp only
    exact (G1 hal).2.2.1
  · rw [if_neg ha] at hal ⊢
    exact G0 hal

end GridPub

end

end ZkFormal.NearV3.Sched

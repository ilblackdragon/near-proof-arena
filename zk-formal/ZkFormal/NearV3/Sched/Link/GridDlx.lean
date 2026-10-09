import ZkFormal.NearV3.Sched.Link.GridShard

/-!
# ZkFormal.NearV3.Sched.Link.GridDlx — the grid delay line `SDLX` (stage F, b4)

Inside the section of instance τ (`SecOk`, start `w₀`, `n = P.n`) every header and cell receives
one `SDLX` message `(τ, a, b, r, N2, L2)` (`dlrg = kGH + kC`). The senders (`dlsg = kSh + kC·(1 − e2)`)
are the shard rows (`(τ, a, 255, r, N2, L2)` for senders, `(τ, 0, a, r, N2, L2)` for receivers) and
the cells above the last grid row (`(τ, a + 1, b, r, N2 − al, L2 − gb)`).

* **`SdlxOwn`** (ownership, decidable on the final AIR): only `ssdV3` sends on `SDLX`; no public
  segment sends on it.
* `in_sec`: a distribute row of instance τ lies in τ's section (`cover` + `start_unique`).
* **`grid_dl`**: header `i` holds the endpoint of sender shard row `i`; cell `(0, j)` that of
  receiver shard row `j`; cell `(i + 1, j)` holds `(r, N2 − al, sL)` of cell `(i, j)`.

The message keys `(τ, a, b)` are unique: a sender is located by `in_sec` and `decode`, and the
`(da, db)` of each row kind pins its position.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- **Ownership of the grid delay line** (decidable on the final AIR): only `ssdV3` (`tsd`) sends on
`SDLX`, and no public segment sends on it. -/
structure SdlxOwn (AP : AirP) (tsd : Nat) : Prop where
  only : ∀ t, t < AP.tables.length → t ≠ tsd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SDLX → i.send = false
  pub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SDLX → seg.send = false

theorem ScanDist.dls_def : ScanDist.interactions[7]! =
    { bus := B_SDLX, mult := [c Dist.dlsg], send := true,
      msg := [c Dist.tau, c Dist.da, c Dist.db, c Dist.r, sub (c Dist.N2) (c Dist.al), c Dist.sL] } := rfl

theorem ScanDist.dlr_def : ScanDist.interactions[8]! =
    { bus := B_SDLX, mult := [c Dist.dlrg], send := false,
      msg := [c Dist.tau, c Dist.a, c Dist.b, c Dist.r, c Dist.N2, c Dist.L2] } := rfl

theorem ScanDist.dlx_send_i : ∀ i ∈ ScanDist.interactions, i.bus = B_SDLX → i.send = true →
    i = ScanDist.interactions[7]! := by
  decide

namespace Dist

/-- Header `i` / cell `(i, j)` of the section at `w₀`. -/
def hdrAt (w0 nv i : Nat) : Nat := w0 + 2 * nv + i * (nv + 1)
def cellAt (w0 nv i j : Nat) : Nat := w0 + 2 * nv + i * (nv + 1) + 1 + j

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

set_option maxRecDepth 8000 in
/-- The `SDLX` cells of a shard row. -/
theorem shard_dl (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1) :
    cv tr t w dlsg = 1 ∧ cv tr t w al = 0 ∧ cv tr t w sL = cv tr t w L2 ∧
      (cv tr t w side = 0 → cv tr t w da = cv tr t w a ∧ cv tr t w db = 255) ∧
      (cv tr t w side = 1 → cv tr t w da = 0 ∧ cv tr t w db = cv tr t w a) := by
  have K := kinds hD hw
  have hC : cv tr t w kC = 0 := by omega
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (c da) (.mul (notE (c side)) (c a))))
    (by simp [constraints, cShard])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (c db)
    (.add (.mul (c side) (c a)) (smul 255 (notE (c side)))))) (by simp [constraints, cShard])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (sub (c sL) (c L2))) (by simp [constraints, cShard])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := .mul (c kSh) (c al)) (by simp [constraints, cShard])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := sub (c dlsg) (.add (c kSh) (.mul (c kC) (notE (c e2)))))
    (by simp [constraints, cGrid])
  dz c3 [hs]; dz c4 [hs]; dz c5 [hs, hC]
  push_cast at c3 c4 c5
  have := lt sL; have := lt L2; have := lt al; have := lt dlsg; have := lt da; have := lt db; have := lt a
  refine ⟨by omega, by omega, by omega, fun h0 => ?_, fun h1 => ?_⟩
  · dz c1 [hs, h0]; dz c2 [hs, h0]; push_cast at c1 c2
    exact ⟨by omega, by omega⟩
  · dz c1 [hs, h1]; dz c2 [hs, h1]; push_cast at c1 c2
    exact ⟨by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- The `SDLX` cells of a cell. -/
theorem cell_dl (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hc : cv tr t w kC = 1) :
    cv tr t w dlsg + cv tr t w e2 = 1 ∧ cv tr t w dlrg = 1 ∧
      cv tr t w da = (cv tr t w a + 1) % 2013265921 ∧ cv tr t w db = cv tr t w b ∧
      ((cv tr t w sL : Int) - ((cv tr t w L2 : Int) - cv tr t w gb)) % 2013265921 = 0 := by
  have K := kinds hD hw
  have hS : cv tr t w kSh = 0 := by omega
  have hG : cv tr t w kGH = 0 := by omega
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  have he2 := bool_of hD hw (x := e2) (by decide)
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (c kC) (sub (c da) (.add (c a) (k 1))))
    (by simp [constraints, cGrid])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (c kC) (sub (c db) (c b))) (by simp [constraints, cGrid])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := .mul (c kC) (sub (c sL) (sub (c L2) (c gb))))
    (by simp [constraints, cGrid])
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := sub (c dlsg) (.add (c kSh) (.mul (c kC) (notE (c e2)))))
    (by simp [constraints, cGrid])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := sub (c dlrg) (.add (c kGH) (c kC))) (by simp [constraints, cGrid])
  dz c1 [hc]; dz c2 [hc]; dz c3 [hc]; dz c5 [hS, hc]; dz c6 [hG, hc]
  push_cast at c1 c2 c3 c5 c6
  have := lt dlsg; have := lt dlrg; have := lt da; have := lt db; have := lt a; have := lt b
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The `SDLX` gates of a header. -/
theorem hdr_dl (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hg : cv tr t w kGH = 1) :
    cv tr t w dlsg = 0 ∧ cv tr t w dlrg = 1 := by
  have K := kinds hD hw
  have hS : cv tr t w kSh = 0 := by omega
  have hC : cv tr t w kC = 0 := by omega
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := sub (c dlsg) (.add (c kSh) (.mul (c kC) (notE (c e2)))))
    (by simp [constraints, cGrid])
  obtain ⟨q6, c6⟩ := Mem.zdvd hD hw (e := sub (c dlrg) (.add (c kGH) (c kC))) (by simp [constraints, cGrid])
  dz c5 [hS, hC]; dz c6 [hg, hC]
  push_cast at c5 c6
  have := lt dlsg; have := lt dlrg
  exact ⟨by omega, by omega⟩

/-- A row with `dlsg = 1` is a shard row or a cell. -/
theorem dlsg_kind (hD : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (h : cv tr t w dlsg = 1) :
    cv tr t w kSh = 1 ∨ cv tr t w kC = 1 := by
  have K := kinds hD hw
  have lt := fun x => cv_lt (tr := tr) (t := t) w x
  obtain ⟨q5, c5⟩ := Mem.zdvd hD hw (e := sub (c dlsg) (.add (c kSh) (.mul (c kC) (notE (c e2)))))
    (by simp [constraints, cGrid])
  dz c5 [h]
  by_cases hC : cv tr t w kC = 0
  · rw [hC] at c5; push_cast at c5; left; have := lt kSh; omega
  · right; omega

/-- **The row of a section at an offset has the section's constants.** -/
theorem ic_of (hD : DLocal tr t pub) {w0 nv x : Nat} (S : Start tr t w0) (hn : cv tr t w0 nn = nv)
    (h1 : 1 ≤ nv) (h64 : nv ≤ 64) (hlo : w0 ≤ x) (hhi : x < w0 + blen nv) : IC tr t x w0 := by
  obtain ⟨SR, HR, CR, -⟩ := block hD S hn h1 h64
  rcases decode h1 hlo hhi with ⟨sd, y, hsd, hy, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact (SR sd y hsd hy).2.2.2.2.1
  · exact (HR i hi).2.2.2
  · exact (CR i j hi hj).2.2.2.2

end

end Dist

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd : Nat}

/-- The hypotheses on the public records used by the grid. -/
structure GridPub (AP : AirP) (pub : List Fp) (tr : Trace Fp) (tsd tp : Nat) (Ps : List InstPub)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat)) : Prop where
  hH : HoldsP AP pub tr
  OS : ScanOwn AP tsd tp
  hrec : I.recs B_SPAR true = (render Ps fwd).par
  h256 : Ps.length ≤ 256
  hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD)

namespace GridPub
variable {Ps : List InstPub} {I : PubIdx AP pub Fp.ofNat} {fwd : List (Nat × Nat)}
  (G : GridPub AP pub tr tsd tp Ps I fwd)
include G

theorem hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64 := fun τ h => (G.hP τ h).n64

theorem hD : Dist.DLocal tr tsd pub := Dist.DLocal.of_sd (sd_local G.hH G.OS)

/-- Every shard row has `1 ≤ nn ≤ 64`. -/
theorem hN : ∀ w, w < tr.height tsd → cv tr tsd w Dist.kSh = 1 →
    1 ≤ cv tr tsd w Dist.nn ∧ cv tr tsd w Dist.nn ≤ 64 := by
  intro w hw hs
  obtain ⟨hτ, -, -, hnn, -⟩ := shard_vals G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hw hs
  have PO := G.hP _ hτ
  rw [hnn]
  exact ⟨PO.n1, PO.n64⟩

/-- **A distribute row of instance τ lies in τ's section.** -/
theorem in_sec {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) (S : SecOk tr tsd w0 τ P)
    {x : Nat} (hx : x < tr.height tsd)
    (hd : cv tr tsd x Dist.kSh = 1 ∨ cv tr tsd x Dist.kGH = 1 ∨ cv tr tsd x Dist.kC = 1)
    (hτ : cv tr tsd x Dist.tau = τ) : w0 ≤ x ∧ x < w0 + Dist.blen P.n := by
  have hD := G.hD
  obtain ⟨w1, st1, hlo, hhi⟩ := Dist.cover (sd_local G.hH G.OS) G.hN x hx hd
  have hN1 := G.hN w1 st1.1 st1.2.1
  have ic := Dist.ic_of hD st1 rfl hN1.1 hN1.2 hlo hhi
  have h1 : w1 = w0 := start_unique G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hP S st1 (ic.1.symm.trans hτ)
  subst h1
  rw [S.nn] at hhi
  exact ⟨hlo, hhi⟩

/-- **The sender of an `SDLX` message received in τ's section.** -/
theorem dl_sender (DX : SdlxOwn AP tsd) {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P)
    (S : SecOk tr tsd w0 τ P) {w : Nat} (hw : w < tr.height tsd) (hrg : cv tr tsd w Dist.dlrg = 1)
    (hτ : cv tr tsd w Dist.tau = τ) :
    ∃ x, x < tr.height tsd ∧ cv tr tsd x Dist.r = cv tr tsd w Dist.r ∧
      cv tr tsd x Dist.sL = cv tr tsd w Dist.L2 ∧
      ((∃ y, y < P.n ∧ x = w0 + 0 * P.n + y ∧ cv tr tsd w Dist.a = y ∧ cv tr tsd w Dist.b = 255 ∧
          cv tr tsd w Dist.N2 = cv tr tsd x Dist.N2) ∨
        (∃ y, y < P.n ∧ x = w0 + 1 * P.n + y ∧ cv tr tsd w Dist.a = 0 ∧ cv tr tsd w Dist.b = y ∧
          cv tr tsd w Dist.N2 = cv tr tsd x Dist.N2) ∨
        (∃ i j, i + 1 < P.n ∧ j < P.n ∧ x = Dist.cellAt w0 P.n i j ∧ cv tr tsd w Dist.a = i + 1 ∧
          cv tr tsd w Dist.b = j ∧ cv tr tsd w Dist.N2 = cv tr tsd x Dist.N2 - cv tr tsd x Dist.al)) := by
  have hD := G.hD
  have OS := G.OS
  have hn1 := S.n1
  have hn64 := S.n64
  have hm : (ScanDist.interactions[8]!).multNat tr tsd w pub ≠ 0 := by
    rw [Mem.multNat_c (by rw [ScanDist.dlr_def]), hrg]; simp
  obtain ⟨x, hx, i', hi', hb', hs', hmsg, hm'⟩ := recv_matched G.hH OS.lt DX.only DX.pub OS.lt hw
    (by rw [OS.tab]; exact Scan.sd_mem 8 (by decide)) (by rw [ScanDist.dlr_def]) (by rw [ScanDist.dlr_def]) hm
  rw [OS.tab] at hi'
  have e7 := ScanDist.dlx_send_i i' hi' hb' hs'
  subst e7
  have hsg : cv tr tsd x Dist.dlsg = 1 := Codec.one_of_mult (i := ScanDist.interactions[7]!) rfl hm'
  rw [ScanDist.dls_def, ScanDist.dlr_def] at hmsg
  simp only [Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨m0, m1, m2, m3, m4, m5, -⟩ := hmsg
  have q0 : cv tr tsd x Dist.tau = cv tr tsd w Dist.tau := congrArg Fp.toNat m0
  have q1 : cv tr tsd x Dist.da = cv tr tsd w Dist.a := congrArg Fp.toNat m1
  have q2 : cv tr tsd x Dist.db = cv tr tsd w Dist.b := congrArg Fp.toNat m2
  have q3 : cv tr tsd x Dist.r = cv tr tsd w Dist.r := congrArg Fp.toNat m3
  have q5 : cv tr tsd x Dist.sL = cv tr tsd w Dist.L2 := congrArg Fp.toNat m5
  -- `N2 − al` on the sender, when `al ≤ N2`
  have q4 : cv tr tsd x Dist.al ≤ cv tr tsd x Dist.N2 →
      cv tr tsd w Dist.N2 = cv tr tsd x Dist.N2 - cv tr tsd x Dist.al := fun hle => by
    have e := Scan.eval_ofNat (tr := tr) (t := tsd) (pub := pub) (w := x)
      (e := sub (c Dist.N2) (c Dist.al)) (v := cv tr tsd x Dist.N2 - cv tr tsd x Dist.al)
      (by simp only [zev_sub, zev_c, cur_cv]; omega)
    rw [e] at m4
    have := congrArg Fp.toNat m4
    rw [toNat_ofNat_lt' (by have := cv_lt (tr := tr) (t := tsd) x Dist.N2; omega)] at this
    exact this.symm
  refine ⟨x, hx, q3, q5, ?_⟩
  have hkx := Dist.dlsg_kind hD hx hsg
  obtain ⟨hlo, hhi⟩ := G.in_sec hP S hx (by rcases hkx with h | h <;> simp [h]) (q0.trans hτ)
  obtain ⟨SR, HR, CR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
  rcases Dist.decode S.n1 hlo hhi with ⟨sd, y, hsd, hy, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · obtain ⟨-, hs, hside, ha, -⟩ := SR sd y hsd hy
    obtain ⟨-, hal, -, D0, D1⟩ := Dist.shard_dl hD hx hs
    have hN := q4 (by rw [hal]; exact Nat.zero_le _)
    rw [hal, Nat.sub_zero] at hN
    rcases (by omega : sd = 0 ∨ sd = 1) with rfl | rfl
    · obtain ⟨d1, d2⟩ := D0 hside
      exact Or.inl ⟨y, hy, rfl, by rw [← q1, d1, ha], by rw [← q2, d2], hN⟩
    · obtain ⟨d1, d2⟩ := D1 hside
      exact Or.inr (Or.inl ⟨y, hy, rfl, by rw [← q1, d1], by rw [← q2, d2, ha], hN⟩)
  · obtain ⟨-, hg, -⟩ := HR i hi
    have := (Dist.hdr_dl hD hx hg).1
    omega
  · obtain ⟨-, hc, ha, hb, hic⟩ := CR i j hi hj
    obtain ⟨g1, -, d1, d2, -⟩ := Dist.cell_dl hD hx hc
    have he2 := Dist.e2_cell hD hx hc (by omega) (by rw [hic.2, S.nn]; exact S.n1) (by rw [hic.2, S.nn]; exact S.n64)
    rw [ha, hic.2, S.nn] at he2
    have hi1 : i + 1 < P.n := by
      by_cases hc' : i + 1 < P.n
      · exact hc'
      · rw [if_pos (by omega)] at he2
        omega
    have hal : cv tr tsd (w0 + 2 * P.n + i * (P.n + 1) + 1 + j) Dist.al ≤
        cv tr tsd (w0 + 2 * P.n + i * (P.n + 1) + 1 + j) Dist.N2 := by
      have hb := Dist.bool_of hD hx (x := Dist.al) (by simp [Dist.boolCols])
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h
      · rw [h]; exact Nat.zero_le _
      · have := (Dist.cell_div hD hx h).2.2.2.2.1; omega
    exact Or.inr (Or.inr ⟨i, j, hi1, hj, rfl, by rw [← q1, d1, ha]; exact Nat.mod_eq_of_lt (by omega),
      by rw [← q2, d2, hb], q4 hal⟩)

/-- **b4: the grid delay line.** Header `i` holds sender shard row `i`'s `(r, N2, L2)`; cell
`(0, j)` holds receiver shard row `j`'s; cell `(i + 1, j)` holds `(r, N2 − al, sL)` of cell `(i, j)`. -/
theorem grid_dl (DX : SdlxOwn AP tsd) {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P)
    (S : SecOk tr tsd w0 τ P) :
    (∀ i, i < P.n →
      cv tr tsd (Dist.hdrAt w0 P.n i) Dist.r = Dist.shardAt tr tsd w0 P.n 0 i ∧
      cv tr tsd (Dist.hdrAt w0 P.n i) Dist.N2 = cv tr tsd (w0 + 0 * P.n + i) Dist.N2 ∧
      cv tr tsd (Dist.hdrAt w0 P.n i) Dist.L2 = cv tr tsd (w0 + 0 * P.n + i) Dist.L2) ∧
    (∀ j, j < P.n →
      cv tr tsd (Dist.cellAt w0 P.n 0 j) Dist.r = Dist.shardAt tr tsd w0 P.n 1 j ∧
      cv tr tsd (Dist.cellAt w0 P.n 0 j) Dist.N2 = cv tr tsd (w0 + 1 * P.n + j) Dist.N2 ∧
      cv tr tsd (Dist.cellAt w0 P.n 0 j) Dist.L2 = cv tr tsd (w0 + 1 * P.n + j) Dist.L2) ∧
    (∀ i j, i + 1 < P.n → j < P.n →
      cv tr tsd (Dist.cellAt w0 P.n (i + 1) j) Dist.r = cv tr tsd (Dist.cellAt w0 P.n i j) Dist.r ∧
      cv tr tsd (Dist.cellAt w0 P.n (i + 1) j) Dist.N2 =
        cv tr tsd (Dist.cellAt w0 P.n i j) Dist.N2 - cv tr tsd (Dist.cellAt w0 P.n i j) Dist.al ∧
      cv tr tsd (Dist.cellAt w0 P.n (i + 1) j) Dist.L2 = cv tr tsd (Dist.cellAt w0 P.n i j) Dist.sL) := by
  have hD := G.hD
  have hn64 := S.n64
  obtain ⟨SR, HR, CR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun i j hi hj => ?_⟩
  · obtain ⟨hw, hg, ha, hic⟩ := HR i hi
    have hb := (Dist.hdr_next hD hw hg).1
    obtain ⟨x, hx, hr, hsl, C⟩ := G.dl_sender DX hP S hw (Dist.hdr_dl hD hw hg).2 (hic.1.trans S.tau)
    unfold Dist.hdrAt
    rcases C with ⟨y, hy, rfl, h1, -, h3⟩ | ⟨y, hy, -, -, h2, -⟩ | ⟨i', j', -, hj', -, -, h2, -⟩
    · have hyi : y = i := by omega
      subst hyi
      obtain ⟨-, hs, -⟩ := SR 0 y (by decide) hy
      have := (Dist.shard_dl hD hx hs).2.2.1
      exact ⟨hr.symm, h3, by rw [← hsl, this]⟩
    · omega
    · omega
  · obtain ⟨hw, hc, ha, hb, hic⟩ := CR 0 j S.n1 hj
    obtain ⟨-, hrg, -⟩ := Dist.cell_dl hD hw hc
    obtain ⟨x, hx, hr, hsl, C⟩ := G.dl_sender DX hP S hw hrg (hic.1.trans S.tau)
    unfold Dist.cellAt
    rcases C with ⟨y, hy, -, -, h2, -⟩ | ⟨y, hy, rfl, -, h2, h3⟩ | ⟨i', j', -, -, -, h1, -⟩
    · omega
    · have hyj : y = j := by omega
      subst hyj
      obtain ⟨-, hs, -⟩ := SR 1 y (by decide) hy
      have := (Dist.shard_dl hD hx hs).2.2.1
      exact ⟨hr.symm, h3, by rw [← hsl, this]⟩
    · omega
  · obtain ⟨hw, hc, ha, hb, hic⟩ := CR (i + 1) j hi hj
    obtain ⟨-, hrg, -⟩ := Dist.cell_dl hD hw hc
    obtain ⟨x, hx, hr, hsl, C⟩ := G.dl_sender DX hP S hw hrg (hic.1.trans S.tau)
    unfold Dist.cellAt
    rcases C with ⟨y, hy, -, -, h2, -⟩ | ⟨y, hy, -, h1, -⟩ | ⟨i', j', -, -, rfl, h1, h2, h3⟩
    · omega
    · omega
    · have e1 : i' = i := by omega
      have e2 : j' = j := by omega
      subst e1 e2
      exact ⟨hr.symm, h3, hsl.symm⟩

end GridPub

end

end ZkFormal.NearV3.Sched

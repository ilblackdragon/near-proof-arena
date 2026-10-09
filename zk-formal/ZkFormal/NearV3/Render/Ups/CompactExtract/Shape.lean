import ZkFormal.NearV3.Render.Ups.CompactExtract.Fields
import ZkFormal.NearV3.Extract.Ups.LayoutShape
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
set_option maxHeartbeats 1000000
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

theorem oneHot {r : Nat} (hr : r < s.rows.length) (hq : s.row r qb = 1) : OneHot (s.row r) :=
  ⟨fun x hx => le1 (stBool (okRow hw hs hr) (rowLt hw hs _) hx), by
    rw [stSum (okRow hw hs hr) (rowLt hw hs _), hq]⟩

/-- Successions in naturals at a field end inside a part. -/
theorem succNat {r : Nat} (hr : r + 1 < s.rows.length) (hC : OneHot (s.row r)) (hD : OneHot (s.row (r + 1)))
    (hfe : s.row r fe = 1) {tl te b1 b2 nk nc : Nat}
    (htl : s.row r qtl = tl) (hte : s.row r qte = te) (hb1 : s.row r qtb1 = b1) (hb2 : s.row r qtb2 = b2)
    (hnk : s.row r nokey = nk) (hnc : s.row r nochild = nc)
    (bt : tl ≤ 1 ∧ te ≤ 1 ∧ b1 ≤ 1 ∧ b2 ≤ 1 ∧ nk ≤ 1 ∧ nc ≤ 1) :
    let C := s.row r; let D := s.row (r + 1)
    (C sTAG = 1 → D sHPL = tl + te ∧ D sBM = b1 ∧ D sVLEN = b2) ∧
    (C sHPL = 1 → D sHPF = 1) ∧
    (C sHPF = 1 → D sKEY + nk = 1 ∧ D sVLEN = nk * tl ∧ D sCH = nk * te) ∧
    (C sKEY = 1 → D sVLEN = tl ∧ D sCH = te) ∧
    (C sVLEN = 1 → D sVH = 1) ∧
    (C sVH = 1 → D sMEM = tl ∧ D sBM = b2) ∧
    (C sBM = 1 → D sMEM = nc ∧ D sCH + nc = 1) ∧
    (C sCH = 1 → D sCH + D sMEM = 1 ∧ D sMEM = C lastw) := by
  intro C D
  subst htl hte hb1 hb2 hnk hnc
  have S := fieldSucc (okIn hw hs hr) (rowLt hw hs (r + 1)) hfe
  have hP := P_gt
  have Cb := hC.bs; have Db := hD.bs
  have lw := le1 (rowBool (okIn hw hs hr) (rowLt hw hs _) (x := lastw) (by simp [rowBools]))
  obtain ⟨t1, t2, t3, t4, t5, nc1⟩ := bt
  simp only [C, D] at S ⊢
  refine ⟨fun h => ?_, fun h => (S.2.1 h), fun h => ?_, fun h => ?_, fun h => S.2.2.2.2.1 h, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, b', c'⟩ := S.1 h
    refine ⟨nat_of_fp (by omega) (by omega) (by rw [natCast_add]; exact a), nat_of_fp (by omega) (by omega) b',
      nat_of_fp (by omega) (by omega) c'⟩
  · obtain ⟨a, b', c'⟩ := S.2.2.1 h
    refine ⟨nat_of_fp (by omega) (by omega) (by rw [natCast_add, a]; grind),
      nat_of_fp (by omega) (by have := Nat.mul_le_mul t5 t1; omega) (by rw [natCast_mul]; exact b'),
      nat_of_fp (by omega) (by have := Nat.mul_le_mul t5 t2; omega) (by rw [natCast_mul]; exact c')⟩
  · obtain ⟨a, b'⟩ := S.2.2.2.1 h
    exact ⟨nat_of_fp (by omega) (by omega) a, nat_of_fp (by omega) (by omega) b'⟩
  · obtain ⟨a, b'⟩ := S.2.2.2.2.2.1 h
    exact ⟨nat_of_fp (by omega) (by omega) a, nat_of_fp (by omega) (by omega) b'⟩
  · obtain ⟨a, b'⟩ := S.2.2.2.2.2.2.1 h
    exact ⟨nat_of_fp (by omega) (by omega) a, nat_of_fp (by omega) (by omega) (by rw [natCast_add, b']; grind)⟩
  · obtain ⟨a, b'⟩ := S.2.2.2.2.2.2.2 h
    exact ⟨nat_of_fp (by omega) (by omega) (by rw [natCast_add]; exact a), nat_of_fp (by omega) (by omega) b'⟩

variable {o ℓ : Nat} (hℓ : 0 < ℓ) (hle : o + ℓ ≤ s.rows.length)
  (hq : ∀ d, d < ℓ → s.row (o + d) qb = 1 ∧ (s.row (o + d) pf = 1 ↔ d = 0) ∧ (s.row (o + d) pl = 1 ↔ d + 1 = ℓ))
  (hpc : ∀ d, d < ℓ → ∀ x ∈ partConst, s.row (o + d) x = s.row o x)
  {fl : List (Nat × Nat)} (hc : Consec 0 fl) (hcov : segEnd 0 fl = ℓ) (hn : 0 < fl.length)
  (hF : ∀ q (h : q < fl.length), UField s (o + fl[q].1) fl[q].2 ∧ fl[q].1 + fl[q].2 ≤ ℓ)
include hℓ hle hq hpc hc hcov hn hF

/-- The state of field `q` holds on its last row. -/
theorem fEndRow {q : Nat} (h : q < fl.length) {re : Nat} (hre0 : re = o + fl[q].1 + fl[q].2 - 1) :
    re < o + ℓ ∧ stOf (s.row re) = stOf (s.row (o + fl[q].1)) ∧ s.row re fe = 1 ∧ s.row re idx = fl[q].2 - 1 ∧
      OneHot (s.row re) := by
  obtain ⟨U, hle'⟩ := hF q h
  have hp := U.pos
  have hre : re = o + fl[q].1 + (fl[q].2 - 1) := by omega
  have hd : re - o < ℓ := by omega
  have hqb := (hq (re - o) hd).1
  rw [show o + (re - o) = re by omega] at hqb
  refine ⟨by omega, ?_, ?_, ?_, oneHot hw hs (by omega) hqb⟩
  · have st := fun x (hx : x ∈ states) => U.st (fl[q].2 - 1) (by omega) x hx
    unfold stOf; rw [hre]
    rw [st sHPL (by simp [states]), st sHPF (by simp [states]), st sKEY (by simp [states]),
      st sVLEN (by simp [states]), st sVH (by simp [states]), st sBM (by simp [states]), st sCH (by simp [states]),
      st sMEM (by simp [states])]
  · rw [hre]; exact (U.fe _ (by omega)).2 (by omega)
  · rw [hre]; exact U.idx _ (by omega)

/-- The last field ends the part with `MEM`; a `MEM` field is the last one. -/
theorem memLast {q : Nat} (h : q < fl.length) :
    (stOf (s.row (o + fl[q].1)) = 8 ↔ q + 1 = fl.length) := by
  obtain ⟨hre, hst, hfe, -, hoh⟩ := fEndRow hw hs hℓ hle hq hpc hc hcov hn hF h (re := o + fl[q].1 + fl[q].2 - 1) rfl
  have hpos := (hF q h).1.pos
  have hle2 := (hF q h).2
  generalize hre' : o + fl[q].1 + fl[q].2 - 1 = re at hre hst hfe hoh
  have hd : re - o < ℓ := by omega
  have hqb := (hq (re - o) hd).1
  have hpl := (hq (re - o) hd).2.2
  rw [show o + (re - o) = re by omega] at hqb hpl
  have F := fieldR hw hs (r := re) (by omega)
  have e := F.2.2.2.2.2.2 hqb
  rw [hfe, Nat.mul_one] at e
  have hb := hoh.bs; have hsum := hoh.sum
  have hlast := segEnd_last fl 0 hc hn
  rw [hcov] at hlast
  constructor
  · intro h8
    have : s.row re sMEM = 1 := by unfold stOf at hst h8; omega
    have hp1 := hpl.1 (by rw [e, this])
    rcases Nat.lt_or_ge (q + 1) fl.length with hl | hl
    · have := consec_get fl 0 hc q hl
      have := (hF (q + 1) hl).1.pos; have := (hF (q + 1) hl).2
      omega
    · omega
  · intro hl
    have : q = fl.length - 1 := by omega
    subst this
    have hp1 : s.row re pl = 1 := hpl.2 (by omega)
    rw [e] at hp1
    unfold stOf at hst ⊢; omega

/-- The first field is `TAG`. -/
theorem fFirst : stOf (s.row (o + fl[0].1)) = 0 := by
  rw [consec_head fl 0 hc hn, Nat.add_zero]
  have h0 := hq 0 hℓ
  simp only [Nat.add_zero] at h0
  have F := fieldR hw hs (r := o) (by omega)
  have hT := (F.2.2.1 (h0.2.1.2 trivial) h0.1).1
  have hoh := oneHot hw hs (r := o) (by omega) h0.1
  have := hoh.bs; have := hoh.sum
  unfold stOf; omega

/-- Field lengths. -/
theorem fLen {q : Nat} (h : q < fl.length) : fl[q].2 = lenSt (s.row o qhk) (stOf (s.row (o + fl[q].1))) := by
  obtain ⟨hre, hst, hfe, hidx, hoh⟩ := fEndRow hw hs hℓ hle hq hpc hc hcov hn hF h (re := o + fl[q].1 + fl[q].2 - 1) rfl
  have hpos := (hF q h).1.pos
  have hle2 := (hF q h).2
  have hm := lenLe hw hs
  have hP := P_big
  generalize hre' : o + fl[q].1 + fl[q].2 - 1 = re at hre hst hfe hidx hoh
  have hk : s.row re qhk = s.row o qhk := by
    have := hpc (re - o) (by omega) qhk (by simp [partConst, qhk]); rwa [show o + (re - o) = re by omega] at this
  have hb := hoh.bs; have hsum := hoh.sum
  have hkP := rowLt hw hs re qhk
  have cv : ∀ n, n < P → ((fl[q].2 - 1 : Nat) : Fp) = ((n : Nat) : Fp) → fl[q].2 = n + 1 := fun n hn e => by
    have := natv (by omega) hn e; omega
  have hcase : s.row re sTAG = 1 ∨ s.row re sHPL = 1 ∨ s.row re sHPF = 1 ∨ s.row re sKEY = 1 ∨
      s.row re sVLEN = 1 ∨ s.row re sVH = 1 ∨ s.row re sBM = 1 ∨ s.row re sCH = 1 ∨ s.row re sMEM = 1 := by omega
  have hkey : ∀ m, m + 2 < P → (m : Fp) + 2 = (s.row re qhk : Fp) → m + 2 = s.row re qhk := fun m hm e =>
    natv hm hkP (by rw [natCast_add]; exact e)
  have hlen := (hF q h).1.pos
  have hsmall : fl[q].2 - 1 + 2 < P := by omega
  have P32 : (31 : Nat) < P := by omega
  have O := stOf_one hoh
  have hre0 : re < s.rows.length := by omega
  clear hm hP hre' hle2 hpos
  have E := fieldEnd (okRow hw hs (i := re) hre0) hfe
  simp only [FieldEndP, hidx] at E
  rw [← hst, ← hk]
  rcases hcase with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · rw [O.1 h1, cv 0 (Nat.lt_trans (by decide) P32) (E.1 h1)]; rfl
  · rw [O.2.1 h1, cv 3 (Nat.lt_trans (by decide) P32) (E.2.1 h1)]; rfl
  · rw [O.2.2.1 h1, cv 0 (Nat.lt_trans (by decide) P32) (E.2.2.1 h1)]; rfl
  · rw [O.2.2.2.1 h1]
    have := hkey _ hsmall (E.2.2.2.1 h1)
    clear E cv hkey O
    simp only [lenSt]; omega
  · rw [O.2.2.2.2.1 h1, cv 3 (Nat.lt_trans (by decide) P32) (E.2.2.2.2.1 h1)]; rfl
  · rw [O.2.2.2.2.2.1 h1, cv 31 P32 (E.2.2.2.2.2.1 h1)]; rfl
  · rw [O.2.2.2.2.2.2.1 h1, cv 1 (Nat.lt_trans (by decide) P32) (E.2.2.2.2.2.2.1 h1)]; rfl
  · rw [O.2.2.2.2.2.2.2.1 h1, cv 31 P32 (E.2.2.2.2.2.2.2.1 h1)]; rfl
  · rw [O.2.2.2.2.2.2.2.2 h1, cv 7 (Nat.lt_trans (by decide) P32) (E.2.2.2.2.2.2.2.2 h1)]; rfl

/-- A field end followed by another field: the successions in naturals. -/
theorem fStep {q : Nat} (h : q + 1 < fl.length) :
    ∃ re, re + 1 < s.rows.length ∧ OneHot (s.row re) ∧ OneHot (s.row (re + 1)) ∧
      stOf (s.row re) = stOf (s.row (o + fl[q].1)) ∧ re + 1 = o + fl[q + 1].1 ∧ s.row re lastw ≤ 1 ∧
      (s.row o qte = 1 → s.row re sCH = 1 → s.row re lastw = 1) ∧
      (let C := s.row re; let D := s.row (re + 1)
       let tl := s.row o qtl; let te := s.row o qte; let b1 := s.row o qtb1; let b2 := s.row o qtb2
       let nk := s.row o nokey; let nc := s.row o nochild
       (C sTAG = 1 → D sHPL = tl + te ∧ D sBM = b1 ∧ D sVLEN = b2) ∧
       (C sHPL = 1 → D sHPF = 1) ∧
       (C sHPF = 1 → D sKEY + nk = 1 ∧ D sVLEN = nk * tl ∧ D sCH = nk * te) ∧
       (C sKEY = 1 → D sVLEN = tl ∧ D sCH = te) ∧
       (C sVLEN = 1 → D sVH = 1) ∧
       (C sVH = 1 → D sMEM = tl ∧ D sBM = b2) ∧
       (C sBM = 1 → D sMEM = nc ∧ D sCH + nc = 1) ∧
       (C sCH = 1 → D sCH + D sMEM = 1 ∧ D sMEM = C lastw)) := by
  have hq1 : q < fl.length := by omega
  obtain ⟨hre, hst, hfe, -, hoh⟩ := fEndRow hw hs hℓ hle hq hpc hc hcov hn hF hq1 (re := o + fl[q].1 + fl[q].2 - 1) rfl
  have hpos := (hF q hq1).1.pos
  have hnx := consec_get fl 0 hc q h
  have hle3 := (hF (q + 1) h).2
  have hpos3 := (hF (q + 1) h).1.pos
  generalize hre' : o + fl[q].1 + fl[q].2 - 1 = re at hre hst hfe hoh
  have hr1 : re + 1 = o + fl[q + 1].1 := by omega
  have hD := (hq (re + 1 - o) (by omega)).1
  rw [show o + (re + 1 - o) = re + 1 by omega] at hD
  have hohD := oneHot hw hs (r := re + 1) (by omega) hD
  have pc := fun x (hx : x ∈ partConst) => hpc (re - o) (by omega) x hx
  simp only [show o + (re - o) = re by omega] at pc
  have hb := partHead (okRow hw hs (i := o) (by omega)) (rowLt hw hs _) ((hq 0 hℓ).2.1.2 rfl)
    (by simpa using (hq 0 hℓ).1)
  obtain ⟨t1, t2, t3, t4, -, t5, t6, -⟩ := hb
  refine ⟨re, by omega, hoh, hohD, hst, hr1,
    le1 (rowBool (okRow hw hs (i := re) (by omega)) (rowLt hw hs _) (x := lastw) (by simp [rowBools])),
    fun ht hch => extLastw (okRow hw hs (i := re) (by omega)) (rowLt hw hs _)
      (by rw [pc qte (by simp [partConst, qte])]; exact ht) hch, ?_⟩
  exact succNat hw hs (r := re) (by omega) hoh hohD hfe (pc qtl (by simp [partConst, qtl]))
    (pc qte (by simp [partConst, qte])) (pc qtb1 (by simp [partConst, qtb1])) (pc qtb2 (by simp [partConst, qtb2]))
    (pc nokey (by simp [partConst, nokey])) (pc nochild (by simp [partConst, nochild]))
    ⟨le1 t1, le1 t2, le1 t3, le1 t4, le1 t5, le1 t6⟩

/-- The field state succession, as naturals on the state indices. -/
theorem gStep {q : Nat} (h : q + 1 < fl.length) {g0 g1 tl te b1 b2 nk nc : Nat}
    (e0 : stOf (s.row (o + fl[q].1)) = g0) (e1 : stOf (s.row (o + fl[q + 1].1)) = g1)
    (etl : s.row o qtl = tl) (ete : s.row o qte = te) (eb1 : s.row o qtb1 = b1) (eb2 : s.row o qtb2 = b2)
    (enk : s.row o nokey = nk) (enc : s.row o nochild = nc) :
    (g0 = 0 → g1 = tl + te + 6 * b1 + 4 * b2) ∧
    (g0 = 1 → g1 = 2) ∧
    (g0 = 2 → tl + te = 1 → nk = 0 → g1 = 3) ∧
    (g0 = 2 → tl + te = 1 → nk = 1 → g1 = 4 * tl + 7 * te) ∧
    (g0 = 3 → tl + te = 1 → g1 = 4 * tl + 7 * te) ∧
    (g0 = 4 → g1 = 5) ∧
    (g0 = 5 → tl + b2 = 1 → g1 = 8 * tl + 6 * b2) ∧
    (g0 = 6 → g1 = 8 * nc + 7 * (1 - nc)) ∧
    (g0 = 7 → g1 = 7 ∨ g1 = 8) ∧ (g0 = 7 → te = 1 → g1 = 8) := by
  have hq1 : q < fl.length := by omega
  obtain ⟨re, hr, hC, hD, hst, hr1, hlw, hext, S⟩ := fStep hw hs hℓ hle hq hpc hc hcov hn hF h
  have hb := partHead (okRow hw hs (i := o) (by omega)) (rowLt hw hs _) ((hq 0 hℓ).2.1.2 rfl)
    (by simpa using (hq 0 hℓ).1)
  obtain ⟨t1, t2, t3, t4, tsum, t5, t6, -⟩ := hb
  rw [← hst] at e0
  rw [← hr1] at e1
  subst etl ete eb1 eb2 enk enc e0 e1
  simp only at S
  obtain ⟨S0, S1, S2, S3, S4, S5, S6, S7⟩ := S
  have Cb := hC.bs; have Cs := hC.sum; have Db := hD.bs; have Ds := hD.sum
  have l1 := le1 t1; have l2 := le1 t2; have l3 := le1 t3; have l4 := le1 t4; have l5 := le1 t5; have l6 := le1 t6
  have I := stOf_inv hC
  have O := stOf_one hD
  clear hst hr1 hF hq hpc
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 ht hk => ?_, fun h0 ht hk => ?_, fun h0 ht => ?_, fun h0 => ?_,
    fun h0 ht => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 ht => ?_⟩
  · have := S0 (I.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S1 (I.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S2 (I.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; rw [hk, Nat.zero_mul, Nat.zero_mul] at this
    unfold stOf; omega
  · have := S2 (I.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; rw [hk, Nat.one_mul, Nat.one_mul] at this
    unfold stOf; omega
  · have := S3 (I.2.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S4 (I.2.2.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S5 (I.2.2.2.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S6 (I.2.2.2.2.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S7 (I.2.2.2.2.2.2.2.1 h0); clear S0 S1 S2 S3 S4 S5 S6 S7; unfold stOf; omega
  · have := S7 (I.2.2.2.2.2.2.2.1 h0); have hl := hext ht (I.2.2.2.2.2.2.2.1 h0)
    clear S0 S1 S2 S3 S4 S5 S6 S7; rw [hl] at this; unfold stOf; omega

/-- **The field list of a node part** (states and lengths), by node type; a branch has `w`
windows, `w = 0` iff `nochild`. -/
theorem partShape : ∃ w,
    fl.map (fun p => (stOf (s.row (o + p.1)), p.2)) =
      shapeU (s.row o qtl) (s.row o qte) (s.row o qtb1) (s.row o nokey) (s.row o qhk) w ∧
    (s.row o qtl + s.row o qte = 0 → (w = 0 ↔ s.row o nochild = 1)) := by
  -- the state of field `q`
  obtain ⟨G, hGd⟩ : ∃ G : Nat → Nat, G = fun q => stOf (s.row (o + (fl.getD q (0, 0)).1)) := ⟨_, rfl⟩
  have hG : ∀ q (h : q < fl.length), stOf (s.row (o + fl[q].1)) = G q := fun q h => by
    rw [hGd]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have hlen : ∀ q (h : q < fl.length), fl[q].2 = lenSt (s.row o qhk) (G q) := fun q h => by
    rw [fLen hw hs hℓ hle hq hpc hc hcov hn hF h, hG q h]
  have hmap : fl.map (fun p => (stOf (s.row (o + p.1)), p.2)) =
      (List.range fl.length).map (fun q => (G q, lenSt (s.row o qhk) (G q))) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map] at h1
    rw [hG i h1, hlen i h1]
  rw [hmap]
  have G0 : G 0 = 0 := by rw [← hG 0 hn]; exact fFirst hw hs hℓ hle hq hpc hc hcov hn hF
  have GL : ∀ q, q < fl.length → (G q = 8 ↔ q + 1 = fl.length) := fun q h => by
    rw [← hG q h]; exact memLast hw hs hℓ hle hq hpc hc hcov hn hF h
  have adv : ∀ q, q < fl.length → G q ≠ 8 → q + 1 < fl.length := fun q h h8 => by
    rcases Nat.lt_or_ge (q + 1) fl.length with h' | h'
    · exact h'
    · exact absurd ((GL q h).2 (by omega)) h8
  have hb := partHead (okRow hw hs (i := o) (by omega)) (rowLt hw hs _) ((hq 0 hℓ).2.1.2 rfl)
    (by simpa using (hq 0 hℓ).1)
  obtain ⟨t1, t2, t3, t4, tsum, t5, t6, -⟩ := hb
  have ST := fun q (h : q + 1 < fl.length) =>
    gStep hw hs hℓ hle hq hpc hc hcov hn hF h (hG q (by omega)) (hG (q + 1) h) rfl rfl rfl rfl rfl rfl
  clear hmap hlen hG hF hc hcov hpc hq hle hGd
  generalize s.row o qtl = tl at *
  generalize s.row o qte = te at *
  generalize s.row o qtb1 = b1 at *
  generalize s.row o qtb2 = b2 at *
  generalize s.row o nokey = nk at *
  generalize s.row o nochild = nc at *
  generalize s.row o qhk = h at *
  generalize fl.length = n at *
  exact shapeRun hn (le1 t1) (le1 t2) (le1 t3) (le1 t4) tsum (le1 t5) (le1 t6) G0 GL ST

end

end ZkFormal.NearV3.Render.UpsRelay.Extract

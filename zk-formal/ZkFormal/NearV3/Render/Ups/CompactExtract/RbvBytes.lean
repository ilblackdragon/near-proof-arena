import ZkFormal.NearV3.Render.Ups.CompactExtract.WexBytes
import ZkFormal.NearV3.Extract.Ups.RbvBytes
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A copied bitmap byte without an insertion bit is the read byte. -/
theorem bCopyB (hcp : C cp = 1) (hba : C sBM = 0 ∨ (C ba0 = 0 ∧ C ba1 = 0)) : C b = C rb := by
  have f := factN ok hC hD (e := .mul (c cp) (sub (c b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0))
    (.mul (not (c fs)) (c ba1))))))) (memBytes (by simp [cBytes]))
  nev_simp at f
  have := hC b; have := hC rb
  simp only [P_lit] at *
  rcases hba with h | ⟨h1, h2⟩
  · simp [hcp, h] at f; omega
  · simp [hcp, h1, h2] at f; omega

/-- A terminal part (`up = 0`) reads no child id. -/
theorem rdcUp0 (hup : C UpsV3.up = 0) : C rdc = 0 := by
  have f := factN ok hC hD (e := sub (c rdc) (.mul (mul3 (c sCH) (c fs) (c tgt)) (c UpsV3.up))) (memFields (by simp [cFields]))
  have := hC rdc
  simp only [P_lit] at *
  nev_simp at f; simp [hup] at f; omega

/-- The windows of `RBR`, `RBV`, `MVE` are copied. -/
theorem chCopy (hch : C sCH = 1) (hk : C kRBR + C kRBV + C kMVE = 1) : C wfr = 0 := by
  have f := factN ok hC hD (e := mul3 (sumc [kRBR, kRBV, kMVE]) (c sCH) (c wfr)) (memFields (by simp [cFields]))
  have := hC wfr; have := hC kRBR; have := hC kRBV; have := hC kMVE
  simp only [P_lit] at *
  simp only [sumc, List.map_cons, List.map_nil] at f
  nev_simp at f
  rcases (show (C kRBR = 1 ∧ C kRBV = 0 ∧ C kMVE = 0) ∨ (C kRBR = 0 ∧ C kRBV = 1 ∧ C kMVE = 0) ∨
      (C kRBR = 0 ∧ C kRBV = 0 ∧ C kMVE = 1) by omega) with ⟨a, b', c'⟩ | ⟨a, b', c'⟩ | ⟨a, b', c'⟩ <;>
    simp [a, b', c', hch] at f <;> omega

/-- `RBV` copies read 36 bytes back. -/
theorem sposRBV (hrd : C rd = 1) (hk : C kRBV = 1) (ha : C aft = 1) (hq : 36 ≤ C qpos) : C spos = C qpos - 36 := by
  have f := pRBV ok hC hrd
  rw [hk, ha, cast1] at f
  exact sub_of_cast (hC _) (hC _) hq (by grind)

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **Copied rows** (bitmap bytes allowed when no bit is inserted). -/
theorem copyRunB (Pb : Nat → List Nat) (hR : UpbReads s Pb)
    {r n δ N : Nat} (hlt : r + n ≤ s.rows.length) (hδ : δ + n ≤ (Pb N).length)
    (hrows : ∀ d, d < n → s.row (r + d) cp = 1 ∧ s.row (r + d) rd = 1 ∧
      (s.row (r + d) sBM = 0 ∨ (s.row (r + d) ba0 = 0 ∧ s.row (r + d) ba1 = 0)) ∧
      s.row (r + d) spos = δ + d ∧ s.row (r + d) sN = N) :
    rowsB s r n = ((Pb N).drop δ).take n := by
  rw [← map_getD_slice _ _ _ hδ]
  apply rowsB_eq_map
  intro d hd
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrows d hd
  rw [bCopyB (okRow hw hs (i := r + d) (by omega)) (rowLt hw hs _) (nextLt hw hs _) h1 h3,
    (hR (r + d) (by omega) h2).1, h4, h5]

end

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- A part of a kind that is never an upper part is a terminal part (`up = 0`). -/
theorem upZero (k : Nat) (hk : k < ps.length) (hkd : 2 ≤ kd k ∧ kd k ≤ 10) : s.row ps[k].1 UpsV3.up = 0 := by
  rcases Nat.lt_or_ge k (nTof ci ti) with h | h
  · exact (hP.term k hk h).2.2.2.1
  · have := (hP.upper k hk h).1; omega

/-- **A value inserted into a branch** (`RBV`): its bytes are `nodeEnc (qRBV cs m val)`. -/
theorem ups_rbvBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 4) (val : NearSpec.Bytes)
    (Pb : Nat → List Nat) (cs : NearSpec.Kids) (m : Nat)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hdig : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 0 →
      s.row i dL = val.length → regN (s.row i) = (NearSpec.sha256 val).map UInt8.toNat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.branch none cs m)).map UInt8.toNat) (hm : m < 2 ^ 64)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRBV cs m val)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRBV cs m val).memD := by
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
  obtain ⟨hx0, hv0, htb2, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_RBV ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  obtain ⟨hℓ, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, ⟨U2, s2⟩, ⟨U3, s3⟩, W, ⟨U5, s5⟩⟩ := branchVShape hw hs U htb2 hq0 K.pf
  subst hℓ
  have hle := K.le
  -- TAG
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 2 by omega] at eT
  -- VLEN, VH (fresh)
  have hvz : vcpV ci 4 = 0 := by simp [vcpV, kdOf, UKind.all, b2n]
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
  -- the row states from `o + 37` on
  have stAt : ∀ d, 37 ≤ d → d < 47 + 32 * ww → OneHot (s.row (o + d)) ∧ o + d < s.rows.length ∧
      IxOf (s.row (o + d)) ci ti di si 4 (sdx k) ∧ (∀ x ∈ partConst, s.row (o + d) x = s.row o x) ∧
      s.row (o + d) qb = 1 ∧
      (d < 39 → s.row (o + d) sBM = 1) ∧ (39 ≤ d → d < 39 + 32 * ww → s.row (o + d) sCH = 1) ∧
      (39 + 32 * ww ≤ d → s.row (o + d) sMEM = 1) := by
    intro d h1 h2
    rcases Nat.lt_or_ge d 39 with h | h
    · have F := kField hw hs hsc K U3 s3 (by omega) (by omega) (d - 37) (by omega)
      rw [show o + 37 + (d - 37) = o + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, fun _ => (stOf_inv a1).2.2.2.2.2.2.1 a2, fun h' => by omega, fun h' => by omega⟩
    · rcases Nat.lt_or_ge d (39 + 32 * ww) with h' | h'
      · have hWe := W ((d - 39) / 32) (by omega)
        have F := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega) ((d - 39) % 32) (by omega)
        rw [show o + 39 + 32 * ((d - 39) / 32) + (d - 39) % 32 = o + d by omega] at F
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        exact ⟨a1, a3, a4, a5, a6, fun h'' => by omega, fun _ _ => (stOf_inv a1).2.2.2.2.2.2.2.1 a2, fun h'' => by omega⟩
      · have F := kField hw hs hsc K U5 s5 (by omega) (by omega) (d - (39 + 32 * ww)) (by omega)
        rw [show o + 39 + 32 * ww + (d - (39 + 32 * ww)) = o + d by omega] at F
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        exact ⟨a1, a3, a4, a5, a6, fun h'' => by omega, fun h'' => by omega,
          fun _ => (stOf_inv a1).2.2.2.2.2.2.2.2 a2⟩
  -- every row from `o + 37` reads at `qpos − 36`
  have readAt : ∀ d, 37 ≤ d → d < 47 + 32 * ww → s.row (o + d) rd = 1 →
      s.row (o + d) rb = (Pb (s.row o sN)).getD (d - 36) 0 ∧ s.row (o + d) plen = (Pb (s.row o sN)).length := by
    intro d h1 h2 hrd
    obtain ⟨hoh, hlt, hI, hpc, hq, hB, hC', hM⟩ := stAt d h1 h2
    have haft := (aftRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hI hq hoh.sum).1 rfl
    have := hoh.sum
    have ha := haft.1 (by
      rcases Nat.lt_or_ge d 39 with h | h
      · have := hB h; have := hoh.bs; omega
      · rcases Nat.lt_or_ge d (39 + 32 * ww) with h' | h'
        · have := hC' h h'; have := hoh.bs; omega
        · have := hM h'; have := hoh.bs; omega)
    have hqp : s.row (o + d) qpos = d := (U.rows d (by omega)).2.1
    have hsp := sposRBV (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hrd (hI.kd 4 (by omega)) ha (by omega)
    rw [hqp] at hsp
    have := hR (o + d) hlt hrd
    rwa [hsp, hpc sN (by decide)] at this
  -- the copied bitmap and windows
  have copyAt : ∀ d, d < 2 + 32 * ww → s.row (o + 37 + d) cp = 1 ∧ s.row (o + 37 + d) rd = 1 ∧
      (s.row (o + 37 + d) sBM = 0 ∨ (s.row (o + 37 + d) ba0 = 0 ∧ s.row (o + 37 + d) ba1 = 0)) ∧
      s.row (o + 37 + d) spos = 1 + d ∧ s.row (o + 37 + d) sN = s.row o sN := by
    intro d hd
    obtain ⟨hoh, hlt, hI, hpc, hq, hB, hC', hM⟩ := stAt (37 + d) (by omega) (by omega)
    rw [show o + (37 + d) = o + 37 + d by omega] at hoh hlt hI hpc hq hB hC' hM
    have hok := okRow hw hs hlt
    have hs1 := hoh.sum
    have hcp : s.row (o + 37 + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rcases Nat.lt_or_ge d 2 with h | h
      · rw [cpBM hok (rowLt hw hs _) hs1 (hB (by omega)), show s.row (o + 37 + d) kRDB = 0 from hI.kd 0 (by omega),
          show s.row (o + 37 + d) kRBR = 0 from hI.kd 3 (by omega), show s.row (o + 37 + d) kRBV = 1 from hI.kd 4 (by omega),
          show s.row (o + 37 + d) kRBI = 0 from hI.kd 5 (by omega)]; rfl
      · have hch := hC' (by omega) (by omega)
        rw [cpCH hok (rowLt hw hs _) hs1 hch, chCopy hok (rowLt hw hs _) (nextLt hw hs _) hch (by
          rw [show s.row (o + 37 + d) kRBR = 0 from hI.kd 3 (by omega), show s.row (o + 37 + d) kRBV = 1 from hI.kd 4 (by omega),
            show s.row (o + 37 + d) kMVE = 0 from hI.kd 7 (by omega)])]; rfl
    have hx : s.row (o + 37 + d) xcp = 0 := by rw [hpc xcp (by decide), hx0]
    have hrd : s.row (o + 37 + d) rd = 1 := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh
      (fun h => by
        rcases Nat.lt_or_ge d 2 with h' | h'
        · have := hB (by omega); omega
        · have := hC' (by omega) (by omega); omega)
      (fun h => ⟨hI.kd 6 (by omega), hI.kd 7 (by omega)⟩)
      (fun h => by
        rcases Nat.lt_or_ge d 2 with h' | h'
        · have := hB (by omega); omega
        · have := hC' (by omega) (by omega); omega)
      (fun _ => hx) (rdcUp0 hok (rowLt hw hs _) (nextLt hw hs _) (by rw [hpc _ (by decide), hup]))
    have hba : s.row (o + 37 + d) ba0 = 0 ∧ s.row (o + 37 + d) ba1 = 0 := by
      have := (kSel hw hs hsc K (r := o + 37 + d) (by omega) (by omega))
      rw [this.2.2.1, this.2.2.2.1]; simp [ba0V, ba1V, kdOf, UKind.all, b2n]
    have hrA := readAt (37 + d) (by omega) (by omega) (by rwa [show o + (37 + d) = o + 37 + d by omega])
    refine ⟨hcp, hrd, Or.inr hba, ?_, hpc sN (by decide)⟩
    have hsp := sposRBV hok (rowLt hw hs _) (nextLt hw hs _) hrd (hI.kd 4 (by omega))
      ((aftRow hok (rowLt hw hs _) (nextLt hw hs _) hI hq hs1).1 rfl |>.1 (by
        rcases Nat.lt_or_ge d 2 with h' | h'
        · have := hB (by omega); have := hoh.bs; omega
        · have := hC' (by omega) (by omega); have := hoh.bs; omega))
      (by rw [show s.row (o + 37 + d) qpos = 37 + d by
            have := (U.rows (37 + d) (by omega)).2.1; rwa [show o + (37 + d) = o + 37 + d by omega] at this]; omega)
    rw [hsp, show s.row (o + 37 + d) qpos = 37 + d by
      have := (U.rows (37 + d) (by omega)).2.1; rwa [show o + (37 + d) = o + 37 + d by omega] at this]
    omega
  -- the source's length, from a `MEM` read
  have FM0 := stAt (39 + 32 * ww) (by omega) (by omega)
  have hrdM : s.row (o + (39 + 32 * ww)) rd = 1 :=
    rdMem (okRow hw hs FM0.2.1) (rowLt hw hs _) (nextLt hw hs _) FM0.2.2.2.2.1 (FM0.2.2.2.2.2.2.2 (by omega))
      (FM0.2.2.1.kd 8 (by omega)) FM0.1
  have hpl := (readAt (39 + 32 * ww) (by omega) (by omega) hrdM).2
  have hpM := pMEM (okRow hw hs FM0.2.1) (rowLt hw hs _) FM0.1.sum hrdM (FM0.2.2.2.2.2.2.2 (by omega))
  have hidx : s.row (o + (39 + 32 * ww)) idx = 0 := by
    have := U5.idx 0 (by omega); rwa [show o + 39 + 32 * ww + 0 = o + (39 + 32 * ww) by omega] at this
  have hsp0 : s.row (o + (39 + 32 * ww)) spos = 3 + 32 * ww := by
    have hrA := hR _ FM0.2.1 hrdM
    have := sposRBV (okRow hw hs FM0.2.1) (rowLt hw hs _) (nextLt hw hs _) hrdM (FM0.2.2.1.kd 4 (by omega))
      ((aftRow (okRow hw hs FM0.2.1) (rowLt hw hs _) (nextLt hw hs _) FM0.2.2.1 FM0.2.2.2.2.1 FM0.1.sum).1 rfl |>.1
        (by have := FM0.2.2.2.2.2.2.2 (by omega); have := FM0.1.bs; have := FM0.1.sum; omega))
      (by rw [(U.rows (39 + 32 * ww) (by omega)).2.1]; omega)
    rw [this, (U.rows (39 + 32 * ww) (by omega)).2.1]; omega
  rw [hidx, hsp0] at hpM
  have hPlen : (Pb (s.row o sN)).length = 11 + 32 * ww := by
    rw [← hpl]
    have hlen := lenLe hw hs
    have e : ((11 + 32 * ww : Nat) : Fp) = ((s.row (o + (39 + 32 * ww)) plen : Nat) : Fp) := by
      rw [show 11 + 32 * ww = (3 + 32 * ww) + 8 by omega, natCast_add]
      rw [cast0] at hpM
      grind
    have := natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e
    omega
  -- the source bytes
  have hsrcL : (nodeEnc (.branch none cs m)).length = 11 + (NearSpec.Kids.hashes cs).length := by
    simp [nodeEnc, NearSpec.u16, leN_length, u64_length]; omega
  have hH : (NearSpec.Kids.hashes cs).length = 32 * ww := by
    have := congrArg List.length hsrc; rw [List.length_map, hsrcL, hPlen] at this; omega
  have cC := copyRunB hw hs Pb hR (r := o + 37) (n := 2 + 32 * ww) (δ := 1) (N := s.row o sN) (by omega)
    (by omega) copyAt
  have hP1 : ((Pb (s.row o sN)).drop 1).take (2 + 32 * ww) =
      (NearSpec.u16 (NearSpec.kidsBitmap cs 0) ++ NearSpec.Kids.hashes cs).map UInt8.toNat := by
    rw [hsrc]; simp [nodeEnc, NearSpec.u16, leN_length, hH, List.take_append_of_le_length]
    rw [← List.append_assoc, List.take_left' (by simp [leN_length, hH])]
  rw [hP1] at cC
  -- MEM
  have R5 := memRegs hw hs hsc K U5 s5 (by omega) (by omega)
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (39 + 32 * ww + i) (by omega) x hx
    rwa [show o + (39 + 32 * ww + i) = o + 39 + 32 * ww + i by omega] at this
  have rbM : ∀ i, i < 8 → s.row (o + 39 + 32 * ww + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
    intro i hi
    obtain ⟨hoh, hlt, hI, -, hq, -, -, hM⟩ := stAt (39 + 32 * ww + i) (by omega) (by omega)
    have hrd := rdMem (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq (hM (by omega)) (hI.kd 8 (by omega)) hoh
    have := (readAt (39 + 32 * ww + i) (by omega) (by omega) hrd).1
    rw [show o + (39 + 32 * ww + i) = o + 39 + 32 * ww + i by omega] at this
    rw [this, hsrc]
    simp only [nodeEnc, List.map_append, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [NearSpec.u16, leN_length, hH]; omega)]
    simp [NearSpec.u16, leN_length, hH]
    rw [show 39 + 32 * ww + i - 36 - (2 + 32 * ww + 1) = i by omega]
  have hA : limbs (fun i => s.row (o + 39 + 32 * ww + i) rb) 8 = m := by
    rw [show limbs (fun i => s.row (o + 39 + 32 * ww + i) rb) 8 =
        limbs (fun i => ((NearSpec.u64 m).map UInt8.toNat).getD i 0) 8 by
      simp only [limbs8]; rw [rbM 0 (by omega), rbM 1 (by omega), rbM 2 (by omega), rbM 3 (by omega),
        rbM 4 (by omega), rbM 5 (by omega), rbM 6 (by omega), rbM 7 (by omega)], limbs_u64]
    omega
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
      · simp [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
      · simp [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc]
      · simp only [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc, heL, heS,
          (R5 i hi).2.1]
        rcases (show s.row (o + 39 + 32 * ww + i) fs = 0 ∨ s.row (o + 39 + 32 * ww + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · have := hbyte (39 + 32 * ww + i) (by omega)
        rwa [show o + (39 + 32 * ww + i) = o + 39 + 32 * ww + i by omega] at this)
  simp only [hKc, heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hA] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + 39 + 32 * ww) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    simp only [UpsSpec.qRBV, NearSpec.valueMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?, Option.getD_some,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    omega
  -- assemble
  rw [hBy, eT, eV, eW, hD, show rowsB s (o + 37) 2 ++ (rowsB s (o + 39) (32 * ww) ++ rowsB s (o + 39 + 32 * ww) 8) =
    rowsB s (o + 37) (2 + 32 * ww) ++ rowsB s (o + 39 + 32 * ww) 8 by
      rw [rowsB_append, List.append_assoc, show o + 37 + 2 = o + 39 by omega], cC, eM]
  simp only [UpsSpec.qRBV, nodeEnc, NearSpec.Slot.valueRef, NearSpec.valueMem, List.map_append, List.map_cons,
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

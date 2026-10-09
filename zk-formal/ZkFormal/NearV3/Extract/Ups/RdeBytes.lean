import ZkFormal.NearV3.Extract.Ups.RlpBytes

/-!
# ZkFormal.NearV3.Extract.Ups.RdeBytes — extension descends `RDE` and pass-throughs `PT` (layer 2)

A part of kind `RDE` (index 1) or `PT` (index 11) rewrites the extension `.ext k c m` on the path
(`k = []` for `PT`): its `TAG HPL HPF [KEY]` bytes are copied from the source record, its child
window is fresh (the `DIGEST` of the part below, id `msgId 12 (512τ + j − 1)` at the length
`clen` the part below sends on `MEMD`) and `memory_usage = m + c'.memD − cm` (`m` read from the
source, `c'.memD` / `cm` the new / old child memory from `MEMD`).  So the part is
`nodeEnc (qRDE k m c' cm)` (`ups_rdeBytes`), and `nodeEnc (qPT m c' cm)` for `PT`
(`ups_ptBytes`).

Hypotheses (from other tables): the `UPB` reads return the source's post bytes `Pb` and the
source is `nodeEnc (.ext k c m)` with a 32-byte child hash and `m < 2^64`; the `DIGEST` lookup
of the part below at `clen` is `c'.hashOf`; the `MEMD` limbs received on the `MEM` rows are
`< 2^12` with values `c'.memD` (new) and `cm` (old); the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- The window of an extension-type upper part (`RDE WEX PT`) is fresh and not a new leaf. -/
theorem chUp (hch : C sCH = 1) (h5 : C kRBI = 0) (h10 : C kSPB = 0) (hk : C kRDE + C kWEX + C kPT = 1) :
    C wfr = 1 ∧ C wn = 0 := by
  have f1 := factN ok hC hD (e := mul3 (sumc [kRDE, kWEX, kPT]) (c sCH) (not (c wfr))) (memFields (by simp [cFields]))
  have f2 := factN ok hC hD (e := .mul (c sCH) (sub (c wn) (.add (.mul (c kRBI) (c tgt)) (.mul (c kSPB) (c wy)))))
    (memFields (by simp [cFields]))
  have := hC wfr; have := hC wn
  simp only [P_lit] at *
  simp only [sumc, List.map_cons, List.map_nil] at f1
  nev_simp at f1 f2
  simp only [hch, h5, h10] at f1 f2
  simp at f2
  have := hC kRDE; have := hC kWEX; have := hC kPT
  rcases (show (C kRDE = 1 ∧ C kWEX = 0 ∧ C kPT = 0) ∨ (C kRDE = 0 ∧ C kWEX = 1 ∧ C kPT = 0) ∨
      (C kRDE = 0 ∧ C kWEX = 0 ∧ C kPT = 1) by omega) with ⟨a, b', c'⟩ | ⟨a, b', c'⟩ | ⟨a, b', c'⟩ <;>
    simp [a, b', c'] at f1 <;> omega

/-- A `MEM` row of a part other than `NLF` reads the old memory byte. -/
theorem rdMem (hq : C qb = 1) (hm : C sMEM = 1) (hk : C kNLF = 0) (hoh : OneHot C) : C rd = 1 := by
  have f := factN ok hC hD (e := .mul (c qb) (sub (c rd) (.add (c cp) (sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF)), c rdc])))) (memBytes (by simp [cBytes]))
  have fm := factN ok hC hD (e := .mul (c sMEM) (c cp)) (memBytes (by simp [cBytes]))
  have hS := hoh.sum
  have hb := hoh.bs
  have hz : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 := by
    omega
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have hrdc := rdcOff ok hC hD z7
  have := hC rd; have := hC cp
  simp only [P_lit] at *
  simp only [sumc, kM, List.map_cons, List.map_nil] at f
  nev_simp at f fm
  simp only [hm] at fm
  simp at fm
  simp [hq, hm, hk, hrdc, z0, z1, z2, z3, z4, z5, z6, z7, fm] at f
  omega

/-- The child part of a descend / wrap / pass-through is the part below (`jm = j − 1`). -/
theorem jmRow (hpf : C pf = 1) (hk : C kRDB + C kRDE + C kWEX + C kPT = 1) (hj : 1 ≤ C j) : C jm = C j - 1 := by
  have f := factN ok hC hD (e := .mul (c pf) (.mul (sumc [kRDB, kRDE, kWEX, kPT]) (sub (c jm) (sub (c j) (k 1)))))
    (memPlan (by simp [cPlan]))
  have := hC jm; have := hC j
  simp only [P_lit] at *
  simp only [sumc, List.map_cons, List.map_nil] at f
  nev_simp at f
  have := hC kRDB; have := hC kRDE; have := hC kWEX; have := hC kPT
  rcases (show (C kRDB = 1 ∧ C kRDE = 0 ∧ C kWEX = 0 ∧ C kPT = 0) ∨ (C kRDB = 0 ∧ C kRDE = 1 ∧ C kWEX = 0 ∧ C kPT = 0) ∨
      (C kRDB = 0 ∧ C kRDE = 0 ∧ C kWEX = 1 ∧ C kPT = 0) ∨ (C kRDB = 0 ∧ C kRDE = 0 ∧ C kWEX = 0 ∧ C kPT = 1) by omega)
    with ⟨a, b', c', d'⟩ | ⟨a, b', c', d'⟩ | ⟨a, b', c', d'⟩ | ⟨a, b', c', d'⟩ <;>
    simp [hpf, a, b', c', d'] at f <;> omega

end

/-- `limbs` of the `u64` bytes. -/
theorem limbs_u64 (x : Nat) :
    limbs (fun i => ((NearSpec.u64 x).map UInt8.toNat).getD i 0) 8 = x % 2 ^ 64 := by
  rw [limbs8, toNats_u64]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  omega

theorem toNats_lt (xs : List UInt8) : ∀ i, (xs.map UInt8.toNat).getD i 0 < 256 := by
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? with
  | none => simp
  | some a => simpa using a.toNat_lt

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **An extension descend or pass-through part** (`RDE`, `PT`): its bytes are
`nodeEnc (.ext k c' (m + c'.memD − cm))`. -/
theorem ups_extUpBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 1 ∨ kd k = 11)
    (Pb : Nat → List Nat) (key : List Nat) (c c' : NearSpec.PTrie) (m cm : Nat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.ext key c m)).map UInt8.toNat)
    (hsl : (nodeEnc (.ext key c m)).length < 2 ^ 32) (hc32 : c.hashOf.length = 32) (hm : m < 2 ^ 64)
    (hdC : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = s.row ps[k].1 clen → regN (s.row i) = c'.hashOf.map UInt8.toNat)
    (hMd : ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv < 67108864 ∧ s.row (ps[k].1 + ps[k].2 - 8 + i) mCv < 67108864)
    (hmB : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mBv) 8 = c'.memD)
    (hmC : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mCv) 8 = cm)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (.ext key c' (m + c'.memD - cm))).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = m + c'.memD - cm := by
  have K := partK hw hs hL hP k hk
  obtain ⟨hj, U⟩ := hL.part k hk
  generalize hkk : kd k = ki at K hkd
  generalize ps[k].1 = o at K U hbyte hsrc hdC hMd hmB hmC hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte hMd hmB hmC ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  -- the part constants
  have HD : s.row o qte = 1 ∧ s.row o useA = 1 ∧ s.row o bN = 1 ∧ s.row o bL = 0 ∧ s.row o cO = 1 ∧
      s.row o cS = 0 ∧ s.row o Cc = 0 ∧ s.row o eL = 0 ∧ s.row o eS = 0 ∧ s.row o Kc = 0 := by
    rcases hkd with rfl | rfl
    · obtain ⟨-, -, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := head_RDE ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    · obtain ⟨-, -, a1, -, -, -, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
        head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  obtain ⟨hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ := HD
  have kv := fun d (hd : d < ℓ) m (hm : m < 12) => (K.ix d hd).kd m hm
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U5, s5⟩⟩ := extShape hw hs U hte hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U5 s5
  subst hℓ
  have hle := K.le
  -- TAG, HPL (grammar)
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 3 by omega] at eT
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1 + d) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  rw [show o+1+3=o+4 by omega, show s.row (o + 4) qhk = q by rw [← hqq]; exact K.pc 4 (by omega) qhk (by decide)] at eH
  have hq22 : q<2^22 := by have := lenLe hw hs; have := K.le; omega
  have hq32 : q<2^32 := by have := rowLt hw hs o qhk; rw [hqq,P_lit] at this; omega
  -- the copied rows `HPL HPF [KEY]`
  have copyAt : ∀ d, 1 ≤ d → d < 5 + q → s.row (o + d) cp = 1 ∧ s.row (o + d) rd = 1 ∧ s.row (o + d) sBM = 0 ∧
      s.row (o + d) spos = d ∧ s.row (o + d) sN = s.row o sN := by
    intro d h1 h2
    have hlt : o + d < s.rows.length := by omega
    have hst : OneHot (s.row (o + d)) ∧ (s.row (o + d) sHPL = 1 ∨ s.row (o + d) sHPF = 1 ∨ s.row (o + d) sKEY = 1) ∧
        (s.row (o + d) sKEY = 1 → 6 ≤ d) := by
      rcases Nat.lt_or_ge d 5 with h | h
      · have F := kField hw hs hsc K U1 s1 (by omega) (by omega) (d - 1) (by omega)
        rw [show o + 1 + (d - 1) = o + d by omega] at F
        have := F.1.sum; have := (stOf_inv F.1).2.1 F.2.1
        exact ⟨F.1, Or.inl ((stOf_inv F.1).2.1 F.2.1), fun _ => by omega⟩
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · subst h'
          have F := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
          simp only [Nat.add_zero] at F
          have := F.1.sum; have := (stOf_inv F.1).2.2.1 F.2.1
          exact ⟨F.1, Or.inr (Or.inl ((stOf_inv F.1).2.2.1 F.2.1)), fun _ => by omega⟩
        · have hk1 := KR.key (by omega)
          have F := kField hw hs hsc K hk1.1 hk1.2 (by omega) (by omega) (d - 6) (by omega)
          rw [show o + 5 + 1 + (d - 6) = o + d by omega] at F
          exact ⟨F.1, Or.inr (Or.inr ((stOf_inv F.1).2.2.2.1 F.2.1)), fun _ => by omega⟩
    obtain ⟨hoh, hS, hK6⟩ := hst
    have hok := okRow hw hs hlt
    have k1 : s.row (o + d) kRDE = if 1 = ki then 1 else 0 := kv d (by omega) 1 (by omega)
    have k2 : s.row (o + d) kRLP = 0 := by
      have := kv d (by omega) 2 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k6 : s.row (o + d) kMVL = 0 := by
      have := kv d (by omega) 6 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k7 : s.row (o + d) kMVE = 0 := by
      have := kv d (by omega) 7 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k11 : s.row (o + d) kPT = if 11 = ki then 1 else 0 := kv d (by omega) 11 (by omega)
    have hs1 := hoh.sum
    have hcp : s.row (o + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rcases hS with h | h | h
      · rw [cpHPL hok (rowLt hw hs _) hs1 h, k1, k2, k11]; rcases hkd with rfl | rfl <;> rfl
      · rw [cpHPF hok (rowLt hw hs _) hs1 h, k1, k2, k11]; rcases hkd with rfl | rfl <;> rfl
      · -- a `PT` part has no key rows
        rcases hkd with rfl | rfl
        · rw [cpKEY hok (rowLt hw hs _) hs1 h, k1, k2, k6, k7]; rfl
        · exfalso
          have H := head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
          have : q = 1 := by rw [← hqq]; exact H.2.2.2.2.2.1
          have := hK6 h
          omega
    have hbm : s.row (o + d) sBM = 0 := by rcases hS with h | h | h <;> omega
    have hch : s.row (o + d) sCH = 0 := by rcases hS with h | h | h <;> omega
    have hrd : s.row (o + d) rd = 1 := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) (K.qb d (by omega)) hcp hoh
      (fun h => by rcases hS with h' | h' | h' <;> omega) (fun _ => ⟨k6, k7⟩)
      (fun h => by rcases hS with h' | h' | h' <;> omega) (fun h => by omega)
      (rdcOff hok (rowLt hw hs _) (nextLt hw hs _) hch)
    refine ⟨hcp, hrd, hbm, ?_, K.pc d (by omega) sN (by decide)⟩
    rw [dirRow hok (rowLt hw hs _) (nextLt hw hs _) (K.ix d (by omega)) (by omega) hrd]
    exact (U.rows d (by omega)).2.1
  -- the source bytes
  have hlenE : (nodeEnc (.ext key c m)).length = 45 + (NearSpec.hexPrefix key false).length := by
    simp [nodeEnc, u32_length, u64_length, hc32]; omega
  have hPlen : (Pb (s.row o sN)).length = 45 + (NearSpec.hexPrefix key false).length := by
    rw [hsrc, List.length_map, hlenE]
  have cH := copyRun hw hs Pb hR (r := o + 1) (n := 4) (δ := 1) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (1 + d) (by omega) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  have hP1 : ((Pb (s.row o sN)).drop 1).take 4 = (NearSpec.u32 (NearSpec.hexPrefix key false).length).map UInt8.toNat := by
    rw [hsrc]; simp [nodeEnc, List.take_append_of_le_length, u32_length]
  rw [hP1, eH] at cH
  have hqhp : (NearSpec.hexPrefix key false).length = q :=
    u32_eq_full (by have := hlenE; omega) hq32 cH.symm
  have cK := copyRun hw hs Pb hR (r := o + 5) (n := q) (δ := 5) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (5 + d) (by omega) (by omega); rwa [show o + (5 + d) = o + 5 + d by omega] at this)
  have hP5 : ((Pb (s.row o sN)).drop 5).take q = (NearSpec.hexPrefix key false).map UInt8.toNat := by
    rw [hsrc, ← hqhp]; simp [nodeEnc, u32_length, List.take_append_of_le_length]
  rw [hP5] at cK
  -- CH (fresh: the part below's digest)
  have FC := kField hw hs hsc K U3 s3 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + 5 + q + d) sCH = 1 ∧ s.row (o + 5 + q + d) wfr = 1 ∧
      s.row (o + 5 + q + d) wn = 0 := by
    intro d hd
    have F := FC d hd
    have h7 := (stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1
    have hI := F.2.2.2.1
    have k1 : s.row (o + 5 + q + d) kRDE = if 1 = ki then 1 else 0 := hI.kd 1 (by omega)
    have k5 : s.row (o + 5 + q + d) kRBI = 0 := by have := hI.kd 5 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k9 : s.row (o + 5 + q + d) kWEX = 0 := by have := hI.kd 9 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k10 : s.row (o + 5 + q + d) kSPB = 0 := by have := hI.kd 10 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k11 : s.row (o + 5 + q + d) kPT = if 11 = ki then 1 else 0 := hI.kd 11 (by omega)
    have := chUp (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) h7 k5 k10
      (by rw [k1, k9, k11]; rcases hkd with rfl | rfl <;> rfl)
    exact ⟨h7, this⟩
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
    have k0 : s.row o kRDB = 0 := by have := I0.kd 0 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k1 : s.row o kRDE = if 1 = ki then 1 else 0 := I0.kd 1 (by omega)
    have k9 : s.row o kWEX = 0 := by have := I0.kd 9 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k11 : s.row o kPT = if 11 = ki then 1 else 0 := I0.kd 11 (by omega)
    rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by rw [k0, k1, k9, k11]; rcases hkd with rfl | rfl <;> rfl)
      (by omega), hj]
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
  have FM := kField hw hs hsc K U5 s5 (by omega) (by omega)
  have rbM : ∀ i, i < 8 → s.row (o + 37 + q + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
    intro i hi
    have F := FM i hi
    have hm8 := (stOf_inv F.1).2.2.2.2.2.2.2.2 F.2.1
    have k8 : s.row (o + 37 + q + i) kNLF = 0 := by have := F.2.2.2.1.kd 8 (by omega); rcases hkd with rfl | rfl <;> exact this
    have hrd := rdMem (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) F.2.2.2.2.2 hm8 k8 F.1
    rw [hR _ F.2.2.1 hrd, dirRow (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) F.2.2.2.1 (by omega) hrd,
      show s.row (o + 37 + q + i) qpos = 37 + q + i by
        have := (U.rows (37 + q + i) (by omega)).2.1; rwa [show o + (37 + q + i) = o + 37 + q + i by omega] at this,
      show s.row (o + 37 + q + i) sN = s.row o sN from pc5 i hi sN (by decide), hsrc]
    simp only [nodeEnc, List.map_append, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [u32_length, hc32, hqhp]; omega)]
    simp [u32_length, hc32, hqhp]
    rw [show 37 + q + i - (4 + (q + 32) + 1) = i by omega]
  have hA : limbs (fun i => s.row (o + 37 + q + i) rb) 8 = m := by
    rw [show limbs (fun i => s.row (o + 37 + q + i) rb) 8 =
        limbs (fun i => ((NearSpec.u64 m).map UInt8.toNat).getD i 0) 8 by
      simp only [limbs8]; rw [rbM 0 (by omega), rbM 1 (by omega), rbM 2 (by omega), rbM 3 (by omega),
        rbM 4 (by omega), rbM 5 (by omega), rbM 6 (by omega), rbM 7 (by omega)], limbs_u64]
    omega
  have hr0 : o + (45 + q) - 8 = o + 37 + q := by omega
  rw [hr0] at hMd hmB hmC
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U U5 s5 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + 37 + q + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [inA, pc5 i hi useA (by decide), huA, Nat.one_mul, rbM i hi]
        have := toNats_lt (NearSpec.u64 m) i; omega
      · simp only [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
        have := (hMd i hi).1; omega
      · simp only [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc]
        have := (hMd i hi).2; omega
      · simp [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc, heL, heS]
      · have := hbyte (37 + q + i) (by omega); rwa [show o + (37 + q + i) = o + 37 + q + i by omega] at this)
  simp only [hKc, heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hA, hmB, hmC] at eM eX
  refine ⟨?_, by rw [hr0, eX]; simp⟩
  -- assemble
  rw [hBy, eT, eH, cK, eW, eM]
  rw [show (List.range 32).map (fun i => s.row (o + 5 + q) (reg i)) = regN (s.row (o + 5 + q)) from rfl, hDC]
  simp only [nodeEnc, List.map_append, List.map_cons, List.map_nil, u32Bytes, toNats_u32, hqhp, List.append_assoc,
    List.cons_append, List.nil_append]

  simp only [List.cons.injEq, true_and]
  refine ⟨rfl, ?_⟩
  congr 3
  simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]

/-- An `RDE` / `PT` part looks up its child's digest (id `jm = k`, length `clen`) on its window. -/
theorem extUpLook (k : Nat) (hk : k < ps.length) (hkd : kd k = 1 ∨ kd k = 11)
    (Pb : Nat → List Nat) (key : List Nat) (c c' : NearSpec.PTrie) (m cm : Nat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.ext key c m)).map UInt8.toNat)
    (hsl : (nodeEnc (.ext key c m)).length < 2 ^ 32) (hc32 : c.hashOf.length = 32) (hm : m < 2 ^ 64)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    ∃ i, i < s.rows.length ∧ s.row i gD = 1 ∧ s.row i dI = upsIdN (s.row 0 tau) k ∧ s.row i dL = s.row ps[k].1 clen := by
  have K := partK hw hs hL hP k hk
  obtain ⟨hj, U⟩ := hL.part k hk
  generalize hkk : kd k = ki at K hkd
  generalize ps[k].1 = o at K U hbyte hsrc hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  -- the part constants
  have HD : s.row o qte = 1 ∧ s.row o useA = 1 ∧ s.row o bN = 1 ∧ s.row o bL = 0 ∧ s.row o cO = 1 ∧
      s.row o cS = 0 ∧ s.row o Cc = 0 ∧ s.row o eL = 0 ∧ s.row o eS = 0 ∧ s.row o Kc = 0 := by
    rcases hkd with rfl | rfl
    · obtain ⟨-, -, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := head_RDE ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    · obtain ⟨-, -, a1, -, -, -, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
        head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
  obtain ⟨hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ := HD
  have kv := fun d (hd : d < ℓ) m (hm : m < 12) => (K.ix d hd).kd m hm
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U5, s5⟩⟩ := extShape hw hs U hte hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U5 s5
  subst hℓ
  have hle := K.le
  -- TAG, HPL (grammar)
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 3 by omega] at eT
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1 + d) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  rw [show o+1+3=o+4 by omega, show s.row (o + 4) qhk = q by rw [← hqq]; exact K.pc 4 (by omega) qhk (by decide)] at eH
  have hq22 : q<2^22 := by have := lenLe hw hs; have := K.le; omega
  have hq32 : q<2^32 := by have := rowLt hw hs o qhk; rw [hqq,P_lit] at this; omega
  -- the copied rows `HPL HPF [KEY]`
  have copyAt : ∀ d, 1 ≤ d → d < 5 + q → s.row (o + d) cp = 1 ∧ s.row (o + d) rd = 1 ∧ s.row (o + d) sBM = 0 ∧
      s.row (o + d) spos = d ∧ s.row (o + d) sN = s.row o sN := by
    intro d h1 h2
    have hlt : o + d < s.rows.length := by omega
    have hst : OneHot (s.row (o + d)) ∧ (s.row (o + d) sHPL = 1 ∨ s.row (o + d) sHPF = 1 ∨ s.row (o + d) sKEY = 1) ∧
        (s.row (o + d) sKEY = 1 → 6 ≤ d) := by
      rcases Nat.lt_or_ge d 5 with h | h
      · have F := kField hw hs hsc K U1 s1 (by omega) (by omega) (d - 1) (by omega)
        rw [show o + 1 + (d - 1) = o + d by omega] at F
        have := F.1.sum; have := (stOf_inv F.1).2.1 F.2.1
        exact ⟨F.1, Or.inl ((stOf_inv F.1).2.1 F.2.1), fun _ => by omega⟩
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · subst h'
          have F := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
          simp only [Nat.add_zero] at F
          have := F.1.sum; have := (stOf_inv F.1).2.2.1 F.2.1
          exact ⟨F.1, Or.inr (Or.inl ((stOf_inv F.1).2.2.1 F.2.1)), fun _ => by omega⟩
        · have hk1 := KR.key (by omega)
          have F := kField hw hs hsc K hk1.1 hk1.2 (by omega) (by omega) (d - 6) (by omega)
          rw [show o + 5 + 1 + (d - 6) = o + d by omega] at F
          exact ⟨F.1, Or.inr (Or.inr ((stOf_inv F.1).2.2.2.1 F.2.1)), fun _ => by omega⟩
    obtain ⟨hoh, hS, hK6⟩ := hst
    have hok := okRow hw hs hlt
    have k1 : s.row (o + d) kRDE = if 1 = ki then 1 else 0 := kv d (by omega) 1 (by omega)
    have k2 : s.row (o + d) kRLP = 0 := by
      have := kv d (by omega) 2 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k6 : s.row (o + d) kMVL = 0 := by
      have := kv d (by omega) 6 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k7 : s.row (o + d) kMVE = 0 := by
      have := kv d (by omega) 7 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k11 : s.row (o + d) kPT = if 11 = ki then 1 else 0 := kv d (by omega) 11 (by omega)
    have hs1 := hoh.sum
    have hcp : s.row (o + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rcases hS with h | h | h
      · rw [cpHPL hok (rowLt hw hs _) hs1 h, k1, k2, k11]; rcases hkd with rfl | rfl <;> rfl
      · rw [cpHPF hok (rowLt hw hs _) hs1 h, k1, k2, k11]; rcases hkd with rfl | rfl <;> rfl
      · -- a `PT` part has no key rows
        rcases hkd with rfl | rfl
        · rw [cpKEY hok (rowLt hw hs _) hs1 h, k1, k2, k6, k7]; rfl
        · exfalso
          have H := head_PT ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
          have : q = 1 := by rw [← hqq]; exact H.2.2.2.2.2.1
          have := hK6 h
          omega
    have hbm : s.row (o + d) sBM = 0 := by rcases hS with h | h | h <;> omega
    have hch : s.row (o + d) sCH = 0 := by rcases hS with h | h | h <;> omega
    have hrd : s.row (o + d) rd = 1 := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) (K.qb d (by omega)) hcp hoh
      (fun h => by rcases hS with h' | h' | h' <;> omega) (fun _ => ⟨k6, k7⟩)
      (fun h => by rcases hS with h' | h' | h' <;> omega) (fun h => by omega)
      (rdcOff hok (rowLt hw hs _) (nextLt hw hs _) hch)
    refine ⟨hcp, hrd, hbm, ?_, K.pc d (by omega) sN (by decide)⟩
    rw [dirRow hok (rowLt hw hs _) (nextLt hw hs _) (K.ix d (by omega)) (by omega) hrd]
    exact (U.rows d (by omega)).2.1
  -- the source bytes
  have hlenE : (nodeEnc (.ext key c m)).length = 45 + (NearSpec.hexPrefix key false).length := by
    simp [nodeEnc, u32_length, u64_length, hc32]; omega
  have hPlen : (Pb (s.row o sN)).length = 45 + (NearSpec.hexPrefix key false).length := by
    rw [hsrc, List.length_map, hlenE]
  have cH := copyRun hw hs Pb hR (r := o + 1) (n := 4) (δ := 1) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (1 + d) (by omega) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  have hP1 : ((Pb (s.row o sN)).drop 1).take 4 = (NearSpec.u32 (NearSpec.hexPrefix key false).length).map UInt8.toNat := by
    rw [hsrc]; simp [nodeEnc, List.take_append_of_le_length, u32_length]
  rw [hP1, eH] at cH
  have hqhp : (NearSpec.hexPrefix key false).length = q :=
    u32_eq_full (by have := hlenE; omega) hq32 cH.symm
  have cK := copyRun hw hs Pb hR (r := o + 5) (n := q) (δ := 5) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (5 + d) (by omega) (by omega); rwa [show o + (5 + d) = o + 5 + d by omega] at this)
  have hP5 : ((Pb (s.row o sN)).drop 5).take q = (NearSpec.hexPrefix key false).map UInt8.toNat := by
    rw [hsrc, ← hqhp]; simp [nodeEnc, u32_length, List.take_append_of_le_length]
  rw [hP5] at cK
  -- CH (fresh: the part below's digest)
  have FC := kField hw hs hsc K U3 s3 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + 5 + q + d) sCH = 1 ∧ s.row (o + 5 + q + d) wfr = 1 ∧
      s.row (o + 5 + q + d) wn = 0 := by
    intro d hd
    have F := FC d hd
    have h7 := (stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1
    have hI := F.2.2.2.1
    have k1 : s.row (o + 5 + q + d) kRDE = if 1 = ki then 1 else 0 := hI.kd 1 (by omega)
    have k5 : s.row (o + 5 + q + d) kRBI = 0 := by have := hI.kd 5 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k9 : s.row (o + 5 + q + d) kWEX = 0 := by have := hI.kd 9 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k10 : s.row (o + 5 + q + d) kSPB = 0 := by have := hI.kd 10 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k11 : s.row (o + 5 + q + d) kPT = if 11 = ki then 1 else 0 := hI.kd 11 (by omega)
    have := chUp (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) h7 k5 k10
      (by rw [k1, k9, k11]; rcases hkd with rfl | rfl <;> rfl)
    exact ⟨h7, this⟩
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
    have k0 : s.row o kRDB = 0 := by have := I0.kd 0 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k1 : s.row o kRDE = if 1 = ki then 1 else 0 := I0.kd 1 (by omega)
    have k9 : s.row o kWEX = 0 := by have := I0.kd 9 (by omega); rcases hkd with rfl | rfl <;> exact this
    have k11 : s.row o kPT = if 11 = ki then 1 else 0 := I0.kd 11 (by omega)
    rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by rw [k0, k1, k9, k11]; rcases hkd with rfl | rfl <;> rfl)
      (by omega), hj]
    omega
  have hdI := dIj_nat (rowLt hw hs _ _) (dCHm (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0.1 c0.2.2)
  have hdL := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (dCHml (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0.1 c0.2.2)
  rw [hsc _ hr3 tau (by decide), show s.row (o + 5 + q) jm = s.row o jm by
    have := K.pc (5 + q) (by omega) jm (by decide); rwa [show o + (5 + q) = o + 5 + q by omega] at this, hjm] at hdI
  rw [show s.row (o + 5 + q) clen = s.row o clen by
    have := K.pc (5 + q) (by omega) clen (by decide); rwa [show o + (5 + q) = o + 5 + q by omega] at this] at hdL
  exact ⟨_, hr3, hgD, hdI, hdL⟩

/-- **`RDE`**: `nodeEnc (qRDE k m c' cm)`. -/
theorem ups_rdeBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 1)
    (Pb : Nat → List Nat) (key : List Nat) (c c' : NearSpec.PTrie) (m cm : Nat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.ext key c m)).map UInt8.toNat)
    (hsl : (nodeEnc (.ext key c m)).length < 2 ^ 32) (hc32 : c.hashOf.length = 32) (hm : m < 2 ^ 64)
    (hdC : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = s.row ps[k].1 clen → regN (s.row i) = c'.hashOf.map UInt8.toNat)
    (hMd : ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv < 67108864 ∧ s.row (ps[k].1 + ps[k].2 - 8 + i) mCv < 67108864)
    (hmB : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mBv) 8 = c'.memD)
    (hmC : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mCv) 8 = cm)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRDE key m c' cm)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRDE key m c' cm).memD :=
  ups_extUpBytes hw hs hL hP k hk (Or.inl hkd) Pb key c c' m cm hR hsrc hsl hc32 hm hdC hMd hmB hmC hbyte

/-- **`PT`**: `nodeEnc (qPT m c' cm)` (the source is `.ext [] c m`). -/
theorem ups_ptBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 11)
    (Pb : Nat → List Nat) (c c' : NearSpec.PTrie) (m cm : Nat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.ext [] c m)).map UInt8.toNat)
    (hsl : (nodeEnc (.ext [] c m)).length < 2 ^ 32) (hc32 : c.hashOf.length = 32) (hm : m < 2 ^ 64)
    (hdC : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = s.row ps[k].1 clen → regN (s.row i) = c'.hashOf.map UInt8.toNat)
    (hMd : ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv < 67108864 ∧ s.row (ps[k].1 + ps[k].2 - 8 + i) mCv < 67108864)
    (hmB : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mBv) 8 = c'.memD)
    (hmC : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mCv) 8 = cm)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qPT m c' cm)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qPT m c' cm).memD :=
  ups_extUpBytes hw hs hL hP k hk (Or.inr hkd) Pb [] c c' m cm hR hsrc hsl hc32 hm hdC hMd hmB hmC hbyte

end

end ZkFormal.NearV3.UpsRows

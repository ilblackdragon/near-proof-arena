import ZkFormal.NearV3.Extract.Ups.Shapes

/-!
# ZkFormal.NearV3.Extract.Ups.RlpBytes — the present-leaf part `RLP` is `nodeEnc (qRLP k v)` (layer 2)

A part of kind `RLP` (kind index 2) rewrites the value of the terminal leaf `.leaf k s m`: its
`TAG HPL HPF [KEY]` bytes are copied from the source record (`UPB` reads at `spos = qpos`), the
value slot is fresh (`L0 L1 L2 0`, the value digest) and `memory_usage = 100 + 2·|hp(k)| + L`.

Hypotheses (from other tables): `Pb n` = the post bytes of record `n` (`hR`: every `UPB` read
returns the byte of its record at its position; `hsrc`: the part's source record is
`nodeEnc (.leaf k s m)`, which is shorter than `2^32`); the value `val`, its length `L` and
digest as for `NLF`; the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem leN_length : ∀ n x, (NearSpec.leN n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [NearSpec.leN, leN_length n]

theorem u32_length (x : Nat) : (NearSpec.u32 x).length = 4 := leN_length 4 x
theorem u64_length (x : Nat) : (NearSpec.u64 x).length = 8 := leN_length 8 x

/-- `u32 x` as `[q, 0, 0, 0]` pins `x` when `x < 2^32`. -/
theorem u32_eq {x q : Nat} (hx : x < 2 ^ 32) (h : (NearSpec.u32 x).map UInt8.toNat = [q, 0, 0, 0]) : x = q := by
  rw [toNats_u32] at h
  simp only [List.cons.injEq, and_true] at h
  omega

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- Direct copies (`RDB RDE RLP RBR PT`) read at their own position. -/
theorem dirRow {ci ti di si ki sdi : Nat} (hI : IxOf C ci ti di si ki sdi)
    (hki : ki = 0 ∨ ki = 1 ∨ ki = 2 ∨ ki = 3 ∨ ki = 11) (hrd : C rd = 1) : C spos = C qpos := by
  have f := pDir ok hC hrd
  have k0 : C kRDB = if 0 = ki then 1 else 0 := hI.kd 0 (by omega)
  have k1 : C kRDE = if 1 = ki then 1 else 0 := hI.kd 1 (by omega)
  have k2 : C kRLP = if 2 = ki then 1 else 0 := hI.kd 2 (by omega)
  have k3 : C kRBR = if 3 = ki then 1 else 0 := hI.kd 3 (by omega)
  have k11 : C kPT = if 11 = ki then 1 else 0 := hI.kd 11 (by omega)
  have hsum : ((C kRDB : Nat) : Fp) + ((C kRDE : Nat) : Fp) + ((C kRLP : Nat) : Fp) + ((C kRBR : Nat) : Fp) +
      ((C kPT : Nat) : Fp) = 1 := by
    rw [k0, k1, k2, k3, k11]
    rcases hki with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hsum] at f
  exact natv (hC _) (hC _) (by grind)

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The present-leaf part** (`RLP`): its bytes are `nodeEnc (qRLP k val)`. -/
theorem ups_rlpBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 2) (val : NearSpec.Bytes)
    (Pb : Nat → List Nat) (key : List Nat) (sl : NearSpec.Slot) (m : Nat)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hdig : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 0 →
      s.row i dL = val.length → regN (s.row i) = (NearSpec.sha256 val).map UInt8.toNat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.leaf key sl m)).map UInt8.toNat)
    (hsl : (nodeEnc (.leaf key sl m)).length < 2 ^ 32)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRLP key val)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRLP key val).memD := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hsrc ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  obtain ⟨hx0, hv0, htl, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_RLP (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead (okRow hw hs hlt0) (rowLt hw hs _) K.pf hq0
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U4, s4⟩, ⟨U5, s5⟩⟩ := leafShape hw hs U htl hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U4 s4 U5 s5 hKc
  subst hℓ
  have hle := K.le
  -- TAG
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 0 by omega] at eT
  -- HPL (grammar)
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1 + d) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  rw [show s.row (o + 1) qhk = q by rw [← hqq]; exact K.pc 1 (by omega) qhk (by decide)] at eH
  have hq256 : q < 256 := by
    have := hbyte 1 (by omega); rw [rowsB_four] at eH; simp only [List.cons.injEq] at eH; omega
  -- the copied rows: `HPL HPF [KEY]` (rows `o+1 … o+4+q`)
  have kv := fun d (hd : d < 49 + q) m (hm : m < 12) => (K.ix d hd).kd m hm
  have copyAt : ∀ d, 1 ≤ d → d < 5 + q → s.row (o + d) cp = 1 ∧ s.row (o + d) rd = 1 ∧ s.row (o + d) sBM = 0 ∧
      s.row (o + d) spos = d ∧ s.row (o + d) sN = s.row o sN := by
    intro d h1 h2
    have hlt : o + d < s.rows.length := by omega
    -- the row's state: HPL, HPF or KEY
    have hst : OneHot (s.row (o + d)) ∧ (s.row (o + d) sHPL = 1 ∨ s.row (o + d) sHPF = 1 ∨ s.row (o + d) sKEY = 1) := by
      rcases Nat.lt_or_ge d 5 with h | h
      · have F := kField hw hs hsc K U1 s1 (by omega) (by omega) (d - 1) (by omega)
        rw [show o + 1 + (d - 1) = o + d by omega] at F
        exact ⟨F.1, Or.inl ((stOf_inv F.1).2.1 F.2.1)⟩
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · subst h'
          have F := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
          simp only [Nat.add_zero] at F
          exact ⟨F.1, Or.inr (Or.inl ((stOf_inv F.1).2.2.1 F.2.1))⟩
        · have hk1 := KR.key (by omega)
          have F := kField hw hs hsc K hk1.1 hk1.2 (by omega) (by omega) (d - 6) (by omega)
          rw [show o + 5 + 1 + (d - 6) = o + d by omega] at F
          exact ⟨F.1, Or.inr (Or.inr ((stOf_inv F.1).2.2.2.1 F.2.1))⟩
    obtain ⟨hoh, hS⟩ := hst
    have hok := okRow hw hs hlt
    have k2 : s.row (o + d) kRLP = 1 := kv d (by omega) 2 (by omega)
    have k1 : s.row (o + d) kRDE = 0 := kv d (by omega) 1 (by omega)
    have k6 : s.row (o + d) kMVL = 0 := kv d (by omega) 6 (by omega)
    have k7 : s.row (o + d) kMVE = 0 := kv d (by omega) 7 (by omega)
    have k11 : s.row (o + d) kPT = 0 := kv d (by omega) 11 (by omega)
    have hcp : s.row (o + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      have hs1 := hoh.sum
      rcases hS with h | h | h
      · rw [cpHPL hok (rowLt hw hs _) hs1 h, k1, k2, k11]; rfl
      · rw [cpHPF hok (rowLt hw hs _) hs1 h, k1, k2, k11]; rfl
      · rw [cpKEY hok (rowLt hw hs _) hs1 h, k1, k2, k6, k7]; rfl
    have hs1 := hoh.sum
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
  have hlenE : (nodeEnc (.leaf key sl m)).length = 13 + (NearSpec.hexPrefix key true).length +
      (sl.valueRef).length := by
    simp [nodeEnc, u32_length, u64_length]; omega
  have hPlen : (Pb (s.row o sN)).length = 13 + (NearSpec.hexPrefix key true).length + (sl.valueRef).length := by
    rw [hsrc, List.length_map, hlenE]
  have cH := copyRun hw hs Pb hR (r := o + 1) (n := 4) (δ := 1) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (1 + d) (by omega) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  have hP1 : ((Pb (s.row o sN)).drop 1).take 4 = (NearSpec.u32 (NearSpec.hexPrefix key true).length).map UInt8.toNat := by
    rw [hsrc]; simp [nodeEnc, List.take_append_of_le_length, u32_length]
  rw [hP1, eH] at cH
  have hqhp : (NearSpec.hexPrefix key true).length = q :=
    u32_eq (by have := hlenE; omega) cH.symm
  have cK := copyRun hw hs Pb hR (r := o + 5) (n := q) (δ := 5) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (5 + d) (by omega) (by omega); rwa [show o + (5 + d) = o + 5 + d by omega] at this)
  have hP5 : ((Pb (s.row o sN)).drop 5).take q = (NearSpec.hexPrefix key true).map UInt8.toNat := by
    rw [hsrc, ← hqhp]; simp [nodeEnc, u32_length, List.take_append_of_le_length]
  rw [hP5] at cK
  -- VLEN, VH (fresh)
  have hvz : vcpV ci 2 = 0 := by simp [vcpV, kdOf, UKind.all, b2n]
  have eV := vlenFresh hw hs hsc K U3 s3 (by omega) (by omega) hvz
  have eV' := eV
  rw [rowsB_four] at eV'
  simp only [List.cons.injEq, and_true] at eV'
  obtain ⟨v0, v1, v2, -⟩ := eV'
  have hL0 : s.row 0 L0 < 256 := by
    rw [← v0]; have := hbyte (5 + q) (by omega); rwa [show o + (5 + q) = o + 5 + q by omega] at this
  have hL1 : s.row 0 L1 < 256 := by
    rw [← v1]; have := hbyte (6 + q) (by omega); rwa [show o + (6 + q) = o + 5 + q + 1 by omega] at this
  have hL2 : s.row 0 L2 < 256 := by
    rw [← v2]; have := hbyte (7 + q) (by omega); rwa [show o + (7 + q) = o + 5 + q + 2 by omega] at this
  obtain ⟨eW, hgD, hdI, hdL⟩ := vhFresh hw hs hsc K U4 s4 (by omega) (by omega) hvz ⟨hL0, hL1, hL2⟩
  have hD := hdig (o + 9 + q) (by omega) hgD hdI (by rw [hdL, hlen])
  -- MEM
  have hb := fun x (hx : x ∈ partConst) => K.pc 0 K.pos x hx
  have R5 := memRegs hw hs hsc K U5 s5 (by omega) (by omega)
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (41 + q + i) (by omega) x hx; rwa [show o + (41 + q + i) = o + 41 + q + i by omega] at this
  have hKc' := hKc (by omega)
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U U5 s5 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hLb : bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i < 256 := by
        simp only [bAt, List.getD_eq_getElem?_getD]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i ≥ 3 by omega) with rfl | rfl | rfl | h
        · simpa using hL0
        · simpa using hL1
        · simpa using hL2
        · simp [List.getElem?_eq_none (show [s.row 0 L0, s.row 0 L1, s.row 0 L2].length ≤ i by simp; omega)]
      have hfs : s.row (o + 41 + q + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [inA, pc5 i hi useA (by decide), huA]
      · simp [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
      · simp [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc]
      · simp only [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc', heL, heS,
          (R5 i hi).2.1]
        rcases (show s.row (o + 41 + q + i) fs = 0 ∨ s.row (o + 41 + q + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · have := hbyte (41 + q + i) (by omega); rwa [show o + (41 + q + i) = o + 41 + q + i by omega] at this)
  simp only [hKc', heL, heS, huA, hbN, hbL, hcO, hcS, hCc] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + 41 + q) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    simp only [UpsSpec.qRLP, NearSpec.newLeaf, NearSpec.leafMem, NearSpec.PTrie.memD, NearSpec.PTrie.mem?,
      Option.getD_some, hqhp, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    omega
  -- assemble
  rw [hBy, eT, eH, cK, eV, eW, eM, hD]
  simp only [UpsSpec.qRLP, NearSpec.newLeaf, nodeEnc, NearSpec.Slot.valueRef, NearSpec.leafMem, List.map_append,
    List.map_cons, List.map_nil, toNats_u32, hqhp, List.append_assoc, List.cons_append, List.nil_append]
  have e1 : val.length % 256 = s.row 0 L0 := by omega
  have e2 : val.length / 256 % 256 = s.row 0 L1 := by omega
  have e3 : val.length / 65536 % 256 = s.row 0 L2 := by omega
  have e4 : val.length / 16777216 % 256 = 0 := by omega
  rw [e1, e2, e3, e4, show q % 256 = q by omega, show q / 256 % 256 = 0 by omega, show q / 65536 % 256 = 0 by omega,
    show q / 16777216 % 256 = 0 by omega]
  simp only [List.cons.injEq, true_and, List.append_cancel_left_eq]
  refine ⟨rfl, ?_⟩
  congr 2
  simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
  omega

end

end ZkFormal.NearV3.UpsRows

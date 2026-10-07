import ZkFormal.NearV3.Extract.Ups.PartBytes

/-!
# ZkFormal.NearV3.Extract.Ups.NlfBytes — the new-leaf part `NLF` is `nodeEnc (qNLF si v)` (layer 2)

A part of kind `NLF` (kind index 8) is 50 bytes: the fields `TAG HPL HPF VLEN VH MEM` of a leaf
with a one-byte hex prefix and no key bytes; tag `0`, `u32 1`, the flag byte `0x3f` (`ys = [15]`,
`t* = W1`) or `0x20` (`ys = []`), the fresh value length `L0 L1 L2 0`, the fresh value digest
(the `DIGEST` register of the `VH` field's first row, looked up at `(msgId 12 (512τ), L)`), and
`memory_usage = 102 + L` from the `MEM` chains.

Hypotheses (from other tables, in the link): the post value `val` has length `L` (`SPLEN`), the
`DIGEST` lookup of the value id at length `L` returns `sha256 val` (`hdig`; the value part's
`BYTES` are `SPOST`'s bytes of `val`), and the part's emitted bytes are `< 256` (`SHA`'s byte
range).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem ysOf_hp (si : Nat) (h : si < 3) :
    (NearSpec.hexPrefix (UpsSpec.ysOf si) true).map UInt8.toNat = [if si = 0 then 63 else 32] := by
  rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> decide

theorem ysOf_hpLen (si : Nat) (h : si < 3) : (NearSpec.hexPrefix (UpsSpec.ysOf si) true).length = 1 := by
  rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> decide

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- A row of a node part is not a walk row. -/
theorem qbWt3 {i : Nat} (hi : i < s.rows.length) (hq : s.row i qb = 1) : s.row i wt3 = 0 := by
  obtain ⟨bact, hact, hwk, -, -, -, bw3, -, -, bwk, -⟩ := kinds (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  rcases bact with h | h <;> rcases bw3 with h' | h' <;> omega

/-- `cp = 0` from its `Fp` provenance equation with a vanishing right-hand side. -/
theorem cpZero {i : Nat} (h : ((s.row i cp : Nat) : Fp) = ((0 : Nat) : Fp)) : s.row i cp = 0 :=
  natv (rowLt hw hs _ _) (by rw [P_lit]; omega) h

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The new-leaf part** (`NLF`): its 50 bytes are `nodeEnc (qNLF si val)`. -/
theorem ups_nlfBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 8) (val : NearSpec.Bytes)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hdig : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 0 →
      s.row i dL = val.length → regN (s.row i) = (NearSpec.sha256 val).map UInt8.toNat)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qNLF si val)).map UInt8.toNat := by
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  have hI := fun d hd => partIxRow hw hs hL hP k hk d hd
  have hSel := fun d hd => partSelAll hw hs hL hP k hk d hd
  obtain ⟨r0, hr0, hmrows, hmem⟩ := ups_mem hw hs hL k hk
  obtain ⟨-, U⟩ := hL.part k hk
  rw [hkd] at hI hSel
  generalize ps[k].1 = o at U hbyte hI hSel hr0 ⊢
  generalize ps[k].2 = ℓ at U hbyte hI hSel hr0 ⊢
  have hlt := U.le
  have hq : ∀ d, d < ℓ → s.row (o + d) qb = 1 := fun d hd => (U.rows d hd).1
  have hpc : ∀ d, d < ℓ → ∀ x ∈ partConst, s.row (o + d) x = s.row o x := fun d hd => (U.rows d hd).2.2.2.2
  have hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x := hL.segc
  have hpf : s.row o pf = 1 := by have := (U.rows 0 U.pos).2.2.1.2 rfl; simpa using this
  have hq0 : s.row o qb = 1 := by simpa using hq 0 U.pos
  have hI0 := hI 0 U.pos
  simp only [Nat.add_zero] at hI0
  have hx0 : s.row o xcp = 0 := by
    have := (hSel 0 U.pos).2.1; simp only [Nat.add_zero] at this; rw [this]; rfl
  have H := nlfHead (okRow hw hs (i := o) (by have := U.pos; omega)) (rowLt hw hs _) (nextLt hw hs _) hpf hI0.kd hx0
  obtain ⟨htl, hhk, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ := H
  obtain ⟨-, -, -, -, hsum, bnk, -, -⟩ := partHead (okRow hw hs (i := o) (by have := U.pos; omega)) (rowLt hw hs _) hpf hq0
  have hte : s.row o qte = 0 := by omega
  have hb1 : s.row o qtb1 = 0 := by omega
  have hb2 : s.row o qtb2 = 0 := by omega
  -- the field list
  obtain ⟨hFA, hBy⟩ := partFieldsAt U
  rw [htl, hhk] at hFA hBy
  have hnk : s.row o nokey = 1 := by
    rcases bnk with h | h
    · exfalso
      have := fieldsAt_len _ _ hFA (3, 0) (by simp [shapeU, h])
      omega
    · exact h
  simp only [shapeU, hnk, ite_true, List.nil_append, List.cons_append] at hFA hBy
  simp only [FieldsAt, fieldsB, List.append_nil] at hFA hBy
  obtain ⟨U0, s0, U1, s1, U2, s2, U3, s3, U4, s4, U5, s5, -⟩ := hFA
  have hℓ : ℓ = 50 := by
    have := congrArg List.length hBy
    simp [rowsB] at this; omega
  subst hℓ
  -- row facts on every row of the part
  have ok := fun d (hd : d < 50) => okRow hw hs (i := o + d) (by omega)
  have cL := fun d (hd : d < 50) => rowLt hw hs (o + d)
  have nL := fun d (hd : d < 50) => nextLt hw hs (o + d)
  have qd := fun d (hd : d < 50) => hq d hd
  -- TAG
  have eT := tagField hw hs U0 s0 (by omega) hq0 hpf
  rw [hb1, hb2, hte] at eT
  -- HPL
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by rw [show o + 1 + d = o + (1 + d) by omega]; exact qd _ (by omega))
  rw [show o+1+3=o+4 by omega, hpc 4 (by omega) qhk (by decide), hhk] at eH
  change rowsB s (o+1) 4=[1,0,0,0] at eH
  -- HPF
  have st2 := fieldRowSt hw hs U2 s2 (by omega) (fun d hd => by rw [show o + 1 + 4 + d = o + (5 + d) by omega]; exact qd _ (by omega)) 0 (by omega)
  simp only [show o + 1 + 4 = o + 5 by omega] at st2
  have hts : s.row (o + 5) ts1 = if si = 0 then 1 else 0 := by
    show s.row (o + 5) 31 = _
    have := (hI 5 (by omega)).ts 0 (by omega); simpa [eq_comm] using this
  have eF := nlfHpf (ok 5 (by omega)) (cL 5 (by omega)) (nL 5 (by omega)) ((stOf_inv st2.1).2.2.1 st2.2)
    (by show s.row (o + 5) 58 = 1; have := (hI 5 (by omega)).kd 8 (by omega); simpa [kcol] using this) (by rw [hts]; split <;> omega)
  -- VLEN (fresh)
  simp only [show o + 1 + 4 = o + 5 by omega, show o + 5 + 1 = o + 6 by omega, show o + 6 + 4 = o + 10 by omega,
    show o + 10 + 32 = o + 42 by omega] at U2 U3 U4 U5 s2 s3 s4 s5 hBy
  have st3 := fieldRowSt hw hs U3 s3 (by omega) (fun d hd => by rw [show o + 6 + d = o + (6 + d) by omega]; exact qd _ (by omega))
  have cpV : ∀ d, d < 4 → s.row (o + 6 + d) sVLEN = 1 ∧ s.row (o + 6 + d) cp = 0 := fun d hd => by
    have h1 := (stOf_inv (st3 d hd).1).2.2.2.2.1 (st3 d hd).2
    refine ⟨h1, cpZero hw hs ?_⟩
    have := cpVLEN (C := s.row (o + 6 + d)) (D := s.next (o + 6 + d)) (okRow hw hs (by omega)) (rowLt hw hs _)
      (st3 d hd).1.sum h1
    have hv := (hSel (6 + d) (by omega)).1
    rw [show o + (6 + d) = o + 6 + d by omega] at hv
    rw [this, hv]; rfl
  have fe3 : ∀ d, d < 3 → s.row (o + 6 + d) fe = 0 := fun d hd => by
    rcases rowBool (okRow hw hs (i := o + 6 + d) (by omega)) (rowLt hw hs _) (x := fe) (by decide) with h | h
    · exact h
    · have := (U3.fe d (by omega)).1 h; omega
  have eV := freshVlen hw hs (r0 := o + 6) (by omega) cpV (by simpa using (U3.fs 0 (by omega)).2 rfl) fe3
  rw [hsc (o + 6) (by omega) L0 (by decide), hsc (o + 6) (by omega) L1 (by decide),
    hsc (o + 6) (by omega) L2 (by decide)] at eV
  -- VH (fresh)
  have st4 := fieldRowSt hw hs U4 s4 (by omega) (fun d hd => by rw [show o + 10 + d = o + (10 + d) by omega]; exact qd _ (by omega))
  have cpH : ∀ d, d < 32 → (s.row (o + 10 + d) sVH = 1 ∧ s.row (o + 10 + d) cp = 0 ∧ s.row (o + 10 + d) sCH = 0) ∨
      (s.row (o + 10 + d) sCH = 1 ∧ s.row (o + 10 + d) wfr = 1 ∧ s.row (o + 10 + d) sVH = 0) := fun d hd => by
    have h1 := (stOf_inv (st4 d hd).1).2.2.2.2.2.1 (st4 d hd).2
    have hs1 := (st4 d hd).1.sum
    refine Or.inl ⟨h1, cpZero hw hs ?_, by omega⟩
    have := cpVH (C := s.row (o + 10 + d)) (D := s.next (o + 10 + d)) (okRow hw hs (by omega)) (rowLt hw hs _)
      (st4 d hd).1.sum h1
    have hv := (hSel (10 + d) (by omega)).1
    rw [show o + (10 + d) = o + 10 + d by omega] at hv
    rw [this, hv]; rfl
  have fe4 : ∀ d, d < 31 → s.row (o + 10 + d) fe = 0 := fun d hd => by
    rcases rowBool (okRow hw hs (i := o + 10 + d) (by omega)) (rowLt hw hs _) (x := fe) (by decide) with h | h
    · exact h
    · have := (U4.fe d (by omega)).1 h; omega
  have eW := freshWin hw hs (r0 := o + 10) (by omega) cpH fe4
  have hW0 := cpH 0 (by omega)
  simp only [Nat.add_zero] at hW0
  have hfs10 : s.row (o + 10) fs = 1 := by simpa using (U4.fs 0 (by omega)).2 rfl
  have hq10 : s.row (o + 10) qb = 1 := qd 10 (by omega)
  have hgD := gDrow (okRow hw hs (i := o + 10) (by omega)) (rowLt hw hs _) (nextLt hw hs _) hq10 hfs10
    (qbWt3 hw hs (by omega) hq10) hW0
  have hoh10 : OneHot (s.row (o + 10)) := by simpa using (st4 0 (by omega)).1
  have hvh10 : s.row (o + 10) sVH = 1 := by
    rcases hW0 with h | h
    · exact h.1
    · exact absurd h.2.2 (by have := (stOf_inv hoh10).2.2.2.2.2.1 (by simpa using (st4 0 (by omega)).2); omega)
  have hdI := dI_nat (rowLt hw hs _ _) (dVH (okRow hw hs (i := o + 10) (by omega)) (rowLt hw hs _) hoh10.sum hgD hvh10)
  have hdL := dVHl (okRow hw hs (i := o + 10) (by omega)) (rowLt hw hs _) hoh10.sum hgD hvh10
  -- L bytes are bytes
  have eV' := eV
  simp only [rowsB_four, List.cons.injEq, and_true] at eV'
  obtain ⟨v0, v1, v2, -⟩ := eV'
  have hL0 : s.row 0 L0 < 256 := by rw [← v0]; simpa using hbyte 6 (by omega)
  have hL1 : s.row 0 L1 < 256 := by rw [← v1]; simpa [Nat.add_assoc] using hbyte 7 (by omega)
  have hL2 : s.row 0 L2 < 256 := by rw [← v2]; simpa [Nat.add_assoc] using hbyte 8 (by omega)
  -- the value digest
  rw [hsc (o + 10) (by omega) tau (by decide)] at hdI
  rw [hsc (o + 10) (by omega) L0 (by decide), hsc (o + 10) (by omega) L1 (by decide),
    hsc (o + 10) (by omega) L2 (by decide)] at hdL
  have hdL' : s.row (o + 10) dL = val.length := by
    rw [hlen]
    apply natv (rowLt hw hs _ _) (by rw [P_lit]; omega)
    rw [hdL, natCast_add, natCast_add, natCast_mul, natCast_mul]
    grind
  have hD := hdig (o + 10) (by omega) hgD hdI hdL'
  -- MEM
  have hr0' : r0 = o + 42 := by omega
  subst hr0'
  have st5 := fieldRowSt hw hs U5 s5 (by omega) (fun d hd => by rw [show o + 42 + d = o + (42 + d) by omega]; exact qd _ (by omega))
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := hpc (42 + i) (by omega) x hx; rwa [show o + (42 + i) = o + 42 + i by omega] at this
  have fs5 : ∀ i, i < 8 → s.row (o + 42 + i) fs = if i = 0 then 1 else 0 := fun i hi => by
    split
    · next h => subst h; simpa using (U5.fs 0 (by omega)).2 rfl
    · next h => rcases rowBool (okRow hw hs (i := o + 42 + i) (by omega)) (rowLt hw hs _) (x := fs) (by decide) with h' | h'
                · exact h'
                · exact absurd ((U5.fs i hi).1 h') h
  have fe5 : ∀ i, i < 7 → s.row (o + 42 + i) fe = 0 := fun i hi => by
    rcases rowBool (okRow hw hs (i := o + 42 + i) (by omega)) (rowLt hw hs _) (x := fe) (by decide) with h | h
    · exact h
    · have := (U5.fe i (by omega)).1 h; omega
  have ML := fun i (hi : i < 8) => memLR (okRow hw hs (i := o + 42 + i) (by omega)) (rowLt hw hs _) (nextLt hw hs _)
    (hmrows i hi).1
  let Lv : Nat → Nat := fun j => [s.row 0 L0, s.row 0 L1, s.row 0 L2].getD j 0
  have hLR : ∀ i, i < 8 → s.row (o + 42 + i) (LR 0) = Lv i ∧ s.row (o + 42 + i) (LR 1) = Lv (i + 1) ∧
      s.row (o + 42 + i) (LR 2) = Lv (i + 2) := by
    intro i
    induction i with
    | zero =>
      intro _
      have := (ML 0 (by omega)).1 (by rw [fs5 0 (by omega)]; rfl)
      simp only [Nat.add_zero] at this ⊢
      rw [hsc (o + 42) (by omega) L0 (by decide), hsc (o + 42) (by omega) L1 (by decide),
        hsc (o + 42) (by omega) L2 (by decide)] at this
      exact this
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have := (ML i (by omega)).2 (fe5 i (by omega))
      rw [next_eq hw hs (by omega), show o + 42 + i + 1 = o + 42 + (i + 1) by omega] at this
      rw [this.1, this.2.1, this.2.2, ih'.2.1, ih'.2.2]
      refine ⟨rfl, rfl, ?_⟩
      simp only [Lv]
      rcases (show i + 3 ≥ 3 from by omega) with _
      simp [List.getD_eq_getElem?_getD, show ¬ (i + 1 + 2 < 3) by omega]
  have inA0 : ∀ i, i < 8 → inA (s.row (o + 42 + i)) = 0 := fun i hi => by
    simp [inA, pc5 i hi useA (by decide), huA]
  have inB0 : ∀ i, i < 8 → inB (s.row (o + 42 + i)) = 0 := fun i hi => by
    simp [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
  have inC0 : ∀ i, i < 8 → inC (s.row (o + 42 + i)) = 0 := fun i hi => by
    simp [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc]
  have inEv : ∀ i, i < 8 → inE (s.row (o + 42 + i)) = (if i = 0 then 102 else 0) + Lv i := fun i hi => by
    simp only [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc, heL, heS,
      fs5 i hi, (hLR i hi).1]
    split <;> simp
  have hLv : ∀ j, Lv j < 256 := fun j => by
    simp only [Lv]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j ≥ 3 by omega) with rfl | rfl | rfl | h
    · simpa using hL0
    · simpa using hL1
    · simpa using hL2
    · simp [List.getD_eq_getElem?_getD, show ¬ (j < 3) by omega]
  obtain ⟨hrx, -, hbx⟩ := hmem (fun i hi => by
    rw [inA0 i hi, inB0 i hi, inC0 i hi, inEv i hi]
    have := hLv i
    refine ⟨by omega, by omega, by omega, by split <;> omega, ?_⟩
    have := hbyte (42 + i) (by omega); rwa [show o + (42 + i) = o + 42 + i by omega] at this)
  have hA : limbs (fun i => inA (s.row (o + 42 + i))) 8 = 0 := by
    rw [limbs8]; simp only [inA0 _ (by decide : (0 : Nat) < 8), inA0 _ (by decide : (1 : Nat) < 8),
      inA0 _ (by decide : (2 : Nat) < 8), inA0 _ (by decide : (3 : Nat) < 8), inA0 _ (by decide : (4 : Nat) < 8),
      inA0 _ (by decide : (5 : Nat) < 8), inA0 _ (by decide : (6 : Nat) < 8), inA0 _ (by decide : (7 : Nat) < 8)]
  have hB : limbs (fun i => inB (s.row (o + 42 + i))) 8 = 0 := by
    rw [limbs8]; simp only [inB0 _ (by decide : (0 : Nat) < 8), inB0 _ (by decide : (1 : Nat) < 8),
      inB0 _ (by decide : (2 : Nat) < 8), inB0 _ (by decide : (3 : Nat) < 8), inB0 _ (by decide : (4 : Nat) < 8),
      inB0 _ (by decide : (5 : Nat) < 8), inB0 _ (by decide : (6 : Nat) < 8), inB0 _ (by decide : (7 : Nat) < 8)]
  have hE : limbs (fun i => inE (s.row (o + 42 + i))) 8 = 102 + val.length := by
    rw [limbs8]; simp only [inEv _ (by decide : (0 : Nat) < 8), inEv _ (by decide : (1 : Nat) < 8),
      inEv _ (by decide : (2 : Nat) < 8), inEv _ (by decide : (3 : Nat) < 8), inEv _ (by decide : (4 : Nat) < 8),
      inEv _ (by decide : (5 : Nat) < 8), inEv _ (by decide : (6 : Nat) < 8), inEv _ (by decide : (7 : Nat) < 8)]
    simp [Lv, hlen]; omega
  rw [hA, hB, hE] at hrx
  rw [hrx] at hbx
  have hM := u64_limbs (f := fun i => s.row (o + 42 + i) b) (fun i hi => by
    have := hbyte (42 + i) (by omega); rwa [show o + (42 + i) = o + 42 + i by omega] at this) (X := 102 + val.length)
    (by simpa using hbx)
  -- assemble
  rw [hBy, UpsSpec.qNLF_enc]
  simp only [List.map_append, toNats_u32, ysOf_hpLen si i4, ysOf_hp si i4]
  have hlm : NearSpec.leafMem (UpsSpec.ysOf si) val.length = 102 + val.length := by
    unfold NearSpec.leafMem; rw [ysOf_hpLen si i4]; omega
  rw [hlm, hM, eT, eH, rowsB_one, eF, hts, eV, eW]
  rw [show (List.range 32).map (fun i => s.row (o + 10) (reg i)) = regN (s.row (o + 10)) from rfl, hD]
  have e1 : val.length % 256 = s.row 0 L0 := by omega
  have e2 : val.length / 256 % 256 = s.row 0 L1 := by omega
  have e3 : val.length / 65536 % 256 = s.row 0 L2 := by omega
  have e4 : val.length / 16777216 % 256 = 0 := by omega
  rw [e1, e2, e3, e4]
  simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append, rowsB]
  split <;> simp

end

end ZkFormal.NearV3.UpsRows

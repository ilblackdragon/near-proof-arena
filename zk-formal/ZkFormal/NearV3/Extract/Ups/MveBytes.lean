import ZkFormal.NearV3.Extract.Ups.MvlBytes

/-!
# ZkFormal.NearV3.Extract.Ups.MveBytes — a moved extension, `MVE` (layer 2)

A part of kind `MVE` (index 7) is the old extension `.ext k c m` moved below a split at position
`I`: `.ext (k.drop (I+1)) c (extOwnMem (k.drop (I+1)) + (m − extOwnMem k))`.  As for `MVL`
(`MvlBytes`), its tag and hex-prefix length are fresh, its flag byte takes the low nibble read from
the source (`mvHpf`) and its key bytes are copied `δ = phk − qhk` bytes further on (`mvPos`,
`hp_drop`); its child window is copied the same `δ` further on (`chCopy`), and
`memory_usage = (50 + 2·qhk) + (m − (50 + 2·phk))` with `m` read from the source's last eight
bytes (`pMEM`).

Hypotheses: `UpbReads s Pb`; the source is `nodeEnc (.ext k c m)` (`< 2^20` bytes, nibbles `< 16`,
`I + 1 ≤ |k| < 400`, a 32-byte child hash, `m < 2^64`); the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

set_option maxHeartbeats 4000000 in
/-- **A moved extension** (`MVE`): its bytes are `nodeEnc (qMVE k c m ti)`. -/
theorem ups_mveBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 7)
    (Pb : Nat → List Nat) (key : List Nat) (c : NearSpec.PTrie) (m : Nat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.ext key c m)).map UInt8.toNat)
    (hsmall : (nodeEnc (.ext key c m)).length < 2 ^ 20) (hkey : ∀ x ∈ key, x < 16) (hI : ti + 1 ≤ key.length)
    (hklen : key.length < 400) (hc32 : c.hashOf.length = 32) (hm : m < 2 ^ 64)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qMVE key c m ti)).map UInt8.toNat := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  have hup := upZero hw hs hL hP k hk (by omega)
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hsrc hup ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, i2, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨hx0, hv0, hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_MVE ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U5, s5⟩⟩ := extShape hw hs U hte hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U5 s5 hKc
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  have htl : s.row o qtl = 0 := by omega
  have hpodd : s.row o podd ≤ 1 := partBoolN ok0 (rowLt hw hs _) K.pf (x := podd) (by decide)
  have hqodd : s.row o qodd ≤ 1 := partBoolN ok0 (rowLt hw hs _) K.pf (x := qodd) (by decide)
  have hkm : ∀ d, d < 45 + q → s.row (o + d) kMVL + s.row (o + d) kMVE = 1 := fun d hd => by
    rw [show s.row (o + d) kMVL = 0 from (K.ix d hd).kd 6 (by omega), show s.row (o + d) kMVE = 1 from (K.ix d hd).kd 7 (by omega)]
  -- the source
  let H := (NearSpec.hexPrefix key false).map UInt8.toNat
  have hHl : H.length = key.length / 2 + 1 := by simp [H, UpsSpec.hp_len]
  have hPb : Pb (s.row o sN) = [3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++
      (c.hashOf.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat))) := by
    rw [hsrc]; simp [nodeEnc, H]
  have hPlen : (Pb (s.row o sN)).length = 45 + H.length := by
    rw [hPb]; simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length, hc32,
      u64_length]; omega
  -- TAG: the source's flag byte
  have hT0 := kField hw hs hsc K U0 s0 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at hT0
  have htag1 : s.row o sTAG = 1 := (stOf_inv hT0.1).1 hT0.2.1
  have hcp0 : s.row o cp = 0 := cpZero hw hs (by
    rw [cpTAG ok0 (rowLt hw hs _) hT0.1.sum htag1, show s.row o kRDB = 0 from I0.kd 0 (by omega),
      show s.row o kRDE = 0 from I0.kd 1 (by omega), show s.row o kRLP = 0 from I0.kd 2 (by omega),
      show s.row o kRBR = 0 from I0.kd 3 (by omega), show s.row o kRBI = 0 from I0.kd 5 (by omega),
      show s.row o kPT = 0 from I0.kd 11 (by omega)]; rfl)
  have hrd0 := rdMv ok0 (rowLt hw hs _) (nextLt hw hs _) hq0 (by simpa using hkm 0 (by omega)) hT0.1 hcp0 hx0
    (I0.kd 4 (by omega)) (Or.inl htag1)
  have hsp0 : s.row o spos = 5 := by
    have f := pMT ok0 (rowLt hw hs _) hT0.1.sum hrd0 htag1
    rw [← natCast_add, show s.row o kMVL + s.row o kMVE = 1 by simpa using hkm 0 (by omega)] at f
    exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by rw [show (5 : Nat) = 5 from rfl]; grind)
  have hrb0 := (hR o hlt0 hrd0).1
  rw [hsp0] at hrb0
  obtain ⟨mt1, mt2⟩ := mvTag ok0 (rowLt hw hs _) (nextLt hw hs _) hT0.1 htag1 (by simpa using hkm 0 (by omega)) hx0
    (by omega) hpodd
  have hH0 : H.getD 0 0 = 16 * (key.length % 2) + (key.length % 2) * key.headD 0 := by
    simp only [H, UpsSpec.hp_eq]
    have h16 : key.headD 0 < 16 := by cases key with | nil => simp | cons a r => simpa using hkey a (by simp)
    rw [List.headD_eq_head?_getD] at h16 ⊢
    split
    · next h => simp [UpsSpec.lb, UpsSpec.toNat_u8]; rw [h]; omega
    · next h => simp [UpsSpec.lb, UpsSpec.toNat_u8]; rw [show key.length % 2 = 0 by omega]; simp
  have hrb0' : s.row o rb = H.getD 0 0 := by
    rw [hrb0, hPb]; simp only [List.getD_eq_getElem?_getD, List.singleton_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by simp [u32_length])]; simp only [List.length_map, u32_length, Nat.sub_self]
    rw [List.getElem?_append_left (by rw [hHl]; omega)]
  have hpo : s.row o podd = key.length % 2 := by
    have := rowLt hw hs o (reg 4); have h16 : key.headD 0 < 16 := by
      cases key with | nil => simp | cons a r => simpa using hkey a (by simp)
    have bt := nibBits ok0 (rowLt hw hs _) (nextLt hw hs _) (by have := hT0.1.sum; have := hT0.1.bs; omega)
    have := bt 0 (by omega); have := bt 1 (by omega); have := bt 2 (by omega); have := bt 3 (by omega)
    have := bt 4 (by omega); have := bt 5 (by omega); have := bt 6 (by omega); have := bt 7 (by omega)
    rw [hrb0', hH0] at mt2
    rw [htl] at mt1
    rcases Nat.mod_two_eq_zero_or_one key.length with h | h <;> rw [h] at mt2 ⊢ <;> omega
  -- HPL: the source's `hplen`
  have F1 := kField hw hs hsc K U1 s1 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at F1
  have hpl1 : s.row (o + 1) sHPL = 1 := (stOf_inv F1.1).2.1 F1.2.1
  have hfs1 : s.row (o + 1) fs = 1 := by simpa using (U1.fs 0 (by omega)).2 rfl
  have ok1 := okRow hw hs F1.2.2.1
  have hcp1 : s.row (o + 1) cp = 0 := cpZero hw hs (by
    rw [cpHPL ok1 (rowLt hw hs _) F1.1.sum hpl1, show s.row (o + 1) kRDE = 0 from F1.2.2.2.1.kd 1 (by omega),
      show s.row (o + 1) kRLP = 0 from F1.2.2.2.1.kd 2 (by omega), show s.row (o + 1) kPT = 0 from F1.2.2.2.1.kd 11 (by omega)]; rfl)
  have hrd1 := rdMv ok1 (rowLt hw hs _) (nextLt hw hs _) F1.2.2.2.2.2 (by simpa using hkm 1 (by omega)) F1.1 hcp1
    (by rw [F1.2.2.2.2.1 xcp (by decide), hx0]) (F1.2.2.2.1.kd 4 (by omega)) (Or.inr (Or.inr ⟨hpl1, hfs1⟩))
  have hsp1 : s.row (o + 1) spos = 1 := by
    have f := pMH ok1 (rowLt hw hs _) F1.1.sum hrd1 hpl1
    rw [← natCast_add, show s.row (o + 1) kMVL + s.row (o + 1) kMVE = 1 by simpa using hkm 1 (by omega)] at f
    exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (by grind)
  have hphk : s.row o phk = H.length := by
    have f := rHPL ok1 (rowLt hw hs _) F1.1.sum hpl1 hfs1
    rw [← natCast_add, show s.row (o + 1) kMVL + s.row (o + 1) kMVE = 1 by simpa using hkm 1 (by omega)] at f
    have e := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (show ((s.row (o + 1) rb : Nat) : Fp) = ((s.row (o + 1) phk : Nat) : Fp) by grind)
    rw [← F1.2.2.2.2.1 phk (by decide), ← e, (hR _ F1.2.2.1 hrd1).1, hsp1, F1.2.2.2.2.1 sN (by decide), hPb]
    simp [toNats_u32, List.getD_eq_getElem?_getD]; omega
  -- the new hex-prefix length
  have eH := hplField hw hs U1 s1 (by omega) (fun d hd => by
    have := K.qb (1 + d) (by omega); rwa [show o + (1 + d) = o + 1 + d by omega] at this)
  rw [show s.row (o + 1) qhk = q by rw [← hqq]; exact K.pc 1 (by omega) qhk (by decide)] at eH
  have hq256 : q < 256 := by
    have := hbyte 1 (by omega); rw [rowsB_four] at eH; simp only [List.cons.injEq] at eH; omega
  have hQ := mvQhk ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by simpa using hkm 0 (by omega)) (I := ti)
    (by rw [show s.row o ti1 = if 1 = ti then 1 else 0 from I0.ti 1 (by omega),
      show s.row o ti2 = if 2 = ti then 1 else 0 from I0.ti 2 (by omega)]; split <;> split <;> omega) (by omega)
    (by omega) (by omega) hqodd hpodd
  rw [hqq, hphk, hpo, hHl] at hQ
  -- the moved key
  let X := (NearSpec.hexPrefix (key.drop (ti + 1)) false).map UInt8.toNat
  have hXl : X.length = q := by simp [X, UpsSpec.hp_len]; omega
  have hqo : s.row o qodd = (key.length - (ti + 1)) % 2 := by omega
  obtain ⟨hd1, hd0⟩ := UpsSpec.hp_drop key false (ti + 1) hI hkey
  have hδ : H.length - q = key.length / 2 - (key.length - (ti + 1)) / 2 := by omega
  have hqH : q ≤ H.length := by omega
  -- HPF: the moved flag byte
  have F5 := kField hw hs hsc K KR.hpf.1 KR.hpf.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at F5
  have ok5 := okRow hw hs F5.2.2.1
  have hpf5 : s.row (o + 5) sHPF = 1 := (stOf_inv F5.1).2.2.1 F5.2.1
  have hcp5 : s.row (o + 5) cp = 0 := cpZero hw hs (by
    rw [cpHPF ok5 (rowLt hw hs _) F5.1.sum hpf5, show s.row (o + 5) kRDE = 0 from F5.2.2.2.1.kd 1 (by omega),
      show s.row (o + 5) kRLP = 0 from F5.2.2.2.1.kd 2 (by omega), show s.row (o + 5) kPT = 0 from F5.2.2.2.1.kd 11 (by omega)]; rfl)
  have hkm5 : s.row (o + 5) kMVL + s.row (o + 5) kMVE = 1 := hkm 5 (by omega)
  have hrd5 := rdMv ok5 (rowLt hw hs _) (nextLt hw hs _) F5.2.2.2.2.2 hkm5 F5.1 hcp5
    (by rw [F5.2.2.2.2.1 xcp (by decide), hx0]) (F5.2.2.2.1.kd 4 (by omega)) (Or.inr (Or.inl hpf5))
  have pc5 := F5.2.2.2.2.1
  have hsp5 : s.row (o + 5) spos = 5 + (H.length - q) := by
    rw [mvPos ok5 (rowLt hw hs _) (nextLt hw hs _) F5.1 hrd5 hkm5 (by have := F5.1.bs; have := F5.1.sum; omega)
      (by rw [pc5 qhk (by decide), pc5 phk (by decide), hqq, hphk, (U.rows 5 (by omega)).2.1]; omega)
      (by rw [pc5 phk (by decide), hphk, (U.rows 5 (by omega)).2.1, P_lit]; omega),
      pc5 qhk (by decide), pc5 phk (by decide), hqq, hphk, (U.rows 5 (by omega)).2.1]
    omega
  have hrb5 : s.row (o + 5) rb = H.getD (H.length - q) 0 := by
    rw [(hR _ F5.2.2.1 hrd5).1, hsp5, pc5 sN (by decide), hPb]
    simp only [List.getD_eq_getElem?_getD, List.singleton_append]
    rw [show 5 + (H.length - q) = (4 + (H.length - q)) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_right (by simp [u32_length])]
    simp only [List.length_map, u32_length, Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by omega)]
  obtain ⟨mh1, mh2⟩ := mvHpf ok5 (rowLt hw hs _) (nextLt hw hs _) F5.1 hpf5 hkm5
    (by rw [pc5 qtl (by decide), htl]; exact Nat.zero_le 1) (by rw [pc5 qodd (by decide)]; exact hqodd)
  have bt5 := nibBits ok5 (rowLt hw hs _) (nextLt hw hs _) (by have := F5.1.sum; have := F5.1.bs; omega)
  have := bt5 0 (by omega); have := bt5 1 (by omega); have := bt5 2 (by omega); have := bt5 3 (by omega)
  have := bt5 4 (by omega); have := bt5 5 (by omega); have := bt5 6 (by omega); have := bt5 7 (by omega)
  have hb5 : s.row (o + 5) b = X.getD 0 0 := by
    rw [mh2, pc5 qtl (by decide), pc5 qodd (by decide), htl, hd0, ← hδ, ← hrb5, mh1, hqo]
    simp only [UpsSpec.lb]
    rcases Nat.mod_two_eq_zero_or_one (key.length - (ti + 1)) with h | h <;> rw [h] <;> simp <;> omega
  -- KEY: copied `δ` bytes further on
  have keyR : rowsB s (o + 5) q = X := by
    rw [KR.bytes, rowsB_one, hb5]
    rcases Nat.lt_or_ge 1 q with hq1 | hq1
    · obtain ⟨UK, sK⟩ := KR.key hq1
      have cK := copyRun hw hs Pb (fun i hi hrd => (hR i hi hrd).1) (r := o + 5 + 1) (n := q - 1) (δ := 6 + (H.length - q))
        (N := s.row o sN) (by omega) (by rw [hPlen]; omega)
        (fun d hd => by
          have F := kField hw hs hsc K UK sK (by omega) (by omega) d hd
          have hk3 := (stOf_inv F.1).2.2.2.1 F.2.1
          have okd := okRow hw hs F.2.2.1
          have hcp : s.row (o + 5 + 1 + d) cp = 1 := by
            apply natv (rowLt hw hs _ _) one_lt
            rw [cpKEY okd (rowLt hw hs _) F.1.sum hk3, show s.row (o + 5 + 1 + d) kRDE = 0 from F.2.2.2.1.kd 1 (by omega),
              show s.row (o + 5 + 1 + d) kRLP = 0 from F.2.2.2.1.kd 2 (by omega),
              show s.row (o + 5 + 1 + d) kMVL = 0 from F.2.2.2.1.kd 6 (by omega),
              show s.row (o + 5 + 1 + d) kMVE = 1 from F.2.2.2.1.kd 7 (by omega)]; rfl
          have hb := F.1.bs; have hs1 := F.1.sum
          have hrd := rdCopy okd (rowLt hw hs _) (nextLt hw hs _) F.2.2.2.2.2 hcp F.1 (fun h => by omega)
            (fun h => by omega) (fun h => by omega) (fun h => by omega) (rdcOff okd (rowLt hw hs _) (nextLt hw hs _) (by omega))
          have pcd := F.2.2.2.2.1
          have hqp : s.row (o + 5 + 1 + d) qpos = 6 + d := by
            have := (U.rows (6 + d) (by omega)).2.1; rwa [show o + (6 + d) = o + 5 + 1 + d by omega] at this
          refine ⟨hcp, hrd, by omega, ?_, pcd sN (by decide)⟩
          rw [mvPos okd (rowLt hw hs _) (nextLt hw hs _) F.1 hrd (hkm (6 + d) (by omega) |> fun h => by
              rwa [show o + (6 + d) = o + 5 + 1 + d by omega] at h) (by have := F.1.bs; have := F.1.sum; omega)
            (by rw [pcd qhk (by decide), pcd phk (by decide), hqq, hphk, hqp]; omega)
            (by rw [pcd phk (by decide), hphk, hqp, P_lit]; omega),
            pcd qhk (by decide), pcd phk (by decide), hqq, hphk, hqp]
          omega)
      rw [cK, hPb]
      have e : ([3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++ (c.hashOf.map UInt8.toNat ++
          (NearSpec.u64 m).map UInt8.toNat)))).drop (6 + (H.length - q)) =
          H.drop (1 + (H.length - q)) ++ (c.hashOf.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) := by
        rw [show 6 + (H.length - q) = ([3] ++ (NearSpec.u32 H.length).map UInt8.toNat).length + (1 + (H.length - q)) by
          simp [u32_length]; omega, ← List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by simp),
          List.nil_append, Nat.add_sub_cancel_left, List.drop_append_of_le_length (by omega)]
      have hX1 : X.drop 1 = H.drop (1 + (H.length - q)) := by
        have := hd1; simp only [X, H] at this ⊢; rw [this, List.drop_drop, hδ]
      rw [e, List.take_left' (by simp; omega), ← hX1]
      exact headDrop X (by omega)
    · rw [show q - 1 = 0 by omega]
      simp only [rowsB, List.range_zero, List.map_nil, List.append_nil]
      have := headDrop X (by omega)
      rw [List.drop_eq_nil_of_le (by omega), List.append_nil] at this
      exact this
  -- CH: the child hash copied `δ` bytes further on
  have chRow : ∀ t, t < 32 → s.row (o + 5 + q + t) cp = 1 ∧ s.row (o + 5 + q + t) rd = 1 ∧
      s.row (o + 5 + q + t) sBM = 0 ∧ s.row (o + 5 + q + t) spos = 5 + H.length + t ∧
      s.row (o + 5 + q + t) sN = s.row o sN := by
    intro t ht
    obtain ⟨hoh, hst, hlt, hIx, hpc, hq⟩ := kField hw hs hsc K U3 s3 (by omega) (by omega) t ht
    have hch := (stOf_inv hoh).2.2.2.2.2.2.2.1 hst
    have okd := okRow hw hs hlt
    have hb := hoh.bs; have hs1 := hoh.sum
    have hcp : s.row (o + 5 + q + t) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rw [cpCH okd (rowLt hw hs _) hs1 hch, chCopy okd (rowLt hw hs _) (nextLt hw hs _) hch (by
        rw [show s.row (o + 5 + q + t) kRBR = 0 from hIx.kd 3 (by omega), show s.row (o + 5 + q + t) kRBV = 0 from hIx.kd 4 (by omega),
          show s.row (o + 5 + q + t) kMVE = 1 from hIx.kd 7 (by omega)])]; rfl
    have hrd := rdCopy okd (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh (fun h => by omega) (fun h => by omega)
      (fun h => by omega) (fun h => by omega) (rdcUp0 okd (rowLt hw hs _) (nextLt hw hs _) (by rw [hpc _ (by decide), hup]))
    have hqp : s.row (o + 5 + q + t) qpos = 5 + q + t := by
      have := (U.rows (5 + q + t) (by omega)).2.1; rwa [show o + (5 + q + t) = o + 5 + q + t by omega] at this
    refine ⟨hcp, hrd, by omega, ?_, hpc sN (by decide)⟩
    rw [mvPos okd (rowLt hw hs _) (nextLt hw hs _) hoh hrd (by
        rw [show s.row (o + 5 + q + t) kMVL = 0 from hIx.kd 6 (by omega), show s.row (o + 5 + q + t) kMVE = 1 from hIx.kd 7 (by omega)])
      (by omega) (by rw [hpc qhk (by decide), hpc phk (by decide), hqq, hphk, hqp]; omega)
      (by rw [hpc phk (by decide), hphk, hqp, P_lit]; omega),
      hpc qhk (by decide), hpc phk (by decide), hqq, hphk, hqp]
    omega
  have cW := copyRun hw hs Pb (fun i hi hrd => (hR i hi hrd).1) (r := o + 5 + q) (n := 32) (δ := 5 + H.length)
    (N := s.row o sN) (by omega) (by rw [hPlen]; omega) chRow
  have hCR : ((Pb (s.row o sN)).drop (5 + H.length)).take 32 = c.hashOf.map UInt8.toNat := by
    rw [hPb, show 5 + H.length = ([3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)).length by
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length]; omega]
    rw [show [3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++ (c.hashOf.map UInt8.toNat ++
      (NearSpec.u64 m).map UInt8.toNat))) = ([3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)) ++
      (c.hashOf.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) by simp, List.drop_left',
      List.take_left' (by simp [hc32])]
    all_goals rfl
  rw [hCR] at cW
  -- MEM: the old memory, read from the source's last eight bytes
  have R5 := memRegs hw hs hsc K U5 s5 (by omega) (by omega)
  have pcM := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (37 + q + i) (by omega) x hx; rwa [show o + (37 + q + i) = o + 37 + q + i by omega] at this
  have rbM : ∀ i, i < 8 → s.row (o + 37 + q + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
    intro i hi
    obtain ⟨hoh, hst, hlt, hIx, hpc, hq⟩ := kField hw hs hsc K U5 s5 (by omega) (by omega) i hi
    have hm8 := (stOf_inv hoh).2.2.2.2.2.2.2.2 hst
    have hrd := rdMem (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hq hm8 (hIx.kd 8 (by omega)) hoh
    obtain ⟨hrb, hpl⟩ := hR _ hlt hrd
    have hpM := pMEM (okRow hw hs hlt) (rowLt hw hs _) hoh.sum hrd hm8
    rw [U5.idx i hi, hpl, hpc sN (by decide), hPlen] at hpM
    have hsp : s.row (o + 37 + q + i) spos = 37 + H.length + i := by
      apply natv (rowLt hw hs _ _) (by rw [P_lit]; omega)
      have e : ((45 + H.length : Nat) : Fp) + ((i : Nat) : Fp) = ((37 + H.length + i : Nat) : Fp) + ((8 : Nat) : Fp) := by
        rw [← natCast_add, ← natCast_add, show 45 + H.length + i = 37 + H.length + i + 8 by omega]
      rw [e] at hpM
      grind
    rw [hrb, hsp, hpc sN (by decide), hPb]
    rw [show [3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++ (c.hashOf.map UInt8.toNat ++
      (NearSpec.u64 m).map UInt8.toNat))) = ([3] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++
      (H ++ c.hashOf.map UInt8.toNat))) ++ (NearSpec.u64 m).map UInt8.toNat by simp]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [u32_length, hc32]; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length, hc32]
    rw [show 37 + H.length + i - (0 + 1 + (4 + (H.length + 32))) = i by omega]
  have hA : limbs (fun i => s.row (o + 37 + q + i) rb) 8 = m := by
    rw [show limbs (fun i => s.row (o + 37 + q + i) rb) 8 =
        limbs (fun i => ((NearSpec.u64 m).map UInt8.toNat).getD i 0) 8 by
      simp only [limbs8]; rw [rbM 0 (by omega), rbM 1 (by omega), rbM 2 (by omega), rbM 3 (by omega),
        rbM 4 (by omega), rbM 5 (by omega), rbM 6 (by omega), rbM 7 (by omega)], limbs_u64]
    omega
  have hKc' := hKc (by omega)
  have hCc' := hCc (by rw [hphk]; omega)
  rw [hphk] at hCc'
  have eM := memBytesK hw hs hsc K U U5 s5 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + 37 + q + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [inA, pcM i hi useA (by decide), huA, Nat.one_mul, rbM i hi]
        have := toNats_lt (NearSpec.u64 m) i; omega
      · simp [inB, pcM i hi bN (by decide), pcM i hi bL (by decide), hbN, hbL]
      · simp only [inC, pcM i hi cO (by decide), pcM i hi cS (by decide), pcM i hi Cc (by decide), hcO, hcS, hCc']
        rcases (show s.row (o + 37 + q + i) fs = 0 ∨ s.row (o + 37 + q + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · simp only [inE, pcM i hi Kc (by decide), pcM i hi eL (by decide), pcM i hi eS (by decide), hKc', heL, heS]
        rcases (show s.row (o + 37 + q + i) fs = 0 ∨ s.row (o + 37 + q + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · have := hbyte (37 + q + i) (by omega); rwa [show o + (37 + q + i) = o + 37 + q + i by omega] at this)
  simp only [hKc', heL, heS, huA, hbN, hbL, hcO, hcS, hCc', hA] at eM
  -- assemble
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 3 by omega] at eT
  rw [hBy, eT, eH, keyR, cW, eM]
  simp only [UpsSpec.qMVE, nodeEnc, List.map_append, List.map_cons, List.map_nil, toNats_u32, List.append_assoc,
    List.cons_append, List.nil_append]
  have hXq : (NearSpec.hexPrefix (key.drop (ti + 1)) false).length = q := by simpa [X] using hXl
  rw [hXq, show q % 256 = q by omega, show q / 256 % 256 = 0 by omega, show q / 65536 % 256 = 0 by omega,
    show q / 16777216 % 256 = 0 by omega]
  have hHk : (NearSpec.hexPrefix key false).length = H.length := by simp [H]
  simp only [NearSpec.extOwnMem, hXq, hHk]
  simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add]
  rfl

end

end ZkFormal.NearV3.UpsRows

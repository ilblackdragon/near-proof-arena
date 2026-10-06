import ZkFormal.NearV3.Extract.Ups.MvRows

/-!
# ZkFormal.NearV3.Extract.Ups.MvlBytes — a moved leaf, `MVL` (layer 2)

A part of kind `MVL` (index 6) is the old leaf `.leaf k s m` moved below a split at position `I`:
`.leaf (k.drop (I+1)) s (leafMem (k.drop (I+1)) s.len)`.  Its tag and hex-prefix length are
fresh; its flag byte takes the low nibble read from the source (`mvHpf`); its key bytes and value
slot are copied `phk − qhk` bytes further on (`mvPos`, `hp_drop`); `memory_usage = 100 + 2·qhk + slen`
with the old length carried from the copied `VLEN` rows by `SR` (`srChain`).

Hypotheses: `UpbReads s Pb`; the source is `nodeEnc (.leaf k s m)` (`< 2^20` bytes, nibbles `< 16`,
`I + 1 ≤ |k|`, a 36-byte value slot, `s.len < 2^32`); the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

theorem headDrop (l : List Nat) (h : 0 < l.length) : [l.getD 0 0] ++ l.drop 1 = l := by
  cases l with
  | nil => simp at h
  | cons a r => simp

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A moved-key part reads on its `TAG`, `HPF` and first `HPL` rows. -/
theorem rdMv (hq : C qb = 1) (hk : C kMVL + C kMVE = 1) (hoh : OneHot C) (hcp : C cp = 0) (hx : C xcp = 0)
    (hkv : C kRBV = 0)
    (hst : C sTAG = 1 ∨ C sHPF = 1 ∨ (C sHPL = 1 ∧ C fs = 1)) : C rd = 1 := by
  have f := factN ok hC hD (e := .mul (c qb) (sub (c rd) (.add (c cp) (sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF)), c rdc])))) (memBytes (by simp [cBytes]))
  have hS := hoh.sum
  have hb := hoh.bs
  have := hC rd; have := hC kMVL; have := hC kMVE; have := hC kRBV
  simp only [P_lit] at *
  simp only [sumc, kM, List.map_cons, List.map_nil] at f
  nev_simp at f
  have hkm : (C kMVL + C kMVE) % 2013265921 = 1 := by omega
  rcases hst with h | h | ⟨h, h'⟩
  · have z : C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    have hrdc := rdcOff ok hC hD z.2.2.2.2.2.2.1
    simp [hq, h, hcp, hx, hrdc, hkv, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
      z.2.2.2.2.2.2.2] at f
    rw [hkm] at f
    omega
  · have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    have hrdc := rdcOff ok hC hD z.2.2.2.2.2.2.1
    simp [hq, h, hcp, hrdc, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
      z.2.2.2.2.2.2.2] at f
    rw [hkm] at f
    omega
  · have z : C sTAG = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    have hrdc := rdcOff ok hC hD z.2.2.2.2.2.2.1
    simp [hq, h, h', hcp, hrdc, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
      z.2.2.2.2.2.2.2] at f
    rw [hkm] at f
    omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **The old-length register at the `MEM` field**: the four bytes read on the `VLEN` rows. -/
theorem srChain {r r0 : Nat} (h1 : r + 4 ≤ r0) (hlt : r0 < s.rows.length)
    (hV : ∀ t, t < 4 → s.row (r + t) sVLEN = 1 ∧ s.row (r + t) rd = 1 ∧ OneHot (s.row (r + t)))
    (hmid : ∀ i, r + 4 ≤ i → i < r0 → s.row i qb = 1 ∧ s.row i pl = 0 ∧ s.row i sVLEN = 0 ∧ s.row i sMEM = 0) :
    ∀ j, j < 4 → s.row r0 (SR j) = s.row (r + j) rb := by
  have nx := fun i (hi : i + 1 < s.rows.length) => next_eq hw hs (i := i) hi
  have rot := fun t (ht : t < 4) => by
    have := srRot (okRow hw hs (i := r + t) (by omega)) (rowLt hw hs _) (nextLt hw hs _) (hV t ht).1
    rw [nx (r + t) (by omega), show r + t + 1 = r + (t + 1) by omega] at this
    exact this
  have r1 := rot 0 (by omega); have r2 := rot 1 (by omega); have r3 := rot 2 (by omega); have r4 := rot 3 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at r1 r2 r3 r4
  have rbS : ∀ t, t < 4 → s.row (r + t) rb = s.row r (SR t) := by
    intro t ht
    obtain ⟨hv, hrd, hoh⟩ := hV t ht
    have e := natv (rowLt hw hs _ _) (rowLt hw hs _ _)
      (rVLEN (okRow hw hs (i := r + t) (by omega)) (rowLt hw hs _) hoh.sum hrd hv)
    rw [e]
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
    · rfl
    · rw [r1.1]
    · rw [r2.1, r1.2.1]
    · rw [r3.1, r2.2.1, r1.2.2.1]
  have S4 : ∀ j, j < 4 → s.row (r + 4) (SR j) = s.row r (SR j) := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [r4.1, r3.2.1, r2.2.2.1, r1.2.2.2]
    · rw [r4.2.1, r3.2.2.1, r2.2.2.2, r1.1]
    · rw [r4.2.2.1, r3.2.2.2, r2.1, r1.2.1]
    · rw [r4.2.2.2, r3.1, r2.2.1, r1.2.2.1]
  have Sk : ∀ d, r + 4 + d ≤ r0 → ∀ j, j < 4 → s.row (r + 4 + d) (SR j) = s.row r (SR j) := by
    intro d
    induction d with
    | zero => intro _ j hj; exact S4 j hj
    | succ d ih =>
      intro hd j hj
      obtain ⟨hq, hpl, hv, hm⟩ := hmid (r + 4 + d) (by omega) (by omega)
      have := srConst (okRow hw hs (i := r + 4 + d) (by omega)) (rowLt hw hs _) (nextLt hw hs _) hq hpl hv hm j hj
      rw [nx _ (by omega)] at this
      rw [show r + 4 + (d + 1) = r + 4 + d + 1 by omega, this]; exact ih (by omega) j hj
  intro j hj
  rw [rbS j hj, show r0 = r + 4 + (r0 - (r + 4)) by omega]
  exact Sk _ (by omega) j hj

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

set_option maxHeartbeats 4000000 in
/-- **A moved leaf** (`MVL`): its bytes are `nodeEnc (qMVL k s ti)`. -/
theorem ups_mvlBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 6)
    (Pb : Nat → List Nat) (key : List Nat) (sl : NearSpec.Slot) (m : Nat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.leaf key sl m)).map UInt8.toNat)
    (hsmall : (nodeEnc (.leaf key sl m)).length < 2 ^ 22) (hkey : ∀ x ∈ key, x < 16) (hI : ti + 1 ≤ key.length)
    (hklen : key.length < 510) (hsl : sl.valueRef.length = 36) (hslen : sl.len < 2 ^ 32)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qMVL key sl ti)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qMVL key sl ti).memD := by
  have K := partK hw hs hL hP k hk
  obtain ⟨-, U⟩ := hL.part k hk
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hsrc ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, i2, -, i4, -, -⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨hx0, hv0, htl, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_MVL ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨hℓ, -, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, KR, ⟨U3, s3⟩, ⟨U4, s4⟩, ⟨U5, s5⟩⟩ := leafShape hw hs U htl hq0 K.pf
  generalize hqq : s.row o qhk = q at hℓ hBy KR U3 s3 U4 s4 U5 s5 hKc
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  obtain ⟨-, -, -, -, hsum, -, -, -⟩ := partHead ok0 (rowLt hw hs _) K.pf hq0
  have hpodd : s.row o podd ≤ 1 := partBoolN ok0 (rowLt hw hs _) K.pf (x := podd) (by decide)
  have hqodd : s.row o qodd ≤ 1 := partBoolN ok0 (rowLt hw hs _) K.pf (x := qodd) (by decide)
  have hkm : ∀ d, d < 49 + q → s.row (o + d) kMVL + s.row (o + d) kMVE = 1 := fun d hd => by
    rw [show s.row (o + d) kMVL = 1 from (K.ix d hd).kd 6 (by omega), show s.row (o + d) kMVE = 0 from (K.ix d hd).kd 7 (by omega)]
  -- the source
  let H := (NearSpec.hexPrefix key true).map UInt8.toNat
  have hHl : H.length = key.length / 2 + 1 := by simp [H, UpsSpec.hp_len]
  have hPb : Pb (s.row o sN) = [0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++
      (sl.valueRef.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat))) := by
    rw [hsrc]; simp [nodeEnc, H]
  have hsmall' : H.length < 256 := by omega
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
  -- `podd` is the source key's parity
  have hH0 : H.getD 0 0 = 32 + 16 * (key.length % 2) + (key.length % 2) * key.headD 0 := by
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
  let X := (NearSpec.hexPrefix (key.drop (ti + 1)) true).map UInt8.toNat
  have hXl : X.length = q := by simp [X, UpsSpec.hp_len]; omega
  have hqo : s.row o qodd = (key.length - (ti + 1)) % 2 := by omega
  obtain ⟨hd1, hd0⟩ := UpsSpec.hp_drop key true (ti + 1) hI hkey
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
    (by rw [pc5 qtl (by decide), htl]; exact Nat.le_refl 1) (by rw [pc5 qodd (by decide)]; exact hqodd)
  have bt5 := nibBits ok5 (rowLt hw hs _) (nextLt hw hs _) (by have := F5.1.sum; have := F5.1.bs; omega)
  have := bt5 0 (by omega); have := bt5 1 (by omega); have := bt5 2 (by omega); have := bt5 3 (by omega)
  have := bt5 4 (by omega); have := bt5 5 (by omega); have := bt5 6 (by omega); have := bt5 7 (by omega)
  have hb5 : s.row (o + 5) b = X.getD 0 0 := by
    rw [mh2, pc5 qtl (by decide), pc5 qodd (by decide), htl, hd0, ← hδ, ← hrb5, mh1, hqo]
    simp only [UpsSpec.lb, ite_true]
    rcases Nat.mod_two_eq_zero_or_one (key.length - (ti + 1)) with h | h <;> rw [h] <;> omega
  -- KEY: copied `δ` bytes further on
  have keyR : rowsB s (o + 5) q = X := by
    rw [KR.bytes, rowsB_one, hb5]
    rcases Nat.lt_or_ge 1 q with hq1 | hq1
    · obtain ⟨UK, sK⟩ := KR.key hq1
      have cK := copyRun hw hs Pb (fun i hi hrd => (hR i hi hrd).1) (r := o + 5 + 1) (n := q - 1) (δ := 6 + (H.length - q))
        (N := s.row o sN) (by omega) (by rw [hPb]; simp [u32_length]; omega)
        (fun d hd => by
          have F := kField hw hs hsc K UK sK (by omega) (by omega) d hd
          have hk3 := (stOf_inv F.1).2.2.2.1 F.2.1
          have okd := okRow hw hs F.2.2.1
          have hcp : s.row (o + 5 + 1 + d) cp = 1 := by
            apply natv (rowLt hw hs _ _) one_lt
            rw [cpKEY okd (rowLt hw hs _) F.1.sum hk3, show s.row (o + 5 + 1 + d) kRDE = 0 from F.2.2.2.1.kd 1 (by omega),
              show s.row (o + 5 + 1 + d) kRLP = 0 from F.2.2.2.1.kd 2 (by omega),
              show s.row (o + 5 + 1 + d) kMVL = 1 from F.2.2.2.1.kd 6 (by omega),
              show s.row (o + 5 + 1 + d) kMVE = 0 from F.2.2.2.1.kd 7 (by omega)]; rfl
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
      have e : ([0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++ (sl.valueRef.map UInt8.toNat ++
          (NearSpec.u64 m).map UInt8.toNat)))).drop (6 + (H.length - q)) =
          H.drop (1 + (H.length - q)) ++ (sl.valueRef.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) := by
        rw [show 6 + (H.length - q) = ([0] ++ (NearSpec.u32 H.length).map UInt8.toNat).length + (1 + (H.length - q)) by
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
  -- VLEN, VH: the value slot copied `δ` bytes further on
  have slotRow : ∀ t, t < 36 → s.row (o + 5 + q + t) cp = 1 ∧ s.row (o + 5 + q + t) rd = 1 ∧
      s.row (o + 5 + q + t) sBM = 0 ∧ s.row (o + 5 + q + t) spos = 5 + H.length + t ∧
      s.row (o + 5 + q + t) sN = s.row o sN ∧ OneHot (s.row (o + 5 + q + t)) ∧
      (t < 4 → s.row (o + 5 + q + t) sVLEN = 1) ∧ (4 ≤ t → s.row (o + 5 + q + t) sVH = 1) := by
    intro t ht
    obtain ⟨F, hst⟩ : (OneHot (s.row (o + 5 + q + t)) ∧ o + 5 + q + t < s.rows.length ∧
        IxOf (s.row (o + 5 + q + t)) ci ti di si 6 (sdx k) ∧ (∀ x ∈ partConst, s.row (o + 5 + q + t) x = s.row o x) ∧
        s.row (o + 5 + q + t) qb = 1) ∧ ((t < 4 → s.row (o + 5 + q + t) sVLEN = 1) ∧ (4 ≤ t → s.row (o + 5 + q + t) sVH = 1)) := by
      rcases Nat.lt_or_ge t 4 with h | h
      · have F := kField hw hs hsc K U3 s3 (by omega) (by omega) t h
        exact ⟨⟨F.1, F.2.2.1, F.2.2.2.1, F.2.2.2.2.1, F.2.2.2.2.2⟩, fun _ => (stOf_inv F.1).2.2.2.2.1 F.2.1, fun h' => by omega⟩
      · have F := kField hw hs hsc K U4 s4 (by omega) (by omega) (t - 4) (by omega)
        rw [show o + 9 + q + (t - 4) = o + 5 + q + t by omega] at F
        exact ⟨⟨F.1, F.2.2.1, F.2.2.2.1, F.2.2.2.2.1, F.2.2.2.2.2⟩, fun h' => by omega, fun _ => (stOf_inv F.1).2.2.2.2.2.1 F.2.1⟩
    obtain ⟨hoh, hlt, hI, hpc, hq⟩ := F
    have okd := okRow hw hs hlt
    have hb := hoh.bs; have hs1 := hoh.sum
    have hcp : s.row (o + 5 + q + t) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rcases Nat.lt_or_ge t 4 with h | h
      · rw [cpVLEN okd (rowLt hw hs _) hs1 (hst.1 h), hpc vcp (by decide), hv0]
      · rw [cpVH okd (rowLt hw hs _) hs1 (hst.2 h), hpc vcp (by decide), hv0]
    have hst' : s.row (o + 5 + q + t) sVLEN + s.row (o + 5 + q + t) sVH = 1 := by
      rcases Nat.lt_or_ge t 4 with h | h
      · have := hst.1 h; omega
      · have := hst.2 h; omega
    have hrd := rdCopy okd (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh (fun h => by omega) (fun h => by omega)
      (fun _ => hI.kd 3 (by omega)) (fun h => by omega) (rdcOff okd (rowLt hw hs _) (nextLt hw hs _) (by omega))
    have hqp : s.row (o + 5 + q + t) qpos = 5 + q + t := by
      have := (U.rows (5 + q + t) (by omega)).2.1; rwa [show o + (5 + q + t) = o + 5 + q + t by omega] at this
    refine ⟨hcp, hrd, by omega, ?_, hpc sN (by decide), hoh, hst.1, hst.2⟩
    rw [mvPos okd (rowLt hw hs _) (nextLt hw hs _) hoh hrd (by
        rw [show s.row (o + 5 + q + t) kMVL = 1 from hI.kd 6 (by omega), show s.row (o + 5 + q + t) kMVE = 0 from hI.kd 7 (by omega)])
      (by omega) (by rw [hpc qhk (by decide), hpc phk (by decide), hqq, hphk, hqp]; omega)
      (by rw [hpc phk (by decide), hphk, hqp, P_lit]; omega),
      hpc qhk (by decide), hpc phk (by decide), hqq, hphk, hqp]
    omega
  have cV := copyRun hw hs Pb (fun i hi hrd => (hR i hi hrd).1) (r := o + 5 + q) (n := 36) (δ := 5 + H.length)
    (N := s.row o sN) (by omega) (by
      rw [hPb]; simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length, hsl,
        u64_length]; omega)
    (fun t ht => ⟨(slotRow t ht).1, (slotRow t ht).2.1, (slotRow t ht).2.2.1, (slotRow t ht).2.2.2.1, (slotRow t ht).2.2.2.2.1⟩)
  have hVR : ((Pb (s.row o sN)).drop (5 + H.length)).take 36 = sl.valueRef.map UInt8.toNat := by
    rw [hPb, show 5 + H.length = ([0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)).length by
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, u32_length]; omega]
    rw [show [0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ (H ++ (sl.valueRef.map UInt8.toNat ++
      (NearSpec.u64 m).map UInt8.toNat))) = ([0] ++ ((NearSpec.u32 H.length).map UInt8.toNat ++ H)) ++
      (sl.valueRef.map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) by simp, List.drop_left',
      List.take_left' (by simp [hsl])]
    all_goals rfl
  rw [hVR] at cV
  -- the old length through `SR`
  have hSR := srChain hw hs (r := o + 5 + q) (r0 := o + 41 + q) (by omega) (by omega)
    (fun t ht => ⟨(slotRow t (by omega)).2.2.2.2.2.2.1 ht, (slotRow t (by omega)).2.1, (slotRow t (by omega)).2.2.2.2.2.1⟩)
    (fun i h1 h2 => by
      have F := kField hw hs hsc K U4 s4 (by omega) (by omega) (i - (o + 9 + q)) (by omega)
      rw [show o + 9 + q + (i - (o + 9 + q)) = i by omega] at F
      have hvh := (stOf_inv F.1).2.2.2.2.2.1 F.2.1
      have := F.1.bs; have := F.1.sum
      refine ⟨F.2.2.2.2.2, ?_, by omega, by omega⟩
      rcases plBool hw hs F.2.2.1 with h | h
      · exact h
      · have := ((U.rows (i - o) (by omega)).2.2.2.1).1 (by rwa [show o + (i - o) = i by omega]); omega)
  have hvr : (sl.valueRef.map UInt8.toNat).take 4 = (NearSpec.u32 sl.len).map UInt8.toNat := by
    cases sl <;> simp [NearSpec.Slot.valueRef, NearSpec.Slot.len, List.take_append_of_le_length, u32_length]
  have hSj : ∀ j, j < 4 → s.row (o + 41 + q) (SR j) = ((NearSpec.u32 sl.len).map UInt8.toNat).getD j 0 := by
    intro j hj
    obtain ⟨c1, -, c3, -, -, c6, -⟩ := slotRow j (by omega)
    rw [hSR j hj, ← bCopyN (okRow hw hs (i := o + 5 + q + j) (by omega)) (rowLt hw hs _) (nextLt hw hs _) c1 c3]
    have := congrArg (fun l => l.getD j 0) cV
    simp only [rowsB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < 36 by omega),
      Option.map_some, Option.getD_some] at this
    rw [this, ← hvr]
    simp [List.getElem?_take, hj]
  have hS : s.row (o + 41 + q) (SR 0) + 256 * s.row (o + 41 + q) (SR 1) + 65536 * s.row (o + 41 + q) (SR 2) +
      16777216 * s.row (o + 41 + q) (SR 3) = sl.len := by
    rw [hSj 0 (by omega), hSj 1 (by omega), hSj 2 (by omega), hSj 3 (by omega)]
    simp [toNats_u32]; omega
  have hSb : ∀ i, bAt [s.row (o + 41 + q) (SR 0), s.row (o + 41 + q) (SR 1), s.row (o + 41 + q) (SR 2),
      s.row (o + 41 + q) (SR 3)] i < 256 := by
    intro i
    simp only [bAt, List.getD_eq_getElem?_getD]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i ≥ 4 by omega) with rfl | rfl | rfl | rfl | h
    · simpa [hSj 0 (by omega)] using toNats_lt (NearSpec.u32 sl.len) 0
    · simpa [hSj 1 (by omega)] using toNats_lt (NearSpec.u32 sl.len) 1
    · simpa [hSj 2 (by omega)] using toNats_lt (NearSpec.u32 sl.len) 2
    · simpa [hSj 3 (by omega)] using toNats_lt (NearSpec.u32 sl.len) 3
    · simp [List.getElem?_eq_none (show [s.row (o + 41 + q) (SR 0), s.row (o + 41 + q) (SR 1),
        s.row (o + 41 + q) (SR 2), s.row (o + 41 + q) (SR 3)].length ≤ i by simp; omega)]
  -- MEM
  have R5 := memRegs hw hs hsc K U5 s5 (by omega) (by omega)
  have pc5' := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (41 + q + i) (by omega) x hx; rwa [show o + (41 + q + i) = o + 41 + q + i by omega] at this
  have hKc' := hKc (by omega)
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U U5 s5 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + 41 + q + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [inA, pc5' i hi useA (by decide), huA]
      · simp [inB, pc5' i hi bN (by decide), pc5' i hi bL (by decide), hbN, hbL]
      · simp [inC, pc5' i hi cO (by decide), pc5' i hi cS (by decide), pc5' i hi Cc (by decide), hcO, hcS, hCc]
      · simp only [inE, pc5' i hi Kc (by decide), pc5' i hi eL (by decide), pc5' i hi eS (by decide), hKc', heL, heS,
          (R5 i hi).2.2]
        have := hSb i
        rcases (show s.row (o + 41 + q + i) fs = 0 ∨ s.row (o + 41 + q + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · have := hbyte (41 + q + i) (by omega); rwa [show o + (41 + q + i) = o + 41 + q + i by omega] at this)
  simp only [hKc', heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hS] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + 41 + q) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    have hXq : (NearSpec.hexPrefix (key.drop (ti + 1)) true).length = q := by simpa [X] using hXl
    simp only [UpsSpec.qMVL, NearSpec.leafMem, hXq, NearSpec.PTrie.memD, NearSpec.PTrie.mem?, Option.getD_some, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    omega
  -- assemble
  have eT := tagField hw hs U0 s0 (by omega) hq0 K.pf
  rw [show s.row o qtb1 + 2 * s.row o qtb2 + 3 * s.row o qte = 0 by omega] at eT
  rw [hBy, eT, eH, keyR, ← List.append_assoc (rowsB s (o + 5 + q) 4),
    show o + 9 + q = o + 5 + q + 4 by omega, ← rowsB_append, show 4 + 32 = 36 from rfl, cV, eM]
  simp only [UpsSpec.qMVL, nodeEnc, List.map_append, List.map_cons, List.map_nil, toNats_u32, List.append_assoc,
    List.cons_append, List.nil_append]
  have hXq : (NearSpec.hexPrefix (key.drop (ti + 1)) true).length = q := by simpa [X] using hXl
  rw [hXq, show q % 256 = q by omega, show q / 256 % 256 = 0 by omega, show q / 65536 % 256 = 0 by omega,
    show q / 16777216 % 256 = 0 by omega]
  simp only [NearSpec.leafMem, hXq]
  rw [show 100 + 2 * q + 0 * (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) + 1 * sl.len +
      (0 * limbs (fun i => s.row (o + 41 + q + i) rb) 8 + (0 * limbs (fun i => s.row (o + 41 + q + i) mBv) 8 +
        0 * (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)) -
        (0 * limbs (fun i => s.row (o + 41 + q + i) mCv) 8 + 0 * sl.len + 0)) = 50 + 2 * q + (sl.len + 50) by omega]
  rfl

end

end ZkFormal.NearV3.UpsRows

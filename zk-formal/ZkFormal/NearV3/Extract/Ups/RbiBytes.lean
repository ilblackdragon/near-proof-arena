import ZkFormal.NearV3.Extract.Ups.RdbBytes

/-!
# ZkFormal.NearV3.Extract.Ups.RbiBytes — a new leaf inserted into a branch, `RBI` (layer 2)

A part of kind `RBI` (index 5) inserts the new leaf `qNLF si v` (the part below) into the empty
slot `y` (`0` when `t* = W1`, else `15`) of `.branch bv cs m`: the tag and value slot are copied, the
bitmap is copied with bit `y` added (`+1` on the low byte or `+128` on the high byte), the new
window (first or last) is the `DIGEST` of the part below at length 50, the other windows are
copied (32 bytes back after an inserted first window), and `memory_usage = 102 + L + m`.

Hypotheses: `si ≤ 1` (an absent branch slot is at a nibble terminal); `UpbReads s Pb`, the source is
`nodeEnc (.branch bv cs m)` (36-byte slot if any, `m < 2^64`, 16 slots, slot `y` empty); the `DIGEST`
of the part below at 50 is `(qNLF si val).hashOf`; `|val| = L` with `L`'s bytes `< 256`; the part's
bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsSpec

open NearSpec

theorem kidsBitmap_succ : ∀ (cs : Kids) (i : Nat), kidsBitmap cs (i + 1) = 2 * kidsBitmap cs i
  | .nil, _ => by simp [kidsBitmap]
  | .none r, i => by simp only [kidsBitmap]; exact kidsBitmap_succ r (i + 1)
  | .some _ r, i => by
    simp only [kidsBitmap]; rw [kidsBitmap_succ r (i + 1), Nat.pow_succ]; omega

theorem kidsBitmap_lt : ∀ (cs : Kids), kidsBitmap cs 0 < 2 ^ kidsLen cs
  | .nil => by simp [kidsBitmap, kidsLen]
  | .none r => by
    simp only [kidsBitmap, kidsLen, Nat.zero_add, kidsBitmap_succ r 0, Nat.pow_succ]
    have := kidsBitmap_lt r; omega
  | .some _ r => by
    simp only [kidsBitmap, kidsLen, Nat.zero_add, kidsBitmap_succ r 0, Nat.pow_succ, Nat.pow_zero]
    have := kidsBitmap_lt r; omega

theorem kidsBitmap_even (cs : Kids) (h : kidAt cs 0 = none) : kidsBitmap cs 0 % 2 = 0 := by
  cases cs with
  | nil => simp [kidsBitmap]
  | none r => simp only [kidsBitmap, Nat.zero_add, kidsBitmap_succ r 0]; omega
  | some _ r => simp [kidAt] at h

theorem kidsBitmap_lastFree : ∀ (cs : Kids) (n : Nat), kidsLen cs = n + 1 → kidAt cs n = none →
    kidsBitmap cs 0 < 2 ^ n
  | .nil, _, h, _ => by simp [kidsLen] at h
  | .some _ _, 0, _, h => by simp [kidAt] at h
  | .none r, 0, hl, _ => by
    simp only [kidsLen] at hl
    cases r with
    | nil => simp [kidsBitmap]
    | none _ => simp [kidsLen] at hl
    | some _ _ => simp [kidsLen] at hl
  | .none r, n + 1, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    simp only [kidsBitmap, Nat.zero_add, kidsBitmap_succ r 0, Nat.pow_succ]
    have := kidsBitmap_lastFree r n (by omega) h; omega
  | .some _ r, n + 1, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    simp only [kidsBitmap, Nat.zero_add, kidsBitmap_succ r 0, Nat.pow_succ, Nat.pow_zero]
    have := kidsBitmap_lastFree r n (by omega) h; omega

end ZkFormal.NearV3.UpsSpec

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The tag and value slot of a branch (before its bitmap). -/
def brTag (bv : Option NearSpec.Slot) : List Nat :=
  match bv with | none => [1] | some sl => [2] ++ sl.valueRef.map UInt8.toNat

theorem brPre_eq (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) :
    brPre bv cs = brTag bv ++ [NearSpec.kidsBitmap cs 0 % 256, NearSpec.kidsBitmap cs 0 / 256 % 256] := by
  cases bv <;> simp [brPre, brTag, NearSpec.u16, NearSpec.leN, toNat_u8, Nat.div_div_eq_div_mul]

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- A copied bitmap byte with the insertion bit. -/
theorem bCopyIns (hcp : C cp = 1) (hbm : C sBM = 1) {a : Nat}
    (ha : (C fs = 1 ∧ C ba0 = a) ∨ (C fs = 0 ∧ C ba1 = a)) (hlt : C rb + a < P) : C b = C rb + a := by
  have f := factN ok hC hD (e := .mul (c cp) (sub (c b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0))
    (.mul (not (c fs)) (c ba1))))))) (memBytes (by simp [cBytes]))
  have := hC b
  simp only [P_lit] at *
  nev_simp at f
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [hcp, hbm, h1, h2] at f <;> omega

/-- `RBI` reads `32·aft` bytes back. -/
theorem sposRBI (hrd : C rd = 1) (hk : C kRBI = 1) {a : Nat} (ha : C aft = a) (hq : 32 * a ≤ C qpos) :
    C spos = C qpos - 32 * a := by
  have f := pRBI ok hC hrd
  rw [hk, ha, cast1] at f
  exact sub_of_cast (hC _) (hC _) hq (by rw [natCast_mul]; grind)

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

set_option maxHeartbeats 4000000 in
/-- **A new leaf inserted into a branch** (`RBI`): its bytes are `nodeEnc (qRBI bv cs m si val)`. -/
theorem ups_rbiBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 5) (val : NearSpec.Bytes) (hsi : si ≤ 1)
    (Pb : Nat → List Nat) (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (m : Nat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.branch bv cs m)).map UInt8.toNat)
    (hsl : (nodeEnc (.branch bv cs m)).length < 2 ^ 20)
    (hbv : ∀ sl, bv = some sl → sl.valueRef.length = 36) (hm : m < 2 ^ 64)
    (hkl : UpsSpec.kidsLen cs = 16) (hslot : UpsSpec.kidAt cs (UpsSpec.yOf si) = none)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hLb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hdN : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = 50 → regN (s.row i) = (UpsSpec.qNLF si val).hashOf.map UInt8.toNat)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRBI bv cs m si val)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRBI bv cs m si val).memD := by
  have K := partK hw hs hL hP k hk
  have hup := upZero hw hs hL hP k hk (by omega)
  obtain ⟨hj, -⟩ := hL.part k hk
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  rw [hkd] at K
  generalize ps[k].1 = o at K U hbyte hsrc hup hdN hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, isd⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨hx0, hv0, htl, hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_RBI ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨c0, B⟩ := brLay hw hs hsc K U htl hte
  have hℓ := B.len
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  have hc0 : c0 = 3 ∨ c0 = 39 := by rcases B.c0v with h | h <;> omega
  have hts : s.row o ts1 = if si = 0 then 1 else 0 := by
    show s.row o 31 = _; have := I0.ts 0 (by omega); simpa [eq_comm] using this
  -- reads `32·aft` back
  have readAt : ∀ d a, d < c0 + 32 * ww + 8 → s.row (o + d) rd = 1 → s.row (o + d) aft = a → 32 * a ≤ d →
      s.row (o + d) rb = (Pb (s.row o sN)).getD (d - 32 * a) 0 ∧ s.row (o + d) plen = (Pb (s.row o sN)).length := by
    intro d a h2 hrd ha ha'
    have hlt : o + d < s.rows.length := by omega
    have hI := K.ix d h2
    have hsp := sposRBI (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hrd (hI.kd 5 (by omega)) ha
      (by rw [(U.rows d h2).2.1]; exact ha')
    rw [(U.rows d h2).2.1] at hsp
    have := hR (o + d) hlt hrd
    rwa [hsp, K.pc d h2 sN (by decide)] at this
  have aftAt : ∀ d, d < c0 + 32 * ww + 8 → s.row (o + d) sCH = 0 →
      s.row (o + d) aft = (if c0 + 32 * ww ≤ d then 1 else 0) := by
    intro d hd hch
    have hlt : o + d < s.rows.length := by omega
    have hoh := oneHot hw hs hlt (K.qb d hd)
    have A := (aftRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (K.ix d hd) (K.qb d hd) hoh.sum).2 rfl
    rcases Nat.lt_or_ge d c0 with h | h
    · obtain ⟨-, -, -, -, -, -, a7, a8, -⟩ := B.pre d h
      have := hoh.bs; have := hoh.sum
      rw [A.1 (by omega), if_neg (by omega)]
    · rcases Nat.lt_or_ge d (c0 + 32 * ww) with h' | h'
      · have := (B.win (d - c0) (by omega)).2.2.2.2.2; rw [show o + c0 + (d - c0) = o + d by omega] at this; omega
      · have F := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega) (d - (c0 + 32 * ww)) (by omega)
        rw [show o + c0 + 32 * ww + (d - (c0 + 32 * ww)) = o + d by omega] at F
        rw [A.2.2 ((stOf_inv F.1).2.2.2.2.2.2.2.2 F.2.1), if_pos h']
  -- MEM read: the source's length
  have hMEM0 := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at hMEM0
  have hm8 : s.row (o + c0 + 32 * ww) sMEM = 1 := (stOf_inv hMEM0.1).2.2.2.2.2.2.2.2 hMEM0.2.1
  have hrdM : s.row (o + (c0 + 32 * ww)) rd = 1 := by
    rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]
    exact rdMem (okRow hw hs hMEM0.2.2.1) (rowLt hw hs _) (nextLt hw hs _) hMEM0.2.2.2.2.2 hm8
      (hMEM0.2.2.2.1.kd 8 (by omega)) hMEM0.1
  have haM := aftAt (c0 + 32 * ww) (by omega) (by
    rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; have := hMEM0.1.bs; have := hMEM0.1.sum; omega)
  rw [if_pos (Nat.le_refl _)] at haM
  have hlenP : (Pb (s.row o sN)).length = (brPre bv cs).length + (NearSpec.Kids.hashes cs).length + 8 := by
    rw [hsrc, brEnc]; simp [u64_length]; omega
  obtain ⟨l1, l2⟩ := brPre_len bv cs hbv
  -- the tag: `bv` matches the layout
  have hT0 := B.pre 0 (by omega)
  simp only [Nat.add_zero] at hT0
  obtain ⟨t1, -, -, -, -, t6, -, -, t9, t10, -, -⟩ := hT0
  have htag1 : s.row o sTAG = 1 := t9.2 trivial
  have hcp0 : s.row o cp = 1 := by
    apply natv (rowLt hw hs _ _) one_lt
    rw [cpTAG ok0 (rowLt hw hs _) t1.sum htag1, show s.row o kRDB = 0 from I0.kd 0 (by omega),
      show s.row o kRDE = 0 from I0.kd 1 (by omega), show s.row o kRLP = 0 from I0.kd 2 (by omega),
      show s.row o kRBR = 0 from I0.kd 3 (by omega), show s.row o kRBI = 1 from I0.kd 5 (by omega),
      show s.row o kPT = 0 from I0.kd 11 (by omega)]; rfl
  have hrd0 : s.row o rd = 1 := rdCopy ok0 (rowLt hw hs _) (nextLt hw hs _) hq0 hcp0 t1
    (fun _ => ⟨I0.kd 4 (by omega), I0.kd 6 (by omega), I0.kd 7 (by omega), hx0⟩)
    (fun _ => ⟨I0.kd 6 (by omega), I0.kd 7 (by omega)⟩) (fun _ => I0.kd 3 (by omega)) (fun _ => hx0)
    (rdcOff ok0 (rowLt hw hs _) (nextLt hw hs _) t6)
  have hb0 := bCopyN ok0 (rowLt hw hs _) (nextLt hw hs _) hcp0 (by have := t1.bs; have := t1.sum; omega)
  have hgr0 := (gramRow ok0 (rowLt hw hs _) (nextLt hw hs _) t1.sum).1 htag1 K.pf
  have ha0 := aftAt 0 (by omega) (by simpa using t6)
  rw [if_neg (by omega)] at ha0
  have hr0 := (readAt 0 0 (by omega) (by simpa using hrd0) (by simpa using ha0) (by omega)).1
  simp only [Nat.add_zero] at hr0
  rw [hb0, hr0, hsrc, brEnc] at hgr0
  have hpreL : (brPre bv cs).length = c0 := by
    have : (brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat)).getD 0 0 =
        (brPre bv cs).getD 0 0 := by
      simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by rw [l1]; split <;> omega)]
    rw [this, l2] at hgr0
    rw [l1]
    rcases B.c0v with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> cases bv <;> simp at hgr0 ⊢ <;> omega
  clear hgr0 l2
  -- the source's length and the window count, from a `MEM` read (as naturals mod `P`)
  have hMr : (s.row (o + (c0 + 32 * ww)) spos + 32) % P = c0 + 32 * ww ∧
      (s.row (o + (c0 + 32 * ww)) spos + 8) % P = s.row (o + (c0 + 32 * ww)) plen % P := by
    have hlt : o + (c0 + 32 * ww) < s.rows.length := by omega
    have C1 := factN (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)
      (e := mul3 (c rd) (c kRBI) (sub (.add (c spos) (smul 32 (c aft))) (c qpos))) (memBytes (by simp [cBytes]))
    have C2 := factN (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)
      (e := mul3 (c rd) (c sMEM) (sub (.add (c spos) (Dsl.k 8)) (.add (c plen) (c idx)))) (memBytes (by simp [cBytes]))
    have hk5 : s.row (o + (c0 + 32 * ww)) kRBI = 1 := (K.ix (c0 + 32 * ww) (by omega)).kd 5 (by omega)
    have hq := (U.rows (c0 + 32 * ww) (by omega)).2.1
    have hidx : s.row (o + (c0 + 32 * ww)) idx = 0 := by
      have := B.memU.1.idx 0 (by omega); rwa [show o + c0 + 32 * ww + 0 = o + (c0 + 32 * ww) by omega] at this
    rw [show o + c0 + 32 * ww = o + (c0 + 32 * ww) by omega] at hm8
    have := rowLt hw hs (o + (c0 + 32 * ww)) spos; have := rowLt hw hs (o + (c0 + 32 * ww)) plen
    simp only [P_lit] at *
    nev_simp at C1 C2
    simp [hrdM, hk5, haM, hq, hm8, hidx] at C1 C2
    constructor <;> omega
  have hpl := (hR _ (by omega) hrdM).2
  rw [K.pc (c0 + 32 * ww) (by omega) sN (by decide)] at hpl
  have hww : 0 < ww ∧ (Pb (s.row o sN)).length = c0 + 32 * (ww - 1) + 8 := by
    have hPl : (Pb (s.row o sN)).length < 2 ^ 20 := by rw [hsrc, List.length_map]; exact hsl
    rw [hpl] at hMr
    have hlP := rowLt hw hs (o + (c0 + 32 * ww)) spos
    simp only [P_lit] at hMr hlP
    rcases B.c0v with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> rcases Nat.eq_zero_or_pos ww with h0 | h0
    · exfalso; subst h0; omega
    · omega
    · exfalso; subst h0
      have : (brPre bv cs).length ≥ 3 := by rw [l1]; split <;> omega
      omega
    · omega
  obtain ⟨hww, hPlen⟩ := hww
  have hHl : (NearSpec.Kids.hashes cs).length = 32 * (ww - 1) := by omega
  have hHl' : ((NearSpec.Kids.hashes cs).map UInt8.toNat).length = 32 * (ww - 1) := by simp [hHl]
  -- the windows: flags and roles
  have WF := winFlags hw hs (r := o + c0) hww (by omega) (by omega)
    (by have := (B.pre (c0 - 1) (by omega)).2.2.2.2.2.1; rwa [show o + (c0 - 1) = o + c0 - 1 by omega] at this)
    (fun e he => ⟨(B.winU e he).1, fun d hd => by
      have := (B.win (32 * e + d) (by omega)).2.2.2.2.2; rwa [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at this⟩)
    hm8 (by have := hMEM0.1.bs; have := hMEM0.1.sum; omega)
  obtain ⟨es, hesv⟩ : ∃ es, es = if si = 0 then 0 else ww - 1 := ⟨_, rfl⟩
  have hes : es < ww := by rw [hesv]; split <;> omega
  have role : ∀ e, e < ww → ∀ d, d < 32 → s.row (o + c0 + 32 * e + d) wfr = (if e = es then 1 else 0) ∧
      s.row (o + c0 + 32 * e + d) wn = (if e = es then 1 else 0) ∧ s.row (o + c0 + 32 * e + d) rdc = 0 ∧
      s.row (o + c0 + 32 * e + d) aft = (if si = 0 ∧ e ≠ 0 then 1 else 0) := by
    intro e he d hd
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * e + d) (by omega)
    rw [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at a1 a2 a3 a4 a5 a6
    have sl := kSel hw hs hsc K (r := o + c0 + 32 * e + d) (by omega) (by omega)
    have R := winRole (okRow hw hs a2) (rowLt hw hs _) (nextLt hw hs _) a3 i1 i4 (by omega) isd a6 sl.2.2.2.2.1
      sl.2.2.2.2.2 sl.2.1
    obtain ⟨f1, f2⟩ := WF e he d hd
    have hs15 : s15V 5 (sdx k) si = if si = 0 then 0 else 1 := by
      have : ∀ a, a < 3 → ∀ b, b < 3 → s15V 5 a b = if b = 0 then 0 else 1 := by decide
      exact this _ isd _ i4
    have ht : s.row (o + c0 + 32 * e + d) tgt = if e = es then 1 else 0 := by
      rw [R.1, f1, f2, hs15]
      by_cases h1 : si = 0
      · have : es = 0 := by rw [hesv, if_pos h1]
        rw [this, if_pos h1]
        by_cases h2 : e = 0 <;> simp [h2]
      · have : es = ww - 1 := by rw [hesv, if_neg h1]
        rw [this, if_neg h1, if_pos rfl]
        by_cases h2 : e + 1 = ww
        · rw [if_pos h2, if_pos (show e = ww - 1 by rw [← h2, Nat.add_sub_cancel])]
        · rw [if_neg h2, if_neg (show ¬ (e = ww - 1) from fun h => h2 (by rw [h]; exact Nat.sub_add_cancel hww))]
    have A := (aftRow (okRow hw hs a2) (rowLt hw hs _) (nextLt hw hs _) a3 a5 a1.sum).2 rfl
    refine ⟨by rw [R.2.1 (Or.inr rfl), ht], by rw [R.2.2.2.2.2.1, ht]; simp, ?_, ?_⟩
    · rw [R.2.2.2.2.2.2.1, a4 UpsV3.up (by decide), hup, Nat.mul_zero]
    · rw [A.2.1 a6, f1]
      by_cases h1 : si = 0 <;> by_cases h2 : e = 0 <;> simp [h1, h2]
  -- prefix rows (tag, value slot): copied at their own position
  have copyPre : ∀ d, d < c0 - 2 → s.row (o + d) cp = 1 ∧ s.row (o + d) rd = 1 ∧
      (s.row (o + d) sBM = 0 ∨ (s.row (o + d) ba0 = 0 ∧ s.row (o + d) ba1 = 0)) ∧
      s.row (o + d) spos = 0 + d ∧ s.row (o + d) sN = s.row o sN := by
    intro d hd
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ := B.pre d (by omega)
    have hok := okRow hw hs a2
    have hs1 := a1.sum; have hb := a1.bs
    have hbm0 : s.row (o + d) sBM = 0 := by
      rcases (show s.row (o + d) sBM = 0 ∨ s.row (o + d) sBM = 1 by omega) with h | h
      · exact h
      · have := a10.1 h; omega
    have hcp : s.row (o + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      by_cases ht : s.row (o + d) sTAG = 1
      · rw [cpTAG hok (rowLt hw hs _) hs1 ht, show s.row (o + d) kRDB = 0 from a3.kd 0 (by omega),
          show s.row (o + d) kRDE = 0 from a3.kd 1 (by omega), show s.row (o + d) kRLP = 0 from a3.kd 2 (by omega),
          show s.row (o + d) kRBR = 0 from a3.kd 3 (by omega), show s.row (o + d) kRBI = 1 from a3.kd 5 (by omega),
          show s.row (o + d) kPT = 0 from a3.kd 11 (by omega)]; rfl
      by_cases hv : s.row (o + d) sVLEN = 1
      · rw [cpVLEN hok (rowLt hw hs _) hs1 hv, a4 vcp (by decide), hv0]
      · have hvh : s.row (o + d) sVH = 1 := by omega
        rw [cpVH hok (rowLt hw hs _) hs1 hvh, a4 vcp (by decide), hv0]
    have hx : s.row (o + d) xcp = 0 := by rw [a4 xcp (by decide), hx0]
    have hrd := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) a5 hcp a1
      (fun _ => ⟨a3.kd 4 (by omega), a3.kd 6 (by omega), a3.kd 7 (by omega), hx⟩)
      (fun _ => ⟨a3.kd 6 (by omega), a3.kd 7 (by omega)⟩) (fun _ => a3.kd 3 (by omega)) (fun _ => hx)
      (rdcOff hok (rowLt hw hs _) (nextLt hw hs _) a6)
    have ha := aftAt d (by omega) a6
    rw [if_neg (by omega)] at ha
    have hsp := sposRBI hok (rowLt hw hs _) (nextLt hw hs _) hrd (a3.kd 5 (by omega)) ha (by omega)
    rw [(U.rows d (by omega)).2.1] at hsp
    exact ⟨hcp, hrd, Or.inl hbm0, by omega, a4 sN (by decide)⟩
  have cP := copyRunB hw hs Pb hR (r := o) (n := c0 - 2) (δ := 0) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by simpa using copyPre d hd)
  -- the bitmap rows
  have bmRow : ∀ t, t < 2 → s.row (o + (c0 - 2 + t)) b =
      (Pb (s.row o sN)).getD (c0 - 2 + t) 0 + (if t = 0 then (if si = 0 then 1 else 0) else (if si = 0 then 0 else 128)) := by
    intro t ht
    have hd0 : c0 - 2 + t < c0 + 32 * ww + 8 := by omega
    have hd1 : 32 * 0 ≤ c0 - 2 + t := by omega
    have hd2 : ¬ (c0 + 32 * ww ≤ c0 - 2 + t) := by omega
    obtain ⟨a1, a2, a3, a4, a5, a6, -, -, -, a10, a11, a12⟩ := B.pre (c0 - 2 + t) (by omega)
    have hok := okRow hw hs a2
    have hbm : s.row (o + (c0 - 2 + t)) sBM = 1 := a10.2 (by omega)
    have hcp : s.row (o + (c0 - 2 + t)) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rw [cpBM hok (rowLt hw hs _) a1.sum hbm, show s.row (o + (c0 - 2 + t)) kRDB = 0 from a3.kd 0 (by omega),
        show s.row (o + (c0 - 2 + t)) kRBR = 0 from a3.kd 3 (by omega), show s.row (o + (c0 - 2 + t)) kRBV = 0 from a3.kd 4 (by omega),
        show s.row (o + (c0 - 2 + t)) kRBI = 1 from a3.kd 5 (by omega)]; rfl
    have hx : s.row (o + (c0 - 2 + t)) xcp = 0 := by rw [a4 xcp (by decide), hx0]
    have hrd := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) a5 hcp a1
      (fun _ => ⟨a3.kd 4 (by omega), a3.kd 6 (by omega), a3.kd 7 (by omega), hx⟩)
      (fun _ => ⟨a3.kd 6 (by omega), a3.kd 7 (by omega)⟩) (fun _ => a3.kd 3 (by omega)) (fun _ => hx)
      (rdcOff hok (rowLt hw hs _) (nextLt hw hs _) a6)
    have ha := aftAt (c0 - 2 + t) hd0 a6
    rw [if_neg hd2] at ha
    have hr := (readAt (c0 - 2 + t) 0 hd0 hrd ha hd1).1
    rw [Nat.mul_zero, Nat.sub_zero] at hr
    have sl := kSel hw hs hsc K (r := o + (c0 - 2 + t)) (by omega) (by omega)
    have hrb : s.row (o + (c0 - 2 + t)) rb < 256 := by rw [hr, hsrc]; exact toNats_lt _ _
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · have hfs : s.row (o + (c0 - 2 + 0)) fs = 1 := a12 hbm (by omega)
      rw [bCopyIns hok (rowLt hw hs _) (nextLt hw hs _) hcp hbm (a := if si = 0 then 1 else 0)
        (Or.inl ⟨hfs, by rw [sl.2.2.1]; by_cases h : si = 0 <;> simp [h, ba0V, kdOf, UKind.all, b2n]⟩)
        (by rw [P_lit]; split <;> omega), hr]
      simp
    · have hfs : s.row (o + (c0 - 2 + 1)) fs = 0 := by
        rcases rowBool hok (rowLt hw hs _) (x := fs) (by decide) with h | h
        · exact h
        · have := a11 h hbm; omega
      rw [bCopyIns hok (rowLt hw hs _) (nextLt hw hs _) hcp hbm (a := if si = 0 then 0 else 128)
        (Or.inr ⟨hfs, by rw [sl.2.2.2.1]; by_cases h : si = 0 <;> simp [h, ba1V, kdOf, UKind.all, b2n]⟩)
        (by rw [P_lit]; split <;> omega), hr]
      simp
  -- copied windows (after the new first window when `si = 0`, before the new last window otherwise)
  obtain ⟨off, hoffv⟩ : ∃ off, off = if si = 0 then 1 else 0 := ⟨_, rfl⟩
  have hoff : off ≤ 1 := by rw [hoffv]; split <;> omega
  have copyW : ∀ d, d < 32 * (ww - 1) → s.row (o + c0 + 32 * off + d) cp = 1 ∧
      s.row (o + c0 + 32 * off + d) rd = 1 ∧
      (s.row (o + c0 + 32 * off + d) sBM = 0 ∨
        (s.row (o + c0 + 32 * off + d) ba0 = 0 ∧ s.row (o + c0 + 32 * off + d) ba1 = 0)) ∧
      s.row (o + c0 + 32 * off + d) spos = c0 + d ∧ s.row (o + c0 + 32 * off + d) sN = s.row o sN := by
    intro d hd
    have e0 : off + d / 32 < ww := by omega
    have r := role (off + d / 32) e0 (d % 32) (by omega)
    rw [show o + c0 + 32 * (off + d / 32) + d % 32 = o + c0 + 32 * off + d by omega] at r
    have hne : ¬ (off + d / 32 = es) := by rw [hesv]; rw [hoffv]; split <;> omega
    simp only [if_neg hne] at r
    have haft : s.row (o + c0 + 32 * off + d) aft = off := by
      rw [r.2.2.2, hoffv]; by_cases h : si = 0 <;> simp [h] <;> omega
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * off + d) (by omega)
    rw [show o + c0 + (32 * off + d) = o + c0 + 32 * off + d by omega] at a1 a2 a3 a4 a5 a6
    have hok := okRow hw hs a2
    have hcp : s.row (o + c0 + 32 * off + d) cp = 1 := by
      apply natv (rowLt hw hs _ _) one_lt
      rw [cpCH hok (rowLt hw hs _) a1.sum a6, r.1]; rfl
    have hx : s.row (o + c0 + 32 * off + d) xcp = 0 := by rw [a4 xcp (by decide), hx0]
    have hb1 := a1.bs; have hs1 := a1.sum
    have hrd := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) a5 hcp a1
      (fun h => by omega) (fun _ => ⟨a3.kd 6 (by omega), a3.kd 7 (by omega)⟩)
      (fun h => by omega) (fun _ => hx) r.2.2.1
    have hq := (U.rows (c0 + 32 * off + d) (by omega)).2.1
    rw [show o + (c0 + 32 * off + d) = o + c0 + 32 * off + d by omega] at hq
    have hsp := sposRBI hok (rowLt hw hs _) (nextLt hw hs _) hrd (a3.kd 5 (by omega)) haft (by rw [hq]; omega)
    rw [hq] at hsp
    refine ⟨hcp, hrd, Or.inl (by omega), by rw [hsp]; omega, a4 sN (by decide)⟩
  have cW := copyRunB hw hs Pb hR (r := o + c0 + 32 * off) (n := 32 * (ww - 1)) (δ := c0)
    (N := s.row o sN) (by omega) (by omega) copyW
  -- the new window (fresh: the new leaf's digest)
  have hWe := B.winU es hes
  have FC := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + c0 + 32 * es + d) sCH = 1 ∧ s.row (o + c0 + 32 * es + d) wfr = 1 ∧
      s.row (o + c0 + 32 * es + d) wn = 1 := by
    intro d hd
    have F := FC d hd
    have r := role es hes d hd
    simp only [if_pos rfl] at r
    exact ⟨(stOf_inv F.1).2.2.2.2.2.2.2.1 F.2.1, r.1, r.2.1⟩
  have eW := freshWin hw hs (r0 := o + c0 + 32 * es) (by omega)
    (fun d hd => Or.inr ⟨(chU d hd).1, (chU d hd).2.1, by have := (FC d hd).1.sum; have := (chU d hd).1; omega⟩)
    (fun d hd => feZero hw hs hsc K hWe.1 (by omega) d (by omega))
  have F0 := FC 0 (by omega)
  simp only [Nat.add_zero] at F0
  have c0' := chU 0 (by omega)
  simp only [Nat.add_zero] at c0'
  have hr3 : o + c0 + 32 * es < s.rows.length := by omega
  have hgD := gDrow (okRow hw hs hr3) (rowLt hw hs _) (nextLt hw hs _) F0.2.2.2.2.2
    (by simpa using (hWe.1.fs 0 (by omega)).2 rfl) (qbWt3 hw hs hr3 F0.2.2.2.2.2)
    (Or.inr ⟨c0'.1, c0'.2.1, by have := F0.1.sum; omega⟩)
  have hdI0 := dCHn (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2
  rw [F0.2.2.2.2.1 j (by decide), hj, hsc _ hr3 tau (by decide)] at hdI0
  have hdI : s.row (o + c0 + 32 * es) dI = upsIdN (s.row 0 tau) k := by
    apply dIj_nat (rowLt hw hs _ _)
    rw [hdI0, natCast_add, cast1]; grind
  have hdL : s.row (o + c0 + 32 * es) dL = 50 :=
    natv (rowLt hw hs _ _) (by rw [P_lit]; omega) (dCHnl (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
  have hDN := hdN (o + c0 + 32 * es) hr3 hgD hdI hdL
  -- the source bytes
  have hTagL : (brTag bv).length = c0 - 2 := by
    have := hpreL; rw [brPre_eq] at this; simp at this; omega
  have hPb : Pb (s.row o sN) = brTag bv ++ ([NearSpec.kidsBitmap cs 0 % 256, NearSpec.kidsBitmap cs 0 / 256 % 256] ++
      ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat)) := by
    rw [hsrc, brEnc, brPre_eq, List.append_assoc]
  -- MEM
  have R5 := memRegs hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega)
  have FM := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega)
  have rbM : ∀ i, i < 8 → s.row (o + c0 + 32 * ww + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
    intro i hi
    have F := FM i hi
    have hrd := rdMem (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) F.2.2.2.2.2
      ((stOf_inv F.1).2.2.2.2.2.2.2.2 F.2.1) (F.2.2.2.1.kd 8 (by omega)) F.1
    have ha := aftAt (c0 + 32 * ww + i) (by omega) (by
      rw [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega]
      have := F.1.bs; have := F.1.sum; have := (stOf_inv F.1).2.2.2.2.2.2.2.2 F.2.1; omega)
    rw [if_pos (by omega)] at ha
    have := (readAt (c0 + 32 * ww + i) 1 (by omega)
      (by rwa [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega]) ha (by omega)).1
    rw [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega] at this
    rw [this, hPb, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by simp [hHl]; omega)]
    simp [hHl]
    rw [show c0 + 32 * ww + i - 32 - (brTag bv).length - 2 - 32 * (ww - 1) = i by omega]
  have hA : limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 = m := by
    rw [show limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 =
        limbs (fun i => ((NearSpec.u64 m).map UInt8.toNat).getD i 0) 8 by
      simp only [limbs8]; rw [rbM 0 (by omega), rbM 1 (by omega), rbM 2 (by omega), rbM 3 (by omega),
        rbM 4 (by omega), rbM 5 (by omega), rbM 6 (by omega), rbM 7 (by omega)], limbs_u64]
    omega
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => (FM i hi).2.2.2.2.1 x hx
  obtain ⟨hL0, hL1, hL2⟩ := hLb
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U B.memU.1 B.memU.2 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + c0 + 32 * ww + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      have hLbi : bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i < 256 := by
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
        rcases (show s.row (o + c0 + 32 * ww + i) fs = 0 ∨ s.row (o + c0 + 32 * ww + i) fs = 1 by omega) with h | h <;>
          rw [h] <;> omega
      · have := hbyte (c0 + 32 * ww + i) (by omega)
        rwa [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega] at this)
  simp only [hKc, heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hA] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * ww) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    simp only [UpsSpec.qRBI, NearSpec.leafMem, ysOf_hpLen si i4, NearSpec.PTrie.memD, NearSpec.PTrie.mem?, Option.getD_some, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    omega
  -- the bytes before the windows
  have ePre : rowsB s o c0 = brTag bv ++ [NearSpec.kidsBitmap cs 0 % 256 + (if si = 0 then 1 else 0),
      NearSpec.kidsBitmap cs 0 / 256 % 256 + (if si = 0 then 0 else 128)] := by
    rw [show c0 = (c0 - 2) + 2 by omega, rowsB_append, cP, List.drop_zero, hPb, List.take_left' hTagL]
    congr 1
    have b0 := bmRow 0 (by omega); have b1 := bmRow 1 (by omega)
    rw [hPb] at b0 b1
    simp only [List.getD_eq_getElem?_getD] at b0 b1
    rw [List.getElem?_append_right (by omega)] at b0 b1
    simp [hTagL, show c0 - 2 + 1 - (c0 - 2) = 1 by omega] at b0 b1
    simp only [rowsB, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.add_zero]
    rw [show o + (c0 - 2) + 1 = o + (c0 - 2 + 1) by omega, b0, b1]
  have eH : ((Pb (s.row o sN)).drop c0).take (32 * (ww - 1)) = (NearSpec.Kids.hashes cs).map UInt8.toNat := by
    rw [hPb, show c0 = (brTag bv).length + 2 by omega, List.drop_append, List.drop_eq_nil_of_le (by simp),
      List.nil_append, show (brTag bv).length + 2 - (brTag bv).length = 2 by omega]
    simp [List.take_left', hHl]
  rw [eH] at cW
  -- assemble
  rw [B.bytes, ePre, eM]
  simp only [UpsSpec.qRBI, brEnc, brPre_eq]
  have hbm16 := UpsSpec.kidsBitmap_lt cs
  rw [hkl] at hbm16
  have hlm : NearSpec.leafMem (UpsSpec.ysOf si) val.length = 102 + val.length := by
    unfold NearSpec.leafMem; rw [ysOf_hpLen si i4]; omega
  rw [hlm]
  rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl
  · -- the new first window
    have hes0 : es = 0 := by rw [hesv]; rfl
    have hoff1 : off = 1 := by rw [hoffv]; rfl
    rw [hes0] at eW hDN
    rw [hoff1] at cW
    obtain ⟨h1, h2⟩ := UpsSpec.setKid_first_ins cs (UpsSpec.qNLF 0 val) hslot (by omega)
    have hev := UpsSpec.kidsBitmap_even cs hslot
    simp only [Nat.mul_zero, Nat.add_zero] at eW hDN
    rw [show 32 * ww = 32 + 32 * (ww - 1) by omega, rowsB_append, eW, cW]
    rw [show (List.range 32).map (fun i => s.row (o + c0) (reg i)) = regN (s.row (o + c0)) from rfl, hDN]
    simp only [UpsSpec.yOf, UpsSpec.key, List.getD_cons_zero] at h1 h2 ⊢
    rw [h1, h2 0]
    simp only [List.map_append, List.append_assoc, List.cons_append, List.nil_append, ite_true, Nat.pow_zero]
    rw [show (1 + NearSpec.kidsBitmap cs 0) % 256 = NearSpec.kidsBitmap cs 0 % 256 + 1 by omega,
      show (1 + NearSpec.kidsBitmap cs 0) / 256 % 256 = NearSpec.kidsBitmap cs 0 / 256 % 256 by omega]
    simp only [Nat.add_zero, Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.sub_zero]
    rw [show 102 + (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) + m = m + (102 + val.length) by omega]
  · -- the new last window
    have hes1 : es = ww - 1 := by rw [hesv]; rfl
    have hoff0 : off = 0 := by rw [hoffv]; rfl
    rw [hes1] at eW hDN
    rw [hoff0] at cW
    obtain ⟨h1, h2⟩ := UpsSpec.setKid_last_ins (UpsSpec.qNLF 1 val) cs 15 hkl hslot
    have hlt15 := UpsSpec.kidsBitmap_lastFree cs 15 hkl hslot
    simp only [Nat.mul_zero, Nat.add_zero] at cW
    rw [show 32 * ww = 32 * (ww - 1) + 32 by omega, rowsB_append, cW, eW]
    rw [show (List.range 32).map (fun i => s.row (o + c0 + 32 * (ww - 1)) (reg i)) =
      regN (s.row (o + c0 + 32 * (ww - 1))) from rfl, hDN]
    simp only [UpsSpec.yOf, UpsSpec.key, List.getD_cons_succ, List.getD_cons_zero] at h1 h2 ⊢
    rw [h1, h2 0]
    simp only [List.map_append, List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add,
      show ¬ ((1 : Nat) = 0) by omega, ite_false]
    rw [show (NearSpec.kidsBitmap cs 0 + 2 ^ 15) % 256 = NearSpec.kidsBitmap cs 0 % 256 by omega,
      show (NearSpec.kidsBitmap cs 0 + 2 ^ 15) / 256 % 256 = NearSpec.kidsBitmap cs 0 / 256 % 256 + 128 by omega]
    simp only [Nat.add_zero, Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.sub_zero]
    rw [show 102 + (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) + m = m + (102 + val.length) by omega]


end

end ZkFormal.NearV3.UpsRows

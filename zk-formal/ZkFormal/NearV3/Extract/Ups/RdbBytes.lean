import ZkFormal.NearV3.Extract.Ups.BranchK

/-!
# ZkFormal.NearV3.Extract.Ups.RdbBytes — a branch descend, `RDB` (layer 2)

A part of kind `RDB` (index 0) rewrites the branch `.branch bv cs m` on the path at the slot it
descends through (`n = 15` from the level-1 record, else `0`): every byte is copied from the
source at its own position except the target window — the first window for slot `0`, the last for
slot `15` (`winFlags`, `tgt`) — which is the digest of the part below, and the `MEM` field
(`m + c'.memD − cm`).  So the part is `nodeEnc (qRDB bv cs m n c' cm)` (`ups_rdbBytes`).

Hypotheses: `UpbReads s Pb`, the source is `nodeEnc (.branch bv cs m)` (a 36-byte value slot if
any, `m < 2^64`, 16 slots, slot `n` holds a child with a 32-byte hash); the `DIGEST` of the part
below at `clen` is `c'.hashOf`; the `MEMD` limbs on the `MEM` rows (`< 2^12`) are `c'.memD` / `cm`;
the part's bytes are `< 256`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The bytes of a branch before its child hashes: tag, value slot, bitmap. -/
def brPre (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) : List Nat :=
  (match bv with | none => [1] | some sl => [2] ++ sl.valueRef.map UInt8.toNat) ++
    (NearSpec.u16 (NearSpec.kidsBitmap cs 0)).map UInt8.toNat

theorem brEnc (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (m : Nat) :
    (nodeEnc (.branch bv cs m)).map UInt8.toNat =
      brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat) := by
  cases bv <;> simp [nodeEnc, brPre]

theorem brPre_len (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (hbv : ∀ sl, bv = some sl → sl.valueRef.length = 36) :
    (brPre bv cs).length = (if bv.isSome then 39 else 3) ∧ (brPre bv cs).getD 0 0 = (if bv.isSome then 2 else 1) := by
  cases bv with
  | none => simp [brPre, NearSpec.u16, leN_length]
  | some sl => simp [brPre, NearSpec.u16, leN_length, hbv sl rfl]

/-- The slot a descend from source level `sd` goes through. -/
def slotOf (sd : Nat) : Nat := if sd = 1 then 15 else 0

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **A branch descend** (`RDB`): its bytes are `nodeEnc (qRDB bv cs m (slotOf sd) c' cm)`. -/
theorem ups_rdbBytes (k : Nat) (hk : k < ps.length) (hkd : kd k = 0)
    (Pb : Nat → List Nat) (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (c c' : NearSpec.PTrie) (m cm : Nat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.branch bv cs m)).map UInt8.toNat)
    (hbv : ∀ sl, bv = some sl → sl.valueRef.length = 36) (hm : m < 2 ^ 64)
    (hkl : UpsSpec.kidsLen cs = 16) (hslot : UpsSpec.kidAt cs (slotOf (sdx k)) = some c) (hc32 : c.hashOf.length = 32)
    (hdC : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = s.row ps[k].1 clen → regN (s.row i) = c'.hashOf.map UInt8.toNat)
    (hMd : ∀ i, i < 8 → s.row (ps[k].1 + ps[k].2 - 8 + i) mBv < 4096 ∧ s.row (ps[k].1 + ps[k].2 - 8 + i) mCv < 4096)
    (hmB : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mBv) 8 = c'.memD)
    (hmC : limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) mCv) 8 = cm)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRDB bv cs m (slotOf (sdx k)) c' cm)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRDB bv cs m (slotOf (sdx k)) c' cm).memD := by
  have K := partK hw hs hL hP k hk
  have hup : s.row ps[k].1 UpsV3.up = 1 := by
    rcases Nat.lt_or_ge k (nTof ci ti) with h | h
    · have := (hP.term k hk h).2.1; omega
    · exact (hP.upper k hk h).2.1
  obtain ⟨hj, -⟩ := hL.part k hk
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  rw [hkd] at K
  generalize hsd : sdx k = sd at K hslot ⊢
  generalize ps[k].1 = o at K U hbyte hsrc hup hdC hMd hmB hmC hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte hMd hmB hmC ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, isd⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨hx0, hv0, htl, hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_RDB ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨c0, B⟩ := brLay hw hs hsc K U htl hte
  have hℓ := B.len
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  have hc0 : c0 = 3 ∨ c0 = 39 := by rcases B.c0v with h | h <;> omega
  -- direct reads
  have readAt : ∀ d, d < c0 + 32 * ww + 8 → s.row (o + d) rd = 1 →
      s.row (o + d) rb = (Pb (s.row o sN)).getD d 0 ∧ s.row (o + d) plen = (Pb (s.row o sN)).length := by
    intro d h2 hrd
    have hlt : o + d < s.rows.length := by omega
    have hI := K.ix d h2
    have hsp := dirRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hI (by omega) hrd
    rw [(U.rows d h2).2.1] at hsp
    have := hR (o + d) hlt hrd
    rwa [hsp, K.pc d h2 sN (by decide)] at this
  -- the window roles: the target window is `e* = 0` (slot 0) or `w − 1` (slot 15)
  have hMEM0 := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at hMEM0
  have hm8 : s.row (o + c0 + 32 * ww) sMEM = 1 := (stOf_inv hMEM0.1).2.2.2.2.2.2.2.2 hMEM0.2.1
  have hww0 : 0 < ww ∨ ww = 0 := by omega
  -- the source's length, from a `MEM` read
  have hrdM : s.row (o + (c0 + 32 * ww)) rd = 1 := by
    rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]
    exact rdMem (okRow hw hs hMEM0.2.2.1) (rowLt hw hs _) (nextLt hw hs _) hMEM0.2.2.2.2.2 hm8
      (hMEM0.2.2.2.1.kd 8 (by omega)) hMEM0.1
  have hpl := (readAt (c0 + 32 * ww) (by omega) hrdM).2
  have hpM := pMEM (okRow hw hs (i := o + (c0 + 32 * ww)) (by omega)) (rowLt hw hs _)
    (by rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; exact hMEM0.1.sum) hrdM
    (by rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; exact hm8)
  have hidx : s.row (o + (c0 + 32 * ww)) idx = 0 := by
    have := B.memU.1.idx 0 (by omega); rwa [show o + c0 + 32 * ww + 0 = o + (c0 + 32 * ww) by omega] at this
  have hsp0 : s.row (o + (c0 + 32 * ww)) spos = c0 + 32 * ww := by
    rw [dirRow (okRow hw hs (i := o + (c0 + 32 * ww)) (by omega)) (rowLt hw hs _) (nextLt hw hs _)
      (K.ix (c0 + 32 * ww) (by omega)) (by omega) hrdM, (U.rows (c0 + 32 * ww) (by omega)).2.1]
  rw [hidx, hsp0] at hpM
  have hPlen : (Pb (s.row o sN)).length = c0 + 32 * ww + 8 := by
    rw [← hpl]
    have e : ((c0 + 32 * ww + 8 : Nat) : Fp) = ((s.row (o + (c0 + 32 * ww)) plen : Nat) : Fp) := by
      rw [natCast_add]
      rw [cast0] at hpM
      grind
    exact (natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e).symm
  -- the tag: `bv` matches the layout
  have hT0 := B.pre 0 (by omega)
  simp only [Nat.add_zero] at hT0
  obtain ⟨t1, -, -, -, -, t6, -, -, t9, t10, -, -⟩ := hT0
  have htag1 : s.row o sTAG = 1 := t9.2 trivial
  have hcp0 : s.row o cp = 1 := by
    apply natv (rowLt hw hs _ _) one_lt
    rw [cpTAG ok0 (rowLt hw hs _) t1.sum htag1, show s.row o kRDB = 1 from I0.kd 0 (by omega),
      show s.row o kRDE = 0 from I0.kd 1 (by omega), show s.row o kRLP = 0 from I0.kd 2 (by omega),
      show s.row o kRBR = 0 from I0.kd 3 (by omega), show s.row o kRBI = 0 from I0.kd 5 (by omega),
      show s.row o kPT = 0 from I0.kd 11 (by omega)]; rfl
  have hrd0 : s.row o rd = 1 := rdCopy ok0 (rowLt hw hs _) (nextLt hw hs _) hq0 hcp0 t1
    (fun _ => ⟨I0.kd 4 (by omega), I0.kd 6 (by omega), I0.kd 7 (by omega), hx0⟩)
    (fun _ => ⟨I0.kd 6 (by omega), I0.kd 7 (by omega)⟩) (fun _ => I0.kd 3 (by omega)) (fun _ => hx0)
    (rdcOff ok0 (rowLt hw hs _) (nextLt hw hs _) t6)
  have hb0 := bCopyN ok0 (rowLt hw hs _) (nextLt hw hs _) hcp0 (by have := t1.bs; have := t1.sum; omega)
  have hgr0 := (gramRow ok0 (rowLt hw hs _) (nextLt hw hs _) t1.sum).1 htag1 K.pf
  have hr0 := (readAt 0 (by omega) (by simpa using hrd0)).1
  simp only [Nat.add_zero] at hr0
  rw [hb0, hr0, hsrc, brEnc] at hgr0
  have hpreL : (brPre bv cs).length = c0 := by
    obtain ⟨l1, l2⟩ := brPre_len bv cs hbv
    have : (brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat)).getD 0 0 =
        (brPre bv cs).getD 0 0 := by
      simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by rw [l1]; split <;> omega)]
    rw [this, l2] at hgr0
    rw [l1]
    rcases B.c0v with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> cases bv <;> simp at hgr0 ⊢ <;> omega
  have hHl : (NearSpec.Kids.hashes cs).length = 32 * ww := by
    have := congrArg List.length hsrc
    rw [hPlen, brEnc] at this
    simp only [List.length_append, List.length_map, u64_length, hpreL] at this
    omega
  -- the slot's child hash, the windows
  have hww : 0 < ww := by
    rcases (show slotOf sd = 0 ∨ slotOf sd = 15 by unfold slotOf; split <;> omega) with h | h
    · rw [h] at hslot
      obtain ⟨R, h1, -⟩ := UpsSpec.setKid_first cs c c' hslot
      have := congrArg List.length h1; simp [hc32] at this; omega
    · rw [h] at hslot
      obtain ⟨R, h1, -⟩ := UpsSpec.setKid_last c c' cs 15 hkl hslot
      have := congrArg List.length h1; simp [hc32] at this; omega
  have WF := winFlags hw hs (r := o + c0) hww (by omega) (by omega)
    (by have := (B.pre (c0 - 1) (by omega)).2.2.2.2.2.1; rwa [show o + (c0 - 1) = o + c0 - 1 by omega] at this)
    (fun e he => ⟨(B.winU e he).1, fun d hd => by
      have := (B.win (32 * e + d) (by omega)).2.2.2.2.2; rwa [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at this⟩)
    hm8 (by have := hMEM0.1.bs; have := hMEM0.1.sum; omega)
  -- the target window `e*`
  let es := if sd = 1 then ww - 1 else 0
  have role : ∀ e, e < ww → ∀ d, d < 32 → s.row (o + c0 + 32 * e + d) wfr = (if e = es then 1 else 0) ∧
      s.row (o + c0 + 32 * e + d) wn = 0 ∧
      s.row (o + c0 + 32 * e + d) rdc = s.row (o + c0 + 32 * e + d) fs * (if e = es then 1 else 0) := by
    intro e he d hd
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * e + d) (by omega)
    rw [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at a1 a2 a3 a4 a5 a6
    have sl := kSel hw hs hsc K (r := o + c0 + 32 * e + d) (by omega) (by omega)
    have R := winRole (okRow hw hs a2) (rowLt hw hs _) (nextLt hw hs _) a3 i1 i4 (by omega) isd a6 sl.2.2.2.2.1
      sl.2.2.2.2.2 sl.2.1
    obtain ⟨f1, f2⟩ := WF e he d hd
    have ht : s.row (o + c0 + 32 * e + d) tgt = if e = es then 1 else 0 := by
      rw [R.1, f1, f2]
      simp only [s15V, kdOf, UKind.all, b2n, es]
      by_cases h1 : sd = 1 <;> simp [h1] <;> split <;> split <;> omega
    refine ⟨by rw [R.2.1 (Or.inl rfl), ht], by rw [R.2.2.2.2.2.1]; rfl, ?_⟩
    rw [R.2.2.2.2.2.2.1, ht, a4 UpsV3.up (by decide), hup, Nat.mul_one]
  have hes : es < ww := by simp only [es]; split <;> omega
  -- copied rows: everything before `MEM` but the target window
  have copyAt : ∀ d, d < c0 + 32 * ww → (d < c0 + 32 * es ∨ c0 + 32 * es + 32 ≤ d) →
      s.row (o + d) cp = 1 ∧ s.row (o + d) rd = 1 ∧
      (s.row (o + d) sBM = 0 ∨ (s.row (o + d) ba0 = 0 ∧ s.row (o + d) ba1 = 0)) ∧
      s.row (o + d) spos = d ∧ s.row (o + d) sN = s.row o sN := by
    intro d hd hne
    have hlt : o + d < s.rows.length := by omega
    have hok := okRow hw hs hlt
    have hI := K.ix d (by omega)
    have hpc := K.pc d (by omega)
    have hq := K.qb d (by omega)
    have hx : s.row (o + d) xcp = 0 := by rw [hpc xcp (by decide), hx0]
    have hba : s.row (o + d) ba0 = 0 ∧ s.row (o + d) ba1 = 0 := by
      have := kSel hw hs hsc K (r := o + d) (by omega) (by omega)
      rw [this.2.2.1, this.2.2.2.1]; simp [ba0V, ba1V, kdOf, UKind.all, b2n]
    obtain ⟨hcp, hoh, hrdc⟩ : s.row (o + d) cp = 1 ∧ OneHot (s.row (o + d)) ∧ s.row (o + d) rdc = 0 := by
      rcases Nat.lt_or_ge d c0 with h | h
      · obtain ⟨a1, -, -, -, -, a6, a7, a8, -⟩ := B.pre d h
        have hs1 := a1.sum; have hb := a1.bs
        refine ⟨?_, a1, rdcOff hok (rowLt hw hs _) (nextLt hw hs _) a6⟩
        apply natv (rowLt hw hs _ _) one_lt
        by_cases ht : s.row (o + d) sTAG = 1
        · rw [cpTAG hok (rowLt hw hs _) hs1 ht, show s.row (o + d) kRDB = 1 from hI.kd 0 (by omega),
            show s.row (o + d) kRDE = 0 from hI.kd 1 (by omega), show s.row (o + d) kRLP = 0 from hI.kd 2 (by omega),
            show s.row (o + d) kRBR = 0 from hI.kd 3 (by omega), show s.row (o + d) kRBI = 0 from hI.kd 5 (by omega),
            show s.row (o + d) kPT = 0 from hI.kd 11 (by omega)]; rfl
        by_cases hb' : s.row (o + d) sBM = 1
        · rw [cpBM hok (rowLt hw hs _) hs1 hb', show s.row (o + d) kRDB = 1 from hI.kd 0 (by omega),
            show s.row (o + d) kRBR = 0 from hI.kd 3 (by omega), show s.row (o + d) kRBV = 0 from hI.kd 4 (by omega),
            show s.row (o + d) kRBI = 0 from hI.kd 5 (by omega)]; rfl
        by_cases hv : s.row (o + d) sVLEN = 1
        · rw [cpVLEN hok (rowLt hw hs _) hs1 hv, hpc vcp (by decide), hv0]
        · have hvh : s.row (o + d) sVH = 1 := by omega
          rw [cpVH hok (rowLt hw hs _) hs1 hvh, hpc vcp (by decide), hv0]
      · obtain ⟨a1, -, -, -, -, a6⟩ := B.win (d - c0) (by omega)
        rw [show o + c0 + (d - c0) = o + d by omega] at a1 a6
        have r := role ((d - c0) / 32) (by omega) ((d - c0) % 32) (by omega)
        rw [show o + c0 + 32 * ((d - c0) / 32) + (d - c0) % 32 = o + d by omega] at r
        have hne' : ¬ ((d - c0) / 32 = es) := by omega
        rw [if_neg hne'] at r
        refine ⟨?_, a1, by rw [r.2.2]; simp⟩
        apply natv (rowLt hw hs _ _) one_lt
        rw [cpCH hok (rowLt hw hs _) a1.sum a6, r.1]; rfl
    have hrd : s.row (o + d) rd = 1 := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh
      (fun _ => ⟨hI.kd 4 (by omega), hI.kd 6 (by omega), hI.kd 7 (by omega), hx⟩)
      (fun _ => ⟨hI.kd 6 (by omega), hI.kd 7 (by omega)⟩) (fun _ => hI.kd 3 (by omega)) (fun _ => hx) hrdc
    refine ⟨hcp, hrd, Or.inr hba, ?_, hpc sN (by decide)⟩
    rw [dirRow hok (rowLt hw hs _) (nextLt hw hs _) hI (by omega) hrd]
    exact (U.rows d (by omega)).2.1
  have cA := copyRunB hw hs Pb hR (r := o) (n := c0 + 32 * es) (δ := 0) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by simpa using copyAt d (by omega) (Or.inl hd))
  have cB := copyRunB hw hs Pb hR (r := o + (c0 + 32 * es + 32)) (n := 32 * (ww - es - 1)) (δ := c0 + 32 * es + 32)
    (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (c0 + 32 * es + 32 + d) (by omega) (Or.inr (by omega))
      rwa [show o + (c0 + 32 * es + 32 + d) = o + (c0 + 32 * es + 32) + d by omega] at this)
  -- the target window (fresh)
  have hWe := B.winU es hes
  have FC := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + c0 + 32 * es + d) sCH = 1 ∧ s.row (o + c0 + 32 * es + d) wfr = 1 ∧
      s.row (o + c0 + 32 * es + d) wn = 0 := by
    intro d hd
    have F := FC d hd
    have r := role es hes d hd
    rw [if_pos rfl] at r
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
  have hjm : s.row o jm = k := by
    rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by
      rw [show s.row o kRDB = 1 from I0.kd 0 (by omega), show s.row o kRDE = 0 from I0.kd 1 (by omega),
        show s.row o kWEX = 0 from I0.kd 9 (by omega), show s.row o kPT = 0 from I0.kd 11 (by omega)]) (by omega), hj]
    omega
  have hdI := dIj_nat (rowLt hw hs _ _) (dCHm (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
  have hdL := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (dCHml (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
  rw [hsc _ hr3 tau (by decide), F0.2.2.2.2.1 jm (by decide), hjm] at hdI
  rw [F0.2.2.2.2.1 clen (by decide)] at hdL
  have hDC := hdC (o + c0 + 32 * es) hr3 hgD hdI hdL
  -- MEM
  have R5 := memRegs hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega)
  have FM := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega)
  have rbM : ∀ i, i < 8 → s.row (o + c0 + 32 * ww + i) rb = ((NearSpec.u64 m).map UInt8.toNat).getD i 0 := by
    intro i hi
    have F := FM i hi
    have hrd := rdMem (okRow hw hs F.2.2.1) (rowLt hw hs _) (nextLt hw hs _) F.2.2.2.2.2
      ((stOf_inv F.1).2.2.2.2.2.2.2.2 F.2.1) (F.2.2.2.1.kd 8 (by omega)) F.1
    have := (readAt (c0 + 32 * ww + i) (by omega) (by rwa [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega])).1
    rw [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega] at this
    rw [this, hsrc, brEnc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hpreL]; omega), List.getElem?_append_right (by simp [hHl]; omega)]
    simp [hpreL, hHl]
    rw [show c0 + 32 * ww + i - c0 - 32 * ww = i by omega]
  have hA : limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 = m := by
    rw [show limbs (fun i => s.row (o + c0 + 32 * ww + i) rb) 8 =
        limbs (fun i => ((NearSpec.u64 m).map UInt8.toNat).getD i 0) 8 by
      simp only [limbs8]; rw [rbM 0 (by omega), rbM 1 (by omega), rbM 2 (by omega), rbM 3 (by omega),
        rbM 4 (by omega), rbM 5 (by omega), rbM 6 (by omega), rbM 7 (by omega)], limbs_u64]
    omega
  have hr0 : o + (c0 + 32 * ww + 8) - 8 = o + c0 + 32 * ww := by omega
  rw [hr0] at hMd hmB hmC
  have pc5 := fun i (hi : i < 8) x (hx : x ∈ partConst) => (FM i hi).2.2.2.2.1 x hx
  obtain ⟨eM, eX⟩ := memBytesK hw hs hsc K U B.memU.1 B.memU.2 (by omega) (by rw [heL, heS, huA, hbN, hbL, hcO, hcS]; omega)
    (fun i hi => by
      have hfs : s.row (o + c0 + 32 * ww + i) fs ≤ 1 := by rw [(R5 i hi).1]; split <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [inA, pc5 i hi useA (by decide), huA, Nat.one_mul, rbM i hi]
        have := toNats_lt (NearSpec.u64 m) i; omega
      · simp only [inB, pc5 i hi bN (by decide), pc5 i hi bL (by decide), hbN, hbL]
        have := (hMd i hi).1; omega
      · simp only [inC, pc5 i hi cO (by decide), pc5 i hi cS (by decide), pc5 i hi Cc (by decide), hcO, hcS, hCc]
        have := (hMd i hi).2; omega
      · simp [inE, pc5 i hi Kc (by decide), pc5 i hi eL (by decide), pc5 i hi eS (by decide), hKc, heL, heS]
      · have := hbyte (c0 + 32 * ww + i) (by omega)
        rwa [show o + (c0 + 32 * ww + i) = o + c0 + 32 * ww + i by omega] at this)
  simp only [hKc, heL, heS, huA, hbN, hbL, hcO, hcS, hCc, hA, hmB, hmC] at eM eX
  refine ⟨?_, (limbs_rows_eq (b := o + c0 + 32 * ww) (by omega) rx).trans ?_⟩
  rotate_left
  · rw [eX]
    simp only [UpsSpec.qRDB, NearSpec.PTrie.memD, NearSpec.PTrie.mem?, Option.getD_some, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]
    all_goals omega
  -- assemble
  have hsplit : rowsB s o c0 ++ rowsB s (o + c0) (32 * ww) =
      rowsB s o (c0 + 32 * es) ++ (rowsB s (o + c0 + 32 * es) 32 ++ rowsB s (o + (c0 + 32 * es + 32)) (32 * (ww - es - 1))) := by
    have h1 := rowsB_append s o c0 (32 * ww)
    have h2 := rowsB_append s o (c0 + 32 * es) (32 + 32 * (ww - es - 1))
    have h3 := rowsB_append s (o + (c0 + 32 * es)) 32 (32 * (ww - es - 1))
    rw [← h1, show c0 + 32 * ww = c0 + 32 * es + (32 + 32 * (ww - es - 1)) by omega, h2, h3]
    simp only [Nat.add_assoc]
  rw [B.bytes, ← List.append_assoc, hsplit, cA, cB, eW, eM]
  rw [show (List.range 32).map (fun i => s.row (o + c0 + 32 * es) (reg i)) = regN (s.row (o + c0 + 32 * es)) from rfl, hDC]
  rw [hsrc, brEnc]
  simp only [UpsSpec.qRDB]
  have hbm : ∀ i, NearSpec.kidsBitmap (UpsSpec.setKid cs (slotOf sd) c') i = NearSpec.kidsBitmap cs i :=
    fun i => UpsSpec.bitmap_setKid c c' cs _ i hslot
  have hpreT : brPre bv (UpsSpec.setKid cs (slotOf sd) c') = brPre bv cs := by simp [brPre, hbm]
  rw [brEnc, hpreT]
  have hHl' : ((NearSpec.Kids.hashes cs).map UInt8.toNat).length = 32 * ww := by simp [hHl]
  have hT : ((brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat)).drop 0).take
      (c0 + 32 * es) = brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat).take (32 * es) := by
    rw [List.drop_zero, List.take_append, List.take_of_length_le (by rw [hpreL]; omega), hpreL,
      show c0 + 32 * es - c0 = 32 * es by omega, List.take_append_of_le_length (by rw [hHl']; have := hes; omega)]
  have hD : ((brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat)).drop
      (c0 + 32 * es + 32)).take (32 * (ww - es - 1)) = ((NearSpec.Kids.hashes cs).map UInt8.toNat).drop (32 * es + 32) := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hpreL]; omega), List.nil_append, hpreL,
      show c0 + 32 * es + 32 - c0 = 32 * es + 32 by omega, List.drop_append_of_le_length (by rw [hHl']; have := hes; omega),
      List.take_left' (by simp [hHl]; have := hes; omega)]
  rw [hT, hD]
  have hmid : ((NearSpec.Kids.hashes cs).map UInt8.toNat).take (32 * es) ++ (c'.hashOf.map UInt8.toNat ++
      ((NearSpec.Kids.hashes cs).map UInt8.toNat).drop (32 * es + 32)) =
      (NearSpec.Kids.hashes (UpsSpec.setKid cs (slotOf sd) c')).map UInt8.toNat := by
    by_cases h1 : sd = 1
    · have hn : slotOf sd = 15 := by simp [slotOf, h1]
      have hes' : es = ww - 1 := by simp [es, h1]
      rw [hn] at hslot ⊢
      obtain ⟨R, e1, e2⟩ := UpsSpec.setKid_last c c' cs 15 hkl hslot
      have hRl : R.length = 32 * (ww - 1) := by have := congrArg List.length e1; simp [hc32] at this; omega
      rw [e2, e1, hes']
      simp only [List.map_append]
      rw [List.take_left' (by simp [hRl]), List.drop_eq_nil_of_le (by simp [hRl, hc32])]
      simp
    · have hn : slotOf sd = 0 := by simp [slotOf, h1]
      have hes' : es = 0 := by simp [es, h1]
      rw [hn] at hslot ⊢
      obtain ⟨R, e1, e2⟩ := UpsSpec.setKid_first cs c c' hslot
      rw [e2, e1, hes']
      simp only [List.map_append, Nat.mul_zero, Nat.zero_add, List.take_zero, List.nil_append]
      rw [show (32 : Nat) = (c.hashOf.map UInt8.toNat).length by simp [hc32], List.drop_left]
  rw [← hmid]
  simp only [List.append_assoc]
  simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]

/-- An `RDB` part looks up its child's digest (id `jm = k`, length `clen`) on its target window. -/
theorem rdbLook (k : Nat) (hk : k < ps.length) (hkd : kd k = 0)
    (Pb : Nat → List Nat) (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (c c' : NearSpec.PTrie) (m cm : Nat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.branch bv cs m)).map UInt8.toNat)
    (hbv : ∀ sl, bv = some sl → sl.valueRef.length = 36) (hm : m < 2 ^ 64)
    (hkl : UpsSpec.kidsLen cs = 16) (hslot : UpsSpec.kidAt cs (slotOf (sdx k)) = some c) (hc32 : c.hashOf.length = 32)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    ∃ i, i < s.rows.length ∧ s.row i gD = 1 ∧ s.row i dI = upsIdN (s.row 0 tau) k ∧ s.row i dL = s.row ps[k].1 clen := by
  have K := partK hw hs hL hP k hk
  have hup : s.row ps[k].1 UpsV3.up = 1 := by
    rcases Nat.lt_or_ge k (nTof ci ti) with h | h
    · have := (hP.term k hk h).2.1; omega
    · exact (hP.upper k hk h).2.1
  obtain ⟨hj, -⟩ := hL.part k hk
  obtain ⟨fl, ww, U⟩ : ∃ fl ww, UPartL s ps[k].1 ps[k].2 fl ww := ⟨_, _, (hL.part k hk).2⟩
  rw [hkd] at K
  generalize hsd : sdx k = sd at K hslot ⊢
  generalize ps[k].1 = o at K U hbyte hsrc hup hj ⊢
  generalize ps[k].2 = ℓ at K U hbyte ⊢
  have hsc := hL.segc
  obtain ⟨i1, -, -, i4, -, isd⟩ := K.idx
  have I0 := K.ix 0 K.pos
  simp only [Nat.add_zero] at I0
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  have ok0 := okRow hw hs hlt0
  obtain ⟨hx0, hv0, htl, hte, huA, hbN, hbL, hcO, hcS, hCc, heL, heS, hKc⟩ :=
    head_RDB ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf I0.kd
  obtain ⟨c0, B⟩ := brLay hw hs hsc K U htl hte
  have hℓ := B.len
  subst hℓ
  have hle := K.le
  have hlen22 := lenLe hw hs
  have hc0 : c0 = 3 ∨ c0 = 39 := by rcases B.c0v with h | h <;> omega
  -- direct reads
  have readAt : ∀ d, d < c0 + 32 * ww + 8 → s.row (o + d) rd = 1 →
      s.row (o + d) rb = (Pb (s.row o sN)).getD d 0 ∧ s.row (o + d) plen = (Pb (s.row o sN)).length := by
    intro d h2 hrd
    have hlt : o + d < s.rows.length := by omega
    have hI := K.ix d h2
    have hsp := dirRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) hI (by omega) hrd
    rw [(U.rows d h2).2.1] at hsp
    have := hR (o + d) hlt hrd
    rwa [hsp, K.pc d h2 sN (by decide)] at this
  -- the window roles: the target window is `e* = 0` (slot 0) or `w − 1` (slot 15)
  have hMEM0 := kField hw hs hsc K B.memU.1 B.memU.2 (by omega) (by omega) 0 (by omega)
  simp only [Nat.add_zero] at hMEM0
  have hm8 : s.row (o + c0 + 32 * ww) sMEM = 1 := (stOf_inv hMEM0.1).2.2.2.2.2.2.2.2 hMEM0.2.1
  have hww0 : 0 < ww ∨ ww = 0 := by omega
  -- the source's length, from a `MEM` read
  have hrdM : s.row (o + (c0 + 32 * ww)) rd = 1 := by
    rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]
    exact rdMem (okRow hw hs hMEM0.2.2.1) (rowLt hw hs _) (nextLt hw hs _) hMEM0.2.2.2.2.2 hm8
      (hMEM0.2.2.2.1.kd 8 (by omega)) hMEM0.1
  have hpl := (readAt (c0 + 32 * ww) (by omega) hrdM).2
  have hpM := pMEM (okRow hw hs (i := o + (c0 + 32 * ww)) (by omega)) (rowLt hw hs _)
    (by rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; exact hMEM0.1.sum) hrdM
    (by rw [show o + (c0 + 32 * ww) = o + c0 + 32 * ww by omega]; exact hm8)
  have hidx : s.row (o + (c0 + 32 * ww)) idx = 0 := by
    have := B.memU.1.idx 0 (by omega); rwa [show o + c0 + 32 * ww + 0 = o + (c0 + 32 * ww) by omega] at this
  have hsp0 : s.row (o + (c0 + 32 * ww)) spos = c0 + 32 * ww := by
    rw [dirRow (okRow hw hs (i := o + (c0 + 32 * ww)) (by omega)) (rowLt hw hs _) (nextLt hw hs _)
      (K.ix (c0 + 32 * ww) (by omega)) (by omega) hrdM, (U.rows (c0 + 32 * ww) (by omega)).2.1]
  rw [hidx, hsp0] at hpM
  have hPlen : (Pb (s.row o sN)).length = c0 + 32 * ww + 8 := by
    rw [← hpl]
    have e : ((c0 + 32 * ww + 8 : Nat) : Fp) = ((s.row (o + (c0 + 32 * ww)) plen : Nat) : Fp) := by
      rw [natCast_add]
      rw [cast0] at hpM
      grind
    exact (natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e).symm
  -- the tag: `bv` matches the layout
  have hT0 := B.pre 0 (by omega)
  simp only [Nat.add_zero] at hT0
  obtain ⟨t1, -, -, -, -, t6, -, -, t9, t10, -, -⟩ := hT0
  have htag1 : s.row o sTAG = 1 := t9.2 trivial
  have hcp0 : s.row o cp = 1 := by
    apply natv (rowLt hw hs _ _) one_lt
    rw [cpTAG ok0 (rowLt hw hs _) t1.sum htag1, show s.row o kRDB = 1 from I0.kd 0 (by omega),
      show s.row o kRDE = 0 from I0.kd 1 (by omega), show s.row o kRLP = 0 from I0.kd 2 (by omega),
      show s.row o kRBR = 0 from I0.kd 3 (by omega), show s.row o kRBI = 0 from I0.kd 5 (by omega),
      show s.row o kPT = 0 from I0.kd 11 (by omega)]; rfl
  have hrd0 : s.row o rd = 1 := rdCopy ok0 (rowLt hw hs _) (nextLt hw hs _) hq0 hcp0 t1
    (fun _ => ⟨I0.kd 4 (by omega), I0.kd 6 (by omega), I0.kd 7 (by omega), hx0⟩)
    (fun _ => ⟨I0.kd 6 (by omega), I0.kd 7 (by omega)⟩) (fun _ => I0.kd 3 (by omega)) (fun _ => hx0)
    (rdcOff ok0 (rowLt hw hs _) (nextLt hw hs _) t6)
  have hb0 := bCopyN ok0 (rowLt hw hs _) (nextLt hw hs _) hcp0 (by have := t1.bs; have := t1.sum; omega)
  have hgr0 := (gramRow ok0 (rowLt hw hs _) (nextLt hw hs _) t1.sum).1 htag1 K.pf
  have hr0 := (readAt 0 (by omega) (by simpa using hrd0)).1
  simp only [Nat.add_zero] at hr0
  rw [hb0, hr0, hsrc, brEnc] at hgr0
  have hpreL : (brPre bv cs).length = c0 := by
    obtain ⟨l1, l2⟩ := brPre_len bv cs hbv
    have : (brPre bv cs ++ ((NearSpec.Kids.hashes cs).map UInt8.toNat ++ (NearSpec.u64 m).map UInt8.toNat)).getD 0 0 =
        (brPre bv cs).getD 0 0 := by
      simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by rw [l1]; split <;> omega)]
    rw [this, l2] at hgr0
    rw [l1]
    rcases B.c0v with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> cases bv <;> simp at hgr0 ⊢ <;> omega
  have hHl : (NearSpec.Kids.hashes cs).length = 32 * ww := by
    have := congrArg List.length hsrc
    rw [hPlen, brEnc] at this
    simp only [List.length_append, List.length_map, u64_length, hpreL] at this
    omega
  -- the slot's child hash, the windows
  have hww : 0 < ww := by
    rcases (show slotOf sd = 0 ∨ slotOf sd = 15 by unfold slotOf; split <;> omega) with h | h
    · rw [h] at hslot
      obtain ⟨R, h1, -⟩ := UpsSpec.setKid_first cs c c' hslot
      have := congrArg List.length h1; simp [hc32] at this; omega
    · rw [h] at hslot
      obtain ⟨R, h1, -⟩ := UpsSpec.setKid_last c c' cs 15 hkl hslot
      have := congrArg List.length h1; simp [hc32] at this; omega
  have WF := winFlags hw hs (r := o + c0) hww (by omega) (by omega)
    (by have := (B.pre (c0 - 1) (by omega)).2.2.2.2.2.1; rwa [show o + (c0 - 1) = o + c0 - 1 by omega] at this)
    (fun e he => ⟨(B.winU e he).1, fun d hd => by
      have := (B.win (32 * e + d) (by omega)).2.2.2.2.2; rwa [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at this⟩)
    hm8 (by have := hMEM0.1.bs; have := hMEM0.1.sum; omega)
  -- the target window `e*`
  let es := if sd = 1 then ww - 1 else 0
  have role : ∀ e, e < ww → ∀ d, d < 32 → s.row (o + c0 + 32 * e + d) wfr = (if e = es then 1 else 0) ∧
      s.row (o + c0 + 32 * e + d) wn = 0 ∧
      s.row (o + c0 + 32 * e + d) rdc = s.row (o + c0 + 32 * e + d) fs * (if e = es then 1 else 0) := by
    intro e he d hd
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := B.win (32 * e + d) (by omega)
    rw [show o + c0 + (32 * e + d) = o + c0 + 32 * e + d by omega] at a1 a2 a3 a4 a5 a6
    have sl := kSel hw hs hsc K (r := o + c0 + 32 * e + d) (by omega) (by omega)
    have R := winRole (okRow hw hs a2) (rowLt hw hs _) (nextLt hw hs _) a3 i1 i4 (by omega) isd a6 sl.2.2.2.2.1
      sl.2.2.2.2.2 sl.2.1
    obtain ⟨f1, f2⟩ := WF e he d hd
    have ht : s.row (o + c0 + 32 * e + d) tgt = if e = es then 1 else 0 := by
      rw [R.1, f1, f2]
      simp only [s15V, kdOf, UKind.all, b2n, es]
      by_cases h1 : sd = 1 <;> simp [h1] <;> split <;> split <;> omega
    refine ⟨by rw [R.2.1 (Or.inl rfl), ht], by rw [R.2.2.2.2.2.1]; rfl, ?_⟩
    rw [R.2.2.2.2.2.2.1, ht, a4 UpsV3.up (by decide), hup, Nat.mul_one]
  have hes : es < ww := by simp only [es]; split <;> omega
  -- copied rows: everything before `MEM` but the target window
  have copyAt : ∀ d, d < c0 + 32 * ww → (d < c0 + 32 * es ∨ c0 + 32 * es + 32 ≤ d) →
      s.row (o + d) cp = 1 ∧ s.row (o + d) rd = 1 ∧
      (s.row (o + d) sBM = 0 ∨ (s.row (o + d) ba0 = 0 ∧ s.row (o + d) ba1 = 0)) ∧
      s.row (o + d) spos = d ∧ s.row (o + d) sN = s.row o sN := by
    intro d hd hne
    have hlt : o + d < s.rows.length := by omega
    have hok := okRow hw hs hlt
    have hI := K.ix d (by omega)
    have hpc := K.pc d (by omega)
    have hq := K.qb d (by omega)
    have hx : s.row (o + d) xcp = 0 := by rw [hpc xcp (by decide), hx0]
    have hba : s.row (o + d) ba0 = 0 ∧ s.row (o + d) ba1 = 0 := by
      have := kSel hw hs hsc K (r := o + d) (by omega) (by omega)
      rw [this.2.2.1, this.2.2.2.1]; simp [ba0V, ba1V, kdOf, UKind.all, b2n]
    obtain ⟨hcp, hoh, hrdc⟩ : s.row (o + d) cp = 1 ∧ OneHot (s.row (o + d)) ∧ s.row (o + d) rdc = 0 := by
      rcases Nat.lt_or_ge d c0 with h | h
      · obtain ⟨a1, -, -, -, -, a6, a7, a8, -⟩ := B.pre d h
        have hs1 := a1.sum; have hb := a1.bs
        refine ⟨?_, a1, rdcOff hok (rowLt hw hs _) (nextLt hw hs _) a6⟩
        apply natv (rowLt hw hs _ _) one_lt
        by_cases ht : s.row (o + d) sTAG = 1
        · rw [cpTAG hok (rowLt hw hs _) hs1 ht, show s.row (o + d) kRDB = 1 from hI.kd 0 (by omega),
            show s.row (o + d) kRDE = 0 from hI.kd 1 (by omega), show s.row (o + d) kRLP = 0 from hI.kd 2 (by omega),
            show s.row (o + d) kRBR = 0 from hI.kd 3 (by omega), show s.row (o + d) kRBI = 0 from hI.kd 5 (by omega),
            show s.row (o + d) kPT = 0 from hI.kd 11 (by omega)]; rfl
        by_cases hb' : s.row (o + d) sBM = 1
        · rw [cpBM hok (rowLt hw hs _) hs1 hb', show s.row (o + d) kRDB = 1 from hI.kd 0 (by omega),
            show s.row (o + d) kRBR = 0 from hI.kd 3 (by omega), show s.row (o + d) kRBV = 0 from hI.kd 4 (by omega),
            show s.row (o + d) kRBI = 0 from hI.kd 5 (by omega)]; rfl
        by_cases hv : s.row (o + d) sVLEN = 1
        · rw [cpVLEN hok (rowLt hw hs _) hs1 hv, hpc vcp (by decide), hv0]
        · have hvh : s.row (o + d) sVH = 1 := by omega
          rw [cpVH hok (rowLt hw hs _) hs1 hvh, hpc vcp (by decide), hv0]
      · obtain ⟨a1, -, -, -, -, a6⟩ := B.win (d - c0) (by omega)
        rw [show o + c0 + (d - c0) = o + d by omega] at a1 a6
        have r := role ((d - c0) / 32) (by omega) ((d - c0) % 32) (by omega)
        rw [show o + c0 + 32 * ((d - c0) / 32) + (d - c0) % 32 = o + d by omega] at r
        have hne' : ¬ ((d - c0) / 32 = es) := by omega
        rw [if_neg hne'] at r
        refine ⟨?_, a1, by rw [r.2.2]; simp⟩
        apply natv (rowLt hw hs _ _) one_lt
        rw [cpCH hok (rowLt hw hs _) a1.sum a6, r.1]; rfl
    have hrd : s.row (o + d) rd = 1 := rdCopy hok (rowLt hw hs _) (nextLt hw hs _) hq hcp hoh
      (fun _ => ⟨hI.kd 4 (by omega), hI.kd 6 (by omega), hI.kd 7 (by omega), hx⟩)
      (fun _ => ⟨hI.kd 6 (by omega), hI.kd 7 (by omega)⟩) (fun _ => hI.kd 3 (by omega)) (fun _ => hx) hrdc
    refine ⟨hcp, hrd, Or.inr hba, ?_, hpc sN (by decide)⟩
    rw [dirRow hok (rowLt hw hs _) (nextLt hw hs _) hI (by omega) hrd]
    exact (U.rows d (by omega)).2.1
  have cA := copyRunB hw hs Pb hR (r := o) (n := c0 + 32 * es) (δ := 0) (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by simpa using copyAt d (by omega) (Or.inl hd))
  have cB := copyRunB hw hs Pb hR (r := o + (c0 + 32 * es + 32)) (n := 32 * (ww - es - 1)) (δ := c0 + 32 * es + 32)
    (N := s.row o sN) (by omega) (by omega)
    (fun d hd => by
      have := copyAt (c0 + 32 * es + 32 + d) (by omega) (Or.inr (by omega))
      rwa [show o + (c0 + 32 * es + 32 + d) = o + (c0 + 32 * es + 32) + d by omega] at this)
  -- the target window (fresh)
  have hWe := B.winU es hes
  have FC := kField hw hs hsc K hWe.1 hWe.2 (by omega) (by omega)
  have chU : ∀ d, d < 32 → s.row (o + c0 + 32 * es + d) sCH = 1 ∧ s.row (o + c0 + 32 * es + d) wfr = 1 ∧
      s.row (o + c0 + 32 * es + d) wn = 0 := by
    intro d hd
    have F := FC d hd
    have r := role es hes d hd
    rw [if_pos rfl] at r
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
  have hjm : s.row o jm = k := by
    rw [jmRow ok0 (rowLt hw hs _) (nextLt hw hs _) K.pf (by
      rw [show s.row o kRDB = 1 from I0.kd 0 (by omega), show s.row o kRDE = 0 from I0.kd 1 (by omega),
        show s.row o kWEX = 0 from I0.kd 9 (by omega), show s.row o kPT = 0 from I0.kd 11 (by omega)]) (by omega), hj]
    omega
  have hdI := dIj_nat (rowLt hw hs _ _) (dCHm (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
  have hdL := natv (rowLt hw hs _ _) (rowLt hw hs _ _) (dCHml (okRow hw hs hr3) (rowLt hw hs _) F0.1.sum hgD c0'.1 c0'.2.2)
  rw [hsc _ hr3 tau (by decide), F0.2.2.2.2.1 jm (by decide), hjm] at hdI
  rw [F0.2.2.2.2.1 clen (by decide)] at hdL
  exact ⟨_, hr3, hgD, hdI, hdL⟩

end

end ZkFormal.NearV3.UpsRows

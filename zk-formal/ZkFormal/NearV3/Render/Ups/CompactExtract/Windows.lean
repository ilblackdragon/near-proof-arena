import ZkFormal.NearV3.Render.Ups.CompactExtract.WinRows
import ZkFormal.NearV3.Render.Ups.CompactExtract.Plan
import ZkFormal.NearV3.Extract.Ups.Windows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- Every row of a part carries the indices. -/
theorem partIxRow (k : Nat) (hk : k < ps.length) (d : Nat) (hd : d < ps[k].2) :
    IxOf (s.row (ps[k].1 + d)) ci ti di si (kd k) (sdx k) := by
  obtain ⟨-, U⟩ := hL.part k hk
  have hr := U.rows d hd
  have hlt : ps[k].1 + d < s.rows.length := by have := U.le; omega
  obtain ⟨c1, c2, c3, c4⟩ := hP.seg _ hlt
  obtain ⟨-, -, pk, psd⟩ := hP.part k hk
  exact ⟨c1, c2, c3, c4, fun m hm => (hr.2.2.2.2 _ (kcol_pc m hm)).trans (pk m hm),
    fun m hm => (hr.2.2.2.2 _ (sd_pc m hm)).trans (psd m hm)⟩

/-- **The derived part constants** on every row of a part. -/
theorem partSelAll (k : Nat) (hk : k < ps.length) (d : Nat) (hd : d < ps[k].2) :
    let C := s.row (ps[k].1 + d)
    C vcp = vcpV ci (kd k) ∧ C xcp = xcpV ci (kd k) ∧ C ba0 = ba0V si (kd k) ∧ C ba1 = ba1V si (kd k) ∧
    C spY1 = spY1V ci si (kd k) ∧ C spY2 = spY2V ci si (kd k) := by
  obtain ⟨-, U⟩ := hL.part k hk
  have hr := U.rows d hd
  have h0 := partIxRow hw hs hL hP k hk 0 U.pos
  rw [Nat.add_zero] at h0
  obtain ⟨hlt, hq, hpf⟩ := pFirst hw hs hL k hk
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  obtain ⟨k1, k2, -, -⟩ := hP.part k hk
  have S := partSel (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) h0 i1 i4 k1 k2 hpf
  intro C
  simp only [C]
  rw [hr.2.2.2.2 vcp (by decide), hr.2.2.2.2 xcp (by decide), hr.2.2.2.2 ba0 (by decide), hr.2.2.2.2 ba1 (by decide),
    hr.2.2.2.2 spY1 (by decide), hr.2.2.2.2 spY2 (by decide)]
  exact S

end

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **Window fields** of a part `(o, ℓ)` with fields `fl`: length 32, `fw` = the previous field
is not a window, `lastw` = `MEM` follows, the window constants are those of the first row,
which has the roles `WinRoleP`. -/
theorem windowsOf {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w)
    {ci ti di si ki sdi : Nat} (i1 : ci < 11) (i4 : si < 3) (k1 : ki < 12) (k2 : sdi < 3)
    (hI : ∀ d, d < ℓ → IxOf (s.row (o + d)) ci ti di si ki sdi)
    (hS : ∀ d, d < ℓ → s.row (o + d) xcp = xcpV ci ki ∧ s.row (o + d) spY1 = spY1V ci si ki ∧
      s.row (o + d) spY2 = spY2V ci si ki) :
    WinsOK s o fl ci si ki sdi := by
  intro q hq h7
  have hqF := U.fields q hq
  have hU := hqF.1
  have hrows := U.rows
  have hq' := fun d (hd : d < ℓ) => (⟨(hrows d hd).1, (hrows d hd).2.2.1, (hrows d hd).2.2.2.1⟩ :
    s.row (o + d) qb = 1 ∧ (s.row (o + d) pf = 1 ↔ d = 0) ∧ (s.row (o + d) pl = 1 ↔ d + 1 = ℓ))
  have hpc := fun d (hd : d < ℓ) => (hrows d hd).2.2.2.2
  have hm := lenLe hw hs
  -- the field's state and length
  have hlen : fl[q].2 = 32 := by
    have := fLen hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq
    rw [this, h7]; rfl
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; have := fFirst hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields
      omega
    · exact h
  have hstart : ∀ d, d < 32 → stOf (s.row (o + fl[q].1 + d)) = 7 ∧ s.row (o + fl[q].1 + d) sCH = 1 ∧
      (s.row (o + fl[q].1 + d) fe = 1 ↔ d = 31) ∧ o + fl[q].1 + d < s.rows.length := by
    intro d hd
    have st := fun x (hx : x ∈ states) => hU.st d (by omega) x hx
    have hrow : o + fl[q].1 + d < s.rows.length := by have := hqF.2; have := U.le; omega
    have hqb : s.row (o + fl[q].1 + d) qb = 1 := by
      have := (hq' (fl[q].1 + d) (by have := hqF.2; omega)).1; rwa [← Nat.add_assoc] at this
    have hoh := oneHot hw hs hrow hqb
    have e7 : stOf (s.row (o + fl[q].1 + d)) = 7 := by
      unfold stOf
      rw [st sHPL (by simp [states]), st sHPF (by simp [states]), st sKEY (by simp [states]),
        st sVLEN (by simp [states]), st sVH (by simp [states]), st sBM (by simp [states]),
        st sCH (by simp [states]), st sMEM (by simp [states])]
      exact h7
    exact ⟨e7, (stOf_inv hoh).2.2.2.2.2.2.2.1 e7, by rw [hU.fe d (by omega)]; omega, hrow⟩
  -- the previous field ends right before
  have hprev := consec_get fl 0 U.consec (q - 1) (by omega)
  simp only [show q - 1 + 1 = q from by omega] at hprev
  have hPq := U.fields (q - 1) (by omega)
  obtain ⟨hre, hst, hfe, -, hoh⟩ := fEndRow hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields
    (q := q - 1) (by omega) (re := o + fl[q - 1].1 + fl[q - 1].2 - 1) rfl
  have hpos' := hPq.1.pos
  have hre1 : o + fl[q - 1].1 + fl[q - 1].2 - 1 + 1 = o + fl[q].1 := by omega
  obtain ⟨e0, c0, -, hlt0⟩ := hstart 0 (by omega)
  rw [Nat.add_zero] at e0 c0 hlt0
  have W := winStep (okIn hw hs (by rw [hre1]; exact hlt0)) (rowLt hw hs _) (rowLt hw hs _)
  rw [hre1] at W
  have fw0 : s.row (o + fl[q].1) fw = (if stOf (s.row (o + (fl[q - 1]'(by omega)).1)) = 7 then 0 else 1) := by
    rw [← hst]
    by_cases h : stOf (s.row (o + fl[q - 1].1 + fl[q - 1].2 - 1)) = 7
    · rw [if_pos h]
      exact W.2.2.1 ((stOf_inv hoh).2.2.2.2.2.2.2.1 h) hfe c0
    · rw [if_neg h]
      have : s.row (o + fl[q - 1].1 + fl[q - 1].2 - 1) sCH = 0 := by
        have := hoh.bs; have := (stOf_one hoh).2.2.2.2.2.2.2.1
        rcases Nat.lt_or_ge (s.row (o + fl[q - 1].1 + fl[q - 1].2 - 1) sCH) 1 with h' | h'
        · omega
        · exact absurd (this (by omega)) h
      exact W.1 this c0
  -- the last row: `lastw` from what follows
  obtain ⟨e31, c31, f31, hlt31⟩ := hstart 31 (by omega)
  have hq1 : q + 1 < fl.length := by
    rcases Nat.lt_or_ge (q + 1) fl.length with h | h
    · exact h
    · have := (memLast hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq).2 (by omega)
      omega
  have hnext := consec_get fl 0 U.consec q hq1
  have hlast1 : o + fl[q].1 + 31 + 1 = o + fl[q + 1].1 := by omega
  have hnlt : o + fl[q + 1].1 < s.rows.length := by
    have := (U.fields (q + 1) hq1).2; have := (U.fields (q + 1) hq1).1.pos; have := U.le; omega
  have W31 := winStep (okIn hw hs (by rw [hlast1]; exact hnlt)) (rowLt hw hs _) (rowLt hw hs _)
  rw [hlast1] at W31
  have lw31 : s.row (o + fl[q].1 + 31) lastw = (if q + 2 = fl.length then 1 else 0) := by
    rw [W31.2.2.2 c31 (f31.2 rfl)]
    have hqb : s.row (o + fl[q + 1].1) qb = 1 := by
      exact (hq' (fl[q + 1].1) (by have := (U.fields (q + 1) hq1).2; have := (U.fields (q+1) hq1).1.pos; omega)).1
    have hoh1 := oneHot hw hs hnlt hqb
    have ml := memLast hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq1
    by_cases h : q + 2 = fl.length
    · rw [if_pos h]; exact (stOf_inv hoh1).2.2.2.2.2.2.2.2 (ml.2 (by omega))
    · rw [if_neg h]
      have := hoh1.bs; have := (stOf_one hoh1).2.2.2.2.2.2.2.2
      rcases Nat.lt_or_ge (s.row (o + fl[q + 1].1) sMEM) 1 with h' | h'
      · omega
      · exact absurd (ml.1 (this (by omega))) (by omega)
  -- constants inside the window
  have inside : ∀ d, d < 31 → ∀ x ∈ [fw, lastw, wfr, tgt, wy, wn],
      s.row (o + fl[q].1 + (d + 1)) x = s.row (o + fl[q].1 + d) x := by
    intro d hd x hx
    obtain ⟨-, cd, fd, hltd⟩ := hstart d (by omega)
    have Wd := winStep (okIn hw hs (by have := (hstart (d + 1) (by omega)).2.2.2; omega)) (rowLt hw hs _) (rowLt hw hs _)
    have hfe0 : s.row (o + fl[q].1 + d) fe = 0 := by
      have := le1 (rowBool (okRow hw hs hltd) (rowLt hw hs _) (x := fe) (by decide))
      rcases Nat.lt_or_ge (s.row (o + fl[q].1 + d) fe) 1 with h' | h'
      · omega
      · exact absurd (fd.1 (by omega)) (by omega)
    have := Wd.2.1 cd hfe0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [show o + fl[q].1 + (d + 1) = o + fl[q].1 + d + 1 by omega]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2.1
    · exact this.2.2.2.1
    · exact this.2.2.2.2.1
    · exact this.2.2.2.2.2
  have toFirst : ∀ x ∈ [fw, lastw, wfr, tgt, wy, wn], ∀ d, d < 32 →
      s.row (o + fl[q].1 + d) x = s.row (o + fl[q].1) x := by
    intro x hx d
    induction d with
    | zero => intro _; rfl
    | succ d ih => intro hd; rw [inside d (by omega) x hx, ih (by omega)]
  -- roles on the first row
  have hdk : fl[q].1 < ℓ := by have := hqF.2; have := hU.pos; omega
  have hS0 := hS _ hdk
  have R := winRole (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _) (hI _ hdk) i1 i4 k1 k2 c0 hS0.2.1 hS0.2.2
    hS0.1
  refine ⟨hlen, hq0, fun d hd => ⟨?_, ?_, toFirst wfr (by simp) d hd, toFirst tgt (by simp) d hd,
    toFirst wy (by simp) d hd, toFirst wn (by simp) d hd⟩, R⟩
  · rw [toFirst fw (by simp) d hd]; exact fw0
  · rw [toFirst lastw (by simp) d hd, ← toFirst lastw (by simp) 31 (by omega)]; exact lw31

end

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **Window roles of part `k`** (layer 2). -/
theorem ups_windows (k : Nat) (hk : k < ps.length) :
    WinsOK s ps[k].1 (fls[k]'(by rw [hL.lens.1]; exact hk)) ci si (kd k) (sdx k) := by
  obtain ⟨-, U⟩ := hL.part k hk
  obtain ⟨i1, -, -, i4⟩ := hP.ix
  obtain ⟨k1, k2, -, -⟩ := hP.part k hk
  exact windowsOf hw hs U i1 i4 k1 k2 (fun d hd => partIxRow hw hs hL hP k hk d hd)
    (fun d hd => let S := partSelAll hw hs hL hP k hk d hd; ⟨S.2.1, S.2.2.2.2.1, S.2.2.2.2.2⟩)

end

end ZkFormal.NearV3.Render.UpsRelay.Extract

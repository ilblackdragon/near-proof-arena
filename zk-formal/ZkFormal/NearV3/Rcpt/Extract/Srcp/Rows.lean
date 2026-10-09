import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Rcpt.Tables.Srcp

/-!
# ZkFormal.NearV3.Rcpt.Extract.Srcp.Rows — row facts of `srcpV3`

Every constraint of `srcpV3` as a fact about cells (rows `r`, next row `r + 1 < H`), and the
unit decomposition: `act = rt ∨ sg`, units start at `rt ∨ sf` and end at `rt ∨ sl`
(`segFacts`).  A root row is a unit of one row; a leaf / path segment is a unit of 32 / 64 rows.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt h

def isOne (tr : Trace Fp) (tt x : Nat) (r : Nat) : Bool := decide (tr.cell tt r x = 1)

def bools : List Nat := [rt, sg, lf, wf, wl, wn, sf, sl, dup, dir, aw, gD, gz]

section
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem con {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ SrcpV3.constraints) :
    e.eval tr tt r pub = 0 := hL.constr r hr e he

theorem isBool {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ bools) :
    tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx)))))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem zero_of_not_one {r : Nat} (hr : r < tr.height tt) {x : Nat} (hx : x ∈ bools)
    (h : isOne tr tt x r = false) : tr.cell tt r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

/-- Row-local facts. -/
theorem local_ {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r rt * tr.cell tt r sg = 0 ∧
    (tr.cell tt r rt = 1 → tr.cell tt r dup = 1 → tr.cell tt r L = 12) ∧
    (tr.cell tt r wf = 1 → tr.cell tt r sg = 1 ∧ tr.cell tt r pw = 0) ∧
    (tr.cell tt r wl = 1 → tr.cell tt r sg = 1 ∧ tr.cell tt r pw = 31) ∧
    tr.cell tt r sf = tr.cell tt r wf * (1 - tr.cell tt r wn) ∧
    tr.cell tt r sl = tr.cell tt r wl * (tr.cell tt r wn + tr.cell tt r lf) ∧
    (tr.cell tt r lf = 1 → tr.cell tt r wn = 0 ∧ tr.cell tt r dir = 0 ∧ tr.cell tt r aw = 1 ∧
      tr.cell tt r sg = 1) ∧
    (tr.cell tt r sg = 1 → tr.cell tt r aw = tr.cell tt r lf + (1 - tr.cell tt r lf) *
      (tr.cell tt r wn + tr.cell tt r dir - 2 * (tr.cell tt r wn * tr.cell tt r dir))) ∧
    (tr.cell tt r sg = 1 → tr.cell tt r aw = 1 → tr.cell tt r b = tr.cell tt r (reg 0)) ∧
    tr.cell tt r gD = tr.cell tt r rt + tr.cell tt r wf * tr.cell tt r aw ∧
    (tr.cell tt r rt = 1 → tr.cell tt r cId = (K_SRC : Fp) + 16 * tr.cell tt r qe ∧
      tr.cell tt r cLen = tr.cell tt r le) ∧
    (tr.cell tt r wf = 1 → tr.cell tt r lf = 1 → tr.cell tt r cId = (K_RC : Fp) + 16 * tr.cell tt r j ∧
      tr.cell tt r cLen = tr.cell tt r L) ∧
    (tr.cell tt r wf = 1 → tr.cell tt r aw = 1 → tr.cell tt r lf = 0 →
      tr.cell tt r cId = (K_SRC : Fp) + 16 * (tr.cell tt r q - 1) ∧ tr.cell tt r cLen = tr.cell tt r pl) ∧
    (tr.cell tt r gz = 1 → tr.cell tt r sl = 1) := by
  have h1 := con hL hr (e := .mul (c rt) (c sg)) (by simp [SrcpV3.constraints])
  have h2 := con hL hr (e := mul3 (c rt) (c dup) (sub (c L) (k 12))) (by simp [SrcpV3.constraints])
  have h3 := con hL hr (e := .mul (c wf) (Dsl.not (c sg))) (by simp [SrcpV3.constraints])
  have h4 := con hL hr (e := .mul (c wl) (Dsl.not (c sg))) (by simp [SrcpV3.constraints])
  have h5 := con hL hr (e := .mul (c wf) (c pw)) (by simp [SrcpV3.constraints])
  have h6 := con hL hr (e := .mul (c wl) (sub (c pw) (k 31))) (by simp [SrcpV3.constraints])
  have h7 := con hL hr (e := sub (c sf) (.mul (c wf) (Dsl.not (c wn)))) (by simp [SrcpV3.constraints])
  have h8 := con hL hr (e := sub (c sl) (.mul (c wl) (.add (c wn) (c lf)))) (by simp [SrcpV3.constraints])
  have h9 := con hL hr (e := .mul (c lf) (c wn)) (by simp [SrcpV3.constraints])
  have h10 := con hL hr (e := .mul (c lf) (c dir)) (by simp [SrcpV3.constraints])
  have h11 := con hL hr (e := .mul (c lf) (Dsl.not (c aw))) (by simp [SrcpV3.constraints])
  have h12 := con hL hr (e := .mul (c lf) (Dsl.not (c sg))) (by simp [SrcpV3.constraints])
  have h13 := con hL hr (e := .mul (c sg) (sub (c aw) (.add (c lf) (.mul (Dsl.not (c lf))
      (sub (.add (c wn) (c dir)) (smul 2 (.mul (c wn) (c dir)))))))) (by simp [SrcpV3.constraints])
  have h14 := con hL hr (e := mul3 (c sg) (c aw) (sub (c b) (c (reg 0)))) (by simp [SrcpV3.constraints])
  have h15 := con hL hr (e := sub (c gD) (.add (c rt) (.mul (c wf) (c aw)))) (by simp [SrcpV3.constraints])
  have h16 := con hL hr (e := .mul (c rt) (sub (c cId) (mid K_SRC (c qe)))) (by simp [SrcpV3.constraints])
  have h17 := con hL hr (e := .mul (c rt) (sub (c cLen) (c le))) (by simp [SrcpV3.constraints])
  have h18 := con hL hr (e := mul3 (c wf) (c lf) (sub (c cId) (mid K_RC (c j)))) (by simp [SrcpV3.constraints])
  have h19 := con hL hr (e := mul3 (c wf) (c lf) (sub (c cLen) (c L))) (by simp [SrcpV3.constraints])
  have h20 := con hL hr (e := .mul (mul3 (c wf) (c aw) (Dsl.not (c lf))) (sub (c cId) (mid K_SRC (sub (c q) (k 1)))))
    (by simp [SrcpV3.constraints])
  have h21 := con hL hr (e := .mul (mul3 (c wf) (c aw) (Dsl.not (c lf))) (sub (c cLen) (c pl)))
    (by simp [SrcpV3.constraints])
  have h22 := con hL hr (e := .mul (c gz) (Dsl.not (c sl))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_smul, eval_mid] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
  refine ⟨h1, fun ha hd => ?_, fun h => ?_, fun h => ?_, by grind, by grind, fun h => ?_, fun h => ?_,
    fun h1' h2' => ?_, by grind, fun h => ?_, fun ha hb' => ?_, fun ha hb' hc' => ?_, fun h => ?_⟩
  · rw [ha, hd] at h2; grind
  · rw [h] at h3 h5; exact ⟨by grind, by grind⟩
  · rw [h] at h4 h6; exact ⟨by grind, by grind⟩
  · rw [h] at h9 h10 h11 h12; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h] at h13; grind
  · rw [h1', h2'] at h14; grind
  · rw [h] at h16 h17; exact ⟨by grind, by grind⟩
  · rw [ha, hb'] at h18 h19; exact ⟨by grind, by grind⟩
  · rw [ha, hb', hc'] at h20 h21; exact ⟨by grind, by grind⟩
  · rw [h] at h22; grind

/-- First row: the root row of list 0. -/
theorem row0 (h0 : 0 < tr.height tt) :
    tr.cell tt 0 rt = 1 ∧ tr.cell tt 0 j = 0 ∧ tr.cell tt 0 q = 0 ∧ tr.cell tt 0 sz = tr.cell tt 0 L := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c rt))) (by simp [SrcpV3.constraints])
  have h2 := con hL h0 (e := .mul .isFirst (c j)) (by simp [SrcpV3.constraints])
  have h3 := con hL h0 (e := .mul .isFirst (c q)) (by simp [SrcpV3.constraints])
  have h4 := con hL h0 (e := .mul .isFirst (sub (c sz) (c L))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_isFirst, if_pos rfl] at h1 h2 h3 h4
  exact ⟨by grind, by grind, by grind, by grind⟩

/-- Last row: not a root row; inside a segment only at its end; `sl ⇒ gz`. -/
theorem lastRow (h0 : 0 < tr.height tt) :
    tr.cell tt (tr.height tt - 1) rt = 0 ∧
    (tr.cell tt (tr.height tt - 1) sg = 1 → tr.cell tt (tr.height tt - 1) sl = 1) ∧
    (tr.cell tt (tr.height tt - 1) sl = 1 → tr.cell tt (tr.height tt - 1) gz = 1) := by
  have hr : tr.height tt - 1 < tr.height tt := by omega
  have hl : tr.height tt - 1 + 1 = tr.height tt := by omega
  have h1 := con hL hr (e := .mul .isLast (c rt)) (by simp [SrcpV3.constraints])
  have h2 := con hL hr (e := .mul .isLast (.mul (c sg) (Dsl.not (c sl)))) (by simp [SrcpV3.constraints])
  have h3 := con hL hr (e := .mul .isLast (.mul (c sl) (Dsl.not (c gz)))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isLast, if_pos hl] at h1 h2 h3
  refine ⟨by grind, fun h => ?_, fun h => ?_⟩
  · rw [h] at h2; grind
  · rw [h] at h3; grind

/-- Root row followed by the leaf segment of its list. -/
theorem afterRoot {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r rt = 1) :
    tr.cell tt (r + 1) sg = 1 ∧ tr.cell tt (r + 1) lf = 1 ∧ tr.cell tt (r + 1) sf = 1 ∧
    tr.cell tt (r + 1) q = tr.cell tt r q + 1 ∧ ∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := .mul (c rt) (Dsl.not (n sg))) (by simp [SrcpV3.constraints])
  have h2 := con hL hr' (e := .mul (c rt) (Dsl.not (n lf))) (by simp [SrcpV3.constraints])
  have h3 := con hL hr' (e := .mul (c rt) (Dsl.not (n sf))) (by simp [SrcpV3.constraints])
  have h4 := con hL hr' (e := .mul (c rt) (sub (n q) (.add (c q) (k 1)))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, nxt hr, ha] at h1 h2 h3 h4
  refine ⟨by grind, by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL hr' (e := Expr.mul (c rt) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun x => Expr.mul (c rt) (sub (n x) (c x))) hx))))))
  simp only [eval_mul, eval_c, eval_n, eval_sub, nxt hr, ha] at h5
  grind

/-- The root row is never the last row. -/
theorem root_not_last {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r rt = 1) : r + 1 < tr.height tt := by
  rcases Nat.lt_or_ge (r + 1) (tr.height tt) with h | h
  · exact h
  · exfalso
    have := (lastRow hL (by omega)).1
    rw [show tr.height tt - 1 = r by omega, ha] at this
    exact fp_one_ne_zero this

/-- Inside a segment. -/
theorem inSeg {r : Nat} (hr : r + 1 < tr.height tt) (hs : tr.cell tt r sg = 1) (hl : tr.cell tt r sl = 0) :
    tr.cell tt (r + 1) sg = 1 ∧ tr.cell tt (r + 1) rt = 0 ∧
    (∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x) ∧
    (∀ x ∈ segConst, tr.cell tt (r + 1) x = tr.cell tt r x) := by
  have hr' : r < tr.height tt := by omega
  have k1 := fun x (hx : x ∈ listConst) => con hL hr' (e := mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem
      (f := fun x => mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) hx)))))
  have k2 := fun x (hx : x ∈ segConst) => con hL hr' (e := mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inr (List.mem_map_of_mem (f := fun x => mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) hx)))
  -- the next row is active and a segment row
  have hw := isBool hL hr' (x := wl) (by simp [bools])
  have hn : tr.cell tt (r + 1) sg = 1 := by
    rcases hw with hw | hw
    · have h1 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (Dsl.not (n sg))) (by simp [SrcpV3.constraints])
      simp only [eval_mul3, eval_c, eval_n, eval_not, nxt hr, hs, hw] at h1; grind
    · have h1 := con hL hr' (e := mul3 (c wl) (Dsl.not (c sl)) (Dsl.not (n sg))) (by simp [SrcpV3.constraints])
      simp only [eval_mul3, eval_c, eval_n, eval_not, nxt hr, hl, hw] at h1; grind
  have hrt : tr.cell tt (r + 1) rt = 0 := by
    have := (local_ hL (r := r + 1) hr).1; rw [hn] at this; grind
  refine ⟨hn, hrt, fun x hx => ?_, fun x hx => ?_⟩
  · have := k1 x hx; simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, nxt hr, hs, hl] at this; grind
  · have := k2 x hx; simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, nxt hr, hs, hl] at this; grind

/-- Inside a window. -/
theorem inWin {r : Nat} (hr : r + 1 < tr.height tt) (hs : tr.cell tt r sg = 1) (hw : tr.cell tt r wl = 0) :
    tr.cell tt (r + 1) wf = 0 ∧ tr.cell tt (r + 1) pw = tr.cell tt r pw + 1 ∧
    tr.cell tt (r + 1) wn = tr.cell tt r wn ∧
    ∀ x, x < 31 → tr.cell tt (r + 1) (reg x) = tr.cell tt r (reg (x + 1)) := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (n wf)) (by simp [SrcpV3.constraints])
  have h2 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n pw) (.add (c pw) (k 1))))
    (by simp [SrcpV3.constraints])
  have h3 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n wn) (c wn))) (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, nxt hr, hs, hw] at h1 h2 h3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_⟩
  have h4 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n (reg x)) (c (reg (x + 1))))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inr (List.mem_map_of_mem (f := fun x => mul3 (c sg) (Dsl.not (c wl))
      (sub (n (reg x)) (c (reg (x + 1))))) (List.mem_range.2 hx)))
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, nxt hr, hs, hw] at h4
  grind

/-- From the first window of a path segment to the second. -/
theorem winSwitch {r : Nat} (hr : r + 1 < tr.height tt) (hw : tr.cell tt r wl = 1) (hl : tr.cell tt r sl = 0) :
    tr.cell tt (r + 1) wf = 1 ∧ tr.cell tt (r + 1) wn = 1 := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c wl) (Dsl.not (c sl)) (Dsl.not (n wf))) (by simp [SrcpV3.constraints])
  have h2 := con hL hr' (e := mul3 (c wl) (Dsl.not (c sl)) (Dsl.not (n wn))) (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, nxt hr, hw, hl] at h1 h2
  exact ⟨by grind, by grind⟩

/-- After a segment: a path segment of the same list. -/
theorem afterSegSg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r sl = 1)
    (hs : tr.cell tt (r + 1) sg = 1) :
    tr.cell tt (r + 1) sf = 1 ∧ tr.cell tt (r + 1) lf = 0 ∧ tr.cell tt (r + 1) q = tr.cell tt r q + 1 ∧
    tr.cell tt (r + 1) pl = 64 - 32 * tr.cell tt r lf ∧
    ∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 (c sl) (n sg) (Dsl.not (n sf))) (by simp [SrcpV3.constraints])
  have h2 := con hL hr' (e := mul3 (c sl) (n sg) (n lf)) (by simp [SrcpV3.constraints])
  have h3 := con hL hr' (e := mul3 (c sl) (n sg) (sub (n q) (.add (c q) (k 1)))) (by simp [SrcpV3.constraints])
  have h4 := con hL hr' (e := mul3 (c sl) (n sg) (sub (n pl) (sub (k 64) (smul 32 (c lf)))))
    (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_smul, nxt hr, hl, hs]
    at h1 h2 h3 h4
  refine ⟨by grind, by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL hr' (e := mul3 (c sl) (n sg) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun x => mul3 (c sl) (n sg) (sub (n x) (c x))) hx))))
  simp only [eval_mul3, eval_c, eval_n, eval_sub, nxt hr, hl, hs] at h5
  grind

/-- After a segment: the root row of the next list. -/
theorem afterSegRt {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r sl = 1)
    (ha : tr.cell tt (r + 1) rt = 1) :
    tr.cell tt (r + 1) q = tr.cell tt r q ∧ tr.cell tt (r + 1) j = tr.cell tt r j + 1 := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := .mul .isTransition (mul3 (c sl) (n rt) (sub (n q) (c q))))
    (by simp [SrcpV3.constraints])
  have h2 := con hL hr' (e := .mul .isTransition (mul3 (c sl) (n rt) (sub (n j) (.add (c j) (k 1)))))
    (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_sub, eval_add, eval_k, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega), hl, ha] at h1 h2
  exact ⟨by grind, by grind⟩

/-- End of a list: the segment's message is the list's last one. -/
theorem listEnd {r : Nat} (hr : r < tr.height tt) (hl : tr.cell tt r sl = 1)
    (hn : tr.cell tt ((r + 1) % tr.height tt) sg = 0) :
    tr.cell tt r q = tr.cell tt r qe ∧ tr.cell tt r le = 64 - 32 * tr.cell tt r lf := by
  have h1 := con hL hr (e := mul3 (c sl) (Dsl.not (n sg)) (sub (c q) (c qe))) (by simp [SrcpV3.constraints])
  have h2 := con hL hr (e := mul3 (c sl) (Dsl.not (n sg)) (sub (c le) (sub (k 64) (smul 32 (c lf)))))
    (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_k, eval_smul, hl, hn] at h1 h2
  exact ⟨by grind, by grind⟩

/-- Padding stays padding. -/
theorem padStep {r : Nat} (hr : r + 1 < tr.height tt) (ha : tr.cell tt r rt = 0) (hs : tr.cell tt r sg = 0) :
    tr.cell tt (r + 1) rt = 0 ∧ tr.cell tt (r + 1) sg = 0 := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := mul3 .isTransition (Dsl.not actE) (.add (n rt) (n sg))) (by simp [SrcpV3.constraints])
  simp only [eval_mul3, actE, eval_c, eval_n, eval_not, eval_add, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega), ha, hs] at h1
  have l1 := (local_ hL (r := r + 1) hr).1
  have c1 := isBool hL hr (x := rt) (by simp [bools])
  have c2 := isBool hL hr (x := sg) (by simp [bools])
  rcases c1 with h | h <;> rcases c2 with h' | h' <;> rw [h, h'] at h1 l1 <;>
    first | exact ⟨h, h'⟩ | (exfalso; grind)

/-- The running size. -/
theorem szStep {r : Nat} (hr : r + 1 < tr.height tt) :
    tr.cell tt (r + 1) sz = tr.cell tt r sz + tr.cell tt (r + 1) rt * tr.cell tt (r + 1) L +
      33 * (tr.cell tt (r + 1) sf * tr.cell tt (r + 1) sg * (1 - tr.cell tt (r + 1) lf)) := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := .mul .isTransition (sub (n sz) (sum [c sz, .mul (n rt) (n L),
      smul 33 (mul3 (n sf) (n sg) (Dsl.not (n lf)))]))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_sum_cons, eval_sum_nil, eval_smul,
    eval_isTransition, nxt hr, if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  grind

/-- The `SIZE` gate: on a segment end, `gz` iff the next row is not active. -/
theorem gzStep {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r sl = 1) :
    (tr.cell tt r gz = 1 ↔ tr.cell tt (r + 1) rt + tr.cell tt (r + 1) sg = 0) := by
  have hr' : r < tr.height tt := by omega
  have h1 := con hL hr' (e := .mul .isTransition (.mul (c gz) (.add (n rt) (n sg)))) (by simp [SrcpV3.constraints])
  have h2 := con hL hr' (e := .mul (mul3 .isTransition (c sl) (Dsl.not (c gz))) (Dsl.not (.add (n rt) (n sg))))
    (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_add, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height tt by omega), hl] at h1 h2
  have b := isBool hL hr' (x := gz) (by simp [bools])
  rcases b with h | h <;> rw [h] at h1 h2 ⊢ <;> constructor <;> intro h' <;> first | grind | exact absurd h' (by decide)

theorem height_le : tr.height tt ≤ 2 ^ 22 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

/-! ## Units -/

def uAct (tr : Trace Fp) (tt : Nat) (r : Nat) : Bool := isOne tr tt rt r || isOne tr tt sg r
def uFirst (tr : Trace Fp) (tt : Nat) (r : Nat) : Bool := isOne tr tt rt r || isOne tr tt sf r
def uLast (tr : Trace Fp) (tt : Nat) (r : Nat) : Bool := isOne tr tt rt r || isOne tr tt sl r

theorem segFacts : SegFacts (tr.height tt) (uAct tr tt) (uFirst tr tt) (uLast tr tt) where
  first_act r hr h := by
    simp only [uFirst, uAct, isOne, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨-, -, hwf, -, hsf, -⟩ := local_ hL hr
      have bw := isBool hL hr (x := wf) (by simp [bools])
      rcases bw with bw | bw
      · rw [hsf, bw] at h; exfalso; grind
      · exact (hwf bw).1
  last_act r hr h := by
    simp only [uLast, uAct, isOne, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨-, -, -, hwl, -, hsl, -⟩ := local_ hL hr
      have bw := isBool hL hr (x := wl) (by simp [bools])
      rcases bw with bw | bw
      · rw [hsl, bw] at h; exfalso; grind
      · exact (hwl bw).1
  cont r hr ha hl := by
    simp only [uLast, uAct, uFirst, isOne, Bool.or_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at ha hl ⊢
    have hr' : r < tr.height tt := by omega
    have hs : tr.cell tt r sg = 1 := by
      rcases ha with h | h
      · exact absurd h hl.1
      · exact h
    have hl0 : tr.cell tt r sl = 0 := zero_of_not_one hL hr' (by simp [bools]) (by simp [isOne, hl.2])
    obtain ⟨hn, hrt, -⟩ := inSeg hL hr hs hl0
    refine ⟨Or.inr hn, by rw [hrt]; decide, ?_⟩
    obtain ⟨-, -, -, -, hsf, -⟩ := local_ hL (r := r + 1) hr
    have bw := isBool hL hr' (x := wl) (by simp [bools])
    rcases bw with bw | bw
    · rw [hsf, (inWin hL hr hs bw).1]; grind
    · rw [hsf, (winSwitch hL hr bw hl0).2]; grind
  next r hr hl ha := by
    simp only [uLast, uAct, uFirst, isOne, Bool.or_eq_true, decide_eq_true_eq] at hl ha ⊢
    rcases hl with hl | hl
    · exact Or.inr (afterRoot hL hr hl).2.2.1
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (afterSegSg hL hr hl ha).1
  pad r hr ha := by
    simp only [uAct, isOne, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ha ⊢
    have h1 := zero_of_not_one hL (r := r) (by omega) (x := rt) (by simp [bools]) (by simp [isOne, ha.1])
    have h2 := zero_of_not_one hL (r := r) (by omega) (x := sg) (by simp [bools]) (by simp [isOne, ha.2])
    obtain ⟨e1, e2⟩ := padStep hL hr h1 h2
    rw [e1, e2]; exact ⟨by decide, by decide⟩
  start h0 := by simp [uFirst, isOne, (row0 hL h0).1]
  stop h0 ha := by
    simp only [uAct, uLast, isOne, Bool.or_eq_true, decide_eq_true_eq] at ha ⊢
    obtain ⟨h1, h2, -⟩ := lastRow hL h0
    rcases ha with ha | ha
    · rw [h1] at ha; exact absurd ha (by decide)
    · exact Or.inr (h2 ha)

end

end ZkFormal.NearV3.SrcpProof

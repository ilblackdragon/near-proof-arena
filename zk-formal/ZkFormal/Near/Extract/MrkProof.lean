import ZkFormal.Near.Extract.MrkShape
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Extract.MrkProof — `MrkViewStmt`

Row facts of the `mrk` table; the rows after the root row decompose into
node segments (a hashed node: 64 rows in two 32-row windows; a promoted node:
one row); the node sequence obeys `MrkShape.Rules`, so it enumerates
`mrkShape n`; the view and its traffic.
-/

namespace ZkFormal.Near.MrkProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk

variable {tr : Trace Fp} {pub : List Fp}

abbrev C (tr : Trace Fp) (r x : Nat) : Fp := tr.cell T_MRK r x

theorem con (hL : TableLocal Mrk.table tr T_MRK pub) {r : Nat} (hr : r < tr.height T_MRK)
    {e : Expr} (he : e ∈ Mrk.constraints) : e.eval tr T_MRK r pub = 0 :=
  hL.constr r hr e he

theorem nxt {r : Nat} (h : r + 1 < tr.height T_MRK) : (r + 1) % tr.height T_MRK = r + 1 :=
  Nat.mod_eq_of_lt h

variable (hL : TableLocal Mrk.table tr T_MRK pub)
include hL

theorem isBool {r : Nat} (hr : r < tr.height T_MRK) {x : Nat}
    (hx : x ∈ [rt, sg, pr, wn, wf, wl, sf, sl, odd, lil, top, gM, gO]) :
    tr.cell T_MRK r x = 0 ∨ tr.cell T_MRK r x = 1 := by
  have := con hL hr (e := Dsl.bool (c x)) (by
    unfold Mrk.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

/-- Row-local facts. -/
theorem local_ {r : Nat} (hr : r < tr.height T_MRK) :
    tr.cell T_MRK r rt * (tr.cell T_MRK r sg + tr.cell T_MRK r pr) = 0 ∧
    tr.cell T_MRK r sg * tr.cell T_MRK r pr = 0 ∧
    tr.cell T_MRK r rt = (if r = 0 then 1 else 0) ∧
    (tr.cell T_MRK r wf = 1 → tr.cell T_MRK r sg = 1 ∧ tr.cell T_MRK r pw = 0) ∧
    (tr.cell T_MRK r wl = 1 → tr.cell T_MRK r sg = 1 ∧ tr.cell T_MRK r pw = 31) ∧
    tr.cell T_MRK r sf = tr.cell T_MRK r wf * (1 - tr.cell T_MRK r wn) ∧
    tr.cell T_MRK r sl = tr.cell T_MRK r wl * tr.cell T_MRK r wn ∧
    (tr.cell T_MRK r pr = 1 → tr.cell T_MRK r wn = 0) ∧
    tr.cell T_MRK r gM = tr.cell T_MRK r wf + tr.cell T_MRK r pr + tr.cell T_MRK r rt ∧
    tr.cell T_MRK r gO = tr.cell T_MRK r sf + tr.cell T_MRK r pr := by
  have h1 := con hL hr (e := .mul (c rt) actE) (by simp [Mrk.constraints])
  have h2 := con hL hr (e := .mul (c sg) (c pr)) (by simp [Mrk.constraints])
  have h3 := con hL hr (e := sub (c rt) .isFirst) (by simp [Mrk.constraints])
  have h4 := con hL hr (e := .mul (c wf) (Dsl.not (c sg))) (by simp [Mrk.constraints])
  have h5 := con hL hr (e := .mul (c wl) (Dsl.not (c sg))) (by simp [Mrk.constraints])
  have h6 := con hL hr (e := .mul (c wf) (c pw)) (by simp [Mrk.constraints])
  have h7 := con hL hr (e := .mul (c wl) (sub (c pw) (k 31))) (by simp [Mrk.constraints])
  have h8 := con hL hr (e := sub (c sf) (.mul (c wf) (Dsl.not (c wn)))) (by simp [Mrk.constraints])
  have h9 := con hL hr (e := sub (c sl) (.mul (c wl) (c wn))) (by simp [Mrk.constraints])
  have h10 := con hL hr (e := .mul (c pr) (c wn)) (by simp [Mrk.constraints])
  have h11 := con hL hr (e := sub (c gM) (.add (c wf) (.add (c pr) (c rt)))) (by simp [Mrk.constraints])
  have h12 := con hL hr (e := sub (c gO) (.add (c sf) (c pr))) (by simp [Mrk.constraints])
  simp only [actE, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_isFirst]
    at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  refine ⟨h1, h2, by grind, fun h => ?_, fun h => ?_, by grind, by grind, fun h => ?_, by grind, by grind⟩
  · rw [h] at h4 h6; exact ⟨by grind, by grind⟩
  · rw [h] at h5 h7; exact ⟨by grind, by grind⟩
  · rw [h] at h10; grind


/-- `act = sg + pr` -/
def A (tr : Trace Fp) (r : Nat) : Fp := tr.cell T_MRK r sg + tr.cell T_MRK r pr
/-- node end: `sl + pr` -/
def E (tr : Trace Fp) (r : Nat) : Fp := tr.cell T_MRK r sl + tr.cell T_MRK r pr

theorem inWin {r : Nat} (hr : r + 1 < tr.height T_MRK) (hs : tr.cell T_MRK r sg = 1)
    (hw : tr.cell T_MRK r wl = 0) :
    tr.cell T_MRK (r + 1) sg = 1 ∧ tr.cell T_MRK (r + 1) wf = 0 ∧
    tr.cell T_MRK (r + 1) pw = tr.cell T_MRK r pw + 1 ∧ tr.cell T_MRK (r + 1) wn = tr.cell T_MRK r wn ∧
    ∀ x, x < 31 → tr.cell T_MRK (r + 1) (reg x) = tr.cell T_MRK r (reg (x + 1)) := by
  have hr' : r < tr.height T_MRK := by omega
  have h1 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (Dsl.not (n sg))) (by simp [Mrk.constraints])
  have h2 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (n wf)) (by simp [Mrk.constraints])
  have h3 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n pw) (.add (c pw) (k 1))))
    (by simp [Mrk.constraints])
  have h4 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n wn) (c wn))) (by simp [Mrk.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3 h4
  rw [hs, hw] at h1 h2 h3 h4
  refine ⟨by grind, by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := con hL hr' (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n (reg x)) (c (reg (x + 1)))))
    (by simp only [Mrk.constraints, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨x, hx, rfl⟩)
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h5
  rw [hs, hw] at h5; grind

theorem nodeConstStep {r : Nat} (hr : r + 1 < tr.height T_MRK) (hs : tr.cell T_MRK r sg = 1)
    (hl : tr.cell T_MRK r sl = 0) :
    ∀ x ∈ nodeConst, tr.cell T_MRK (r + 1) x = tr.cell T_MRK r x := by
  intro x hx
  have h := con hL (by omega : r < _) (e := mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x)))
    (by simp only [Mrk.constraints, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨x, hx, rfl⟩))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hr] at h
  rw [hs, hl] at h; grind

theorem win0End {r : Nat} (hr : r + 1 < tr.height T_MRK) (hw : tr.cell T_MRK r wl = 1)
    (hn : tr.cell T_MRK r wn = 0) :
    tr.cell T_MRK (r + 1) sg = 1 ∧ tr.cell T_MRK (r + 1) wf = 1 ∧ tr.cell T_MRK (r + 1) wn = 1 := by
  have hr' : r < tr.height T_MRK := by omega
  have h1 := con hL hr' (e := mul3 (c wl) (Dsl.not (c wn)) (Dsl.not (n sg))) (by simp [Mrk.constraints])
  have h2 := con hL hr' (e := mul3 (c wl) (Dsl.not (c wn)) (Dsl.not (n wf))) (by simp [Mrk.constraints])
  have h3 := con hL hr' (e := mul3 (c wl) (Dsl.not (c wn)) (Dsl.not (n wn))) (by simp [Mrk.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1 h2 h3
  rw [hw, hn] at h1 h2 h3
  exact ⟨by grind, by grind, by grind⟩

theorem shapeRow {r : Nat} (hr : r < tr.height T_MRK) (ha : A tr r = 1) :
    tr.cell T_MRK r sp + tr.cell T_MRK r odd = 2 * tr.cell T_MRK r s ∧
    tr.cell T_MRK r pr = tr.cell T_MRK r odd * tr.cell T_MRK r lil ∧
    (tr.cell T_MRK r lil = 1 → tr.cell T_MRK r i + 1 = tr.cell T_MRK r s) ∧
    (tr.cell T_MRK r top = 1 → tr.cell T_MRK r s = 1) ∧
    (tr.cell T_MRK r top = 0 → (tr.cell T_MRK r s - 1) * tr.cell T_MRK r inv = 1) := by
  have h1 := con hL hr (e := .mul actE (sub (.add (c sp) (c odd)) (smul 2 (c s)))) (by simp [Mrk.constraints])
  have h2 := con hL hr (e := .mul actE (sub (c pr) (.mul (c odd) (c lil)))) (by simp [Mrk.constraints])
  have h3 := con hL hr (e := .mul (c lil) (sub (.add (c i) (k 1)) (c s))) (by simp [Mrk.constraints])
  have h4 := con hL hr (e := .mul (c top) (sub (c s) (k 1))) (by simp [Mrk.constraints])
  have h5 := con hL hr (e := .mul actE (sub (.mul (sub (c s) (k 1)) (c inv)) (Dsl.not (c top))))
    (by simp [Mrk.constraints])
  simp only [actE, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_smul] at h1 h2 h3 h4 h5
  simp only [A] at ha
  rw [ha] at h1 h2 h5
  refine ⟨by grind, by grind, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h3; grind
  · rw [h] at h4; grind
  · rw [h] at h5; grind

theorem nodeEnd {r : Nat} (hr : r + 1 < tr.height T_MRK) (he : E tr r = 1) :
    (tr.cell T_MRK (r + 1) sg = 1 → tr.cell T_MRK (r + 1) sf = 1) ∧
    (tr.cell T_MRK r lil = 0 → A tr (r + 1) = 1 ∧ tr.cell T_MRK (r + 1) j = tr.cell T_MRK r j ∧
      tr.cell T_MRK (r + 1) i = tr.cell T_MRK r i + 1 ∧ tr.cell T_MRK (r + 1) sp = tr.cell T_MRK r sp) ∧
    (tr.cell T_MRK r lil = 1 → tr.cell T_MRK r top = 0 → A tr (r + 1) = 1 ∧
      tr.cell T_MRK (r + 1) j = tr.cell T_MRK r j + 1 ∧ tr.cell T_MRK (r + 1) i = 0 ∧
      tr.cell T_MRK (r + 1) sp = tr.cell T_MRK r s) ∧
    (tr.cell T_MRK r lil = 1 → tr.cell T_MRK r top = 1 → A tr (r + 1) = 0) ∧
    (A tr (r + 1) = 1 → tr.cell T_MRK (r + 1) q = tr.cell T_MRK r q + tr.cell T_MRK r sg) := by
  have hr' : r < tr.height T_MRK := by omega
  have c0 := con hL hr' (e := .mul endE (.mul (n sg) (Dsl.not (n sf)))) (by simp [Mrk.constraints])
  have c1 := con hL hr' (e := .mul endE (.mul (Dsl.not (c lil)) (Dsl.not nActE))) (by simp [Mrk.constraints])
  have c2 := con hL hr' (e := .mul endE (.mul (Dsl.not (c lil)) (sub (n j) (c j)))) (by simp [Mrk.constraints])
  have c3 := con hL hr' (e := .mul endE (.mul (Dsl.not (c lil)) (sub (n i) (.add (c i) (k 1)))))
    (by simp [Mrk.constraints])
  have c4 := con hL hr' (e := .mul endE (.mul (Dsl.not (c lil)) (sub (n sp) (c sp)))) (by simp [Mrk.constraints])
  have c5 := con hL hr' (e := .mul endE (.mul (c lil) (.mul (Dsl.not (c top)) (Dsl.not nActE))))
    (by simp [Mrk.constraints])
  have c6 := con hL hr' (e := .mul endE (.mul (c lil) (.mul (Dsl.not (c top)) (sub (n j) (.add (c j) (k 1))))))
    (by simp [Mrk.constraints])
  have c7 := con hL hr' (e := .mul endE (.mul (c lil) (.mul (Dsl.not (c top)) (n i)))) (by simp [Mrk.constraints])
  have c8 := con hL hr' (e := .mul endE (.mul (c lil) (.mul (Dsl.not (c top)) (sub (n sp) (c s)))))
    (by simp [Mrk.constraints])
  have c9 := con hL hr' (e := .mul endE (.mul (c lil) (.mul (c top) nActE))) (by simp [Mrk.constraints])
  have c10 := con hL hr' (e := .mul endE (.mul nActE (sub (n q) (.add (c q) (c sg))))) (by simp [Mrk.constraints])
  simp only [endE, nActE, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr]
    at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  simp only [E] at he
  simp only [A]
  rw [he] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · rw [h] at c0; grind
  · rw [h] at c1 c2 c3 c4; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h1, h2] at c5 c6 c7 c8; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h1, h2] at c9; grind
  · rw [h] at c10; grind

theorem rootRow (h1 : 1 < tr.height T_MRK) :
    tr.cell T_MRK 0 rt = 1 ∧ A tr 1 = 1 ∧ tr.cell T_MRK 1 j = 1 ∧ tr.cell T_MRK 1 i = 0 ∧
    tr.cell T_MRK 1 sp = nPubE.eval tr T_MRK 0 pub ∧ tr.cell T_MRK 1 q = 0 ∧
    (tr.cell T_MRK 1 sg = 1 → tr.cell T_MRK 1 sf = 1) := by
  have h0 : (0 : Nat) < tr.height T_MRK := by omega
  have hrt : tr.cell T_MRK 0 rt = 1 := by have := (local_ hL h0).2.2.1; simpa using this
  have c1 := con hL h0 (e := .mul (c rt) (Dsl.not nActE)) (by simp [Mrk.constraints])
  have c2 := con hL h0 (e := .mul (c rt) (sub (n j) (k 1))) (by simp [Mrk.constraints])
  have c3 := con hL h0 (e := .mul (c rt) (n i)) (by simp [Mrk.constraints])
  have c4 := con hL h0 (e := .mul (c rt) (sub (n sp) nPubE)) (by simp [Mrk.constraints])
  have c5 := con hL h0 (e := .mul (c rt) (n q)) (by simp [Mrk.constraints])
  have c6 := con hL h0 (e := .mul (c rt) (.mul (n sg) (Dsl.not (n sf)))) (by simp [Mrk.constraints])
  have e1 : (0 + 1) % tr.height T_MRK = 1 := Nat.mod_eq_of_lt h1
  simp only [nActE, eval_mul, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, e1] at c1 c2 c3 c4 c5 c6
  rw [hrt] at c1 c2 c3 c4 c5 c6
  refine ⟨hrt, by simp only [A]; grind, by grind, by grind, by grind, by grind, fun h => ?_⟩
  rw [h] at c6; grind

theorem padRow {r : Nat} (hr : r + 1 < tr.height T_MRK) (ha : A tr r = 0) (hrt : tr.cell T_MRK r rt = 0) :
    A tr (r + 1) = 0 := by
  have c := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (.add actE (c rt))) nActE)
    (by simp [Mrk.constraints])
  simp only [actE, nActE, eval_mul3, eval_c, eval_not, eval_n, eval_add, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height T_MRK by omega)] at c
  simp only [A] at ha ⊢
  rw [ha, hrt] at c; grind

theorem lastRow (h0 : 0 < tr.height T_MRK) : A tr (tr.height T_MRK - 1) = 0 := by
  have c := con hL (by omega : tr.height T_MRK - 1 < _) (e := .mul .isLast actE) (by simp [Mrk.constraints])
  simp only [actE, eval_mul, eval_c, eval_add, eval_isLast,
    if_pos (show tr.height T_MRK - 1 + 1 = tr.height T_MRK by omega)] at c
  simp only [A]; grind

theorem links {r : Nat} (hr : r < tr.height T_MRK) :
    (tr.cell T_MRK r wf + tr.cell T_MRK r pr = 1 → tr.cell T_MRK r mj + 1 = tr.cell T_MRK r j ∧
      tr.cell T_MRK r mi = 2 * tr.cell T_MRK r i + tr.cell T_MRK r wn) ∧
    (tr.cell T_MRK r rt = 1 → tr.cell T_MRK r mi = 0) ∧
    (tr.cell T_MRK r sf = 1 → tr.cell T_MRK r oId = (K_MRK : Fp) + (16 : Nat) * tr.cell T_MRK r q ∧
      tr.cell T_MRK r oLen = 64) ∧
    (tr.cell T_MRK r pr = 1 → tr.cell T_MRK r oId = tr.cell T_MRK r cId ∧
      tr.cell T_MRK r oLen = tr.cell T_MRK r cLen) := by
  have c1 := con hL hr (e := .mul (.add (c wf) (c pr)) (sub (.add (c mj) (k 1)) (c j))) (by simp [Mrk.constraints])
  have c2 := con hL hr (e := .mul (.add (c wf) (c pr)) (sub (c mi) (.add (smul 2 (c i)) (c wn))))
    (by simp [Mrk.constraints])
  have c3 := con hL hr (e := .mul (c rt) (c mi)) (by simp [Mrk.constraints])
  have c4 := con hL hr (e := .mul (c sf) (sub (c oId) (mid K_MRK (c q)))) (by simp [Mrk.constraints])
  have c5 := con hL hr (e := .mul (c sf) (sub (c oLen) (k 64))) (by simp [Mrk.constraints])
  have c6 := con hL hr (e := .mul (c pr) (sub (c oId) (c cId))) (by simp [Mrk.constraints])
  have c7 := con hL hr (e := .mul (c pr) (sub (c oLen) (c cLen))) (by simp [Mrk.constraints])
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k, eval_smul, eval_mid] at c1 c2 c3 c4 c5 c6 c7
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at c1 c2; exact ⟨by grind, by grind⟩
  · rw [h] at c3; grind
  · rw [h] at c4 c5; exact ⟨by grind, by grind⟩
  · rw [h] at c6 c7; exact ⟨by grind, by grind⟩

end ZkFormal.Near.MrkProof

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

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk

variable {tr : Trace Fp} {pub : List Fp}

def one (tr : Trace Fp) (x r : Nat) : Bool := decide (tr.cell T_MRK r x = 1)

/-- Shifted row predicates (row `r'` = table row `r' + 1`). -/
def actS (tr : Trace Fp) (r : Nat) : Bool := decide (A tr (r + 1) = 1)
def firstS (tr : Trace Fp) (r : Nat) : Bool := one tr sf (r + 1) || one tr pr (r + 1)
def lastS (tr : Trace Fp) (r : Nat) : Bool := one tr sl (r + 1) || one tr pr (r + 1)

theorem height_le (hL : TableLocal Mrk.table tr T_MRK pub) : tr.height T_MRK ≤ 2 ^ 15 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_ge (hL : TableLocal Mrk.table tr T_MRK pub) : 2 ≤ tr.height T_MRK := by
  have := hL.log_ge; unfold Trace.height
  calc 2 = 2 ^ 1 := rfl
    _ ≤ _ := Nat.pow_le_pow_right (by omega) this

theorem bool01 (hL : TableLocal Mrk.table tr T_MRK pub) {r x : Nat} (hr : r < tr.height T_MRK)
    (hx : x ∈ [rt, sg, pr, wn, wf, wl, sf, sl, odd, lil, top, gM, gO]) (h : ¬ tr.cell T_MRK r x = 1) :
    tr.cell T_MRK r x = 0 := (isBool hL hr hx).resolve_right h

theorem A_cases (hL : TableLocal Mrk.table tr T_MRK pub) {r : Nat} (hr : r < tr.height T_MRK) :
    (A tr r = 1 ∧ ((tr.cell T_MRK r sg = 1 ∧ tr.cell T_MRK r pr = 0) ∨
      (tr.cell T_MRK r sg = 0 ∧ tr.cell T_MRK r pr = 1))) ∨
    (A tr r = 0 ∧ tr.cell T_MRK r sg = 0 ∧ tr.cell T_MRK r pr = 0) := by
  have h2 := (local_ hL hr).2.1
  rcases isBool hL hr (x := sg) (by simp) with a | a <;> rcases isBool hL hr (x := pr) (by simp) with b | b <;>
    simp only [A, a, b] at h2 ⊢ <;> grind

theorem segFacts (hL : TableLocal Mrk.table tr T_MRK pub) :
    SegFacts (tr.height T_MRK - 1) (actS tr) (firstS tr) (lastS tr) where
  first_act r hr h := by
    simp only [firstS, one, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [actS, decide_eq_true_eq]
    rcases A_cases hL (r := r + 1) (by omega) with ⟨h1, _⟩ | ⟨-, h2, h3⟩
    · exact h1
    · rcases h with h | h
      · have := (local_ hL (r := r + 1) (by omega)).2.2.2.2.2.1
        rw [h] at this
        have hw : tr.cell T_MRK (r + 1) wf = 1 := by
          rcases isBool hL (r := r + 1) (by omega) (x := wf) (by simp) with e | e <;> rw [e] at this <;> grind
        have := ((local_ hL (r := r + 1) (by omega)).2.2.2.1 hw).1; rw [h2] at this; exact absurd this.symm fp_one_ne_zero
      · rw [h3] at h; exact absurd h fp_zero_ne_one
  last_act r hr h := by
    simp only [lastS, one, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [actS, decide_eq_true_eq]
    rcases A_cases hL (r := r + 1) (by omega) with ⟨h1, _⟩ | ⟨-, h2, h3⟩
    · exact h1
    · rcases h with h | h
      · have := (local_ hL (r := r + 1) (by omega)).2.2.2.2.2.2.1
        rw [h] at this
        have hw : tr.cell T_MRK (r + 1) wl = 1 := by
          rcases isBool hL (r := r + 1) (by omega) (x := wl) (by simp) with e | e <;> rw [e] at this <;> grind
        have := ((local_ hL (r := r + 1) (by omega)).2.2.2.2.1 hw).1; rw [h2] at this; exact absurd this.symm fp_one_ne_zero
      · rw [h3] at h; exact absurd h fp_zero_ne_one
  cont r hr ha hl := by
    simp only [actS, decide_eq_true_eq] at ha
    simp only [lastS, one, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hl
    have hsl := bool01 hL (r := r + 1) (by omega) (by simp) hl.1
    have hpr := bool01 hL (r := r + 1) (by omega) (by simp) hl.2
    have hsg : tr.cell T_MRK (r + 1) sg = 1 := by simp only [A, hpr] at ha; grind
    have loc := local_ hL (r := r + 1) (by omega)
    have nl := local_ hL (r := r + 1 + 1) (by omega)
    have hnext : tr.cell T_MRK (r + 1 + 1) sg = 1 ∧ tr.cell T_MRK (r + 1 + 1) sf = 0 := by
      rcases isBool hL (r := r + 1) (by omega) (x := wl) (by simp) with hw | hw
      · obtain ⟨n1, n2, -⟩ := inWin hL (r := r + 1) (by omega) hsg hw
        refine ⟨n1, ?_⟩; rw [nl.2.2.2.2.2.1, n2]; grind
      · have hwn : tr.cell T_MRK (r + 1) wn = 0 := by
          have := loc.2.2.2.2.2.2.1; rw [hsl, hw] at this; grind
        obtain ⟨n1, n2, n3⟩ := win0End hL (r := r + 1) (by omega) hw hwn
        refine ⟨n1, ?_⟩; rw [nl.2.2.2.2.2.1, n2, n3]; grind
    have hpr' : tr.cell T_MRK (r + 1 + 1) pr = 0 := by
      have := nl.2.1; rw [hnext.1] at this; grind
    constructor
    · simp only [actS, decide_eq_true_eq, A, hnext.1, hpr']; grind
    · simp [firstS, one, hnext.2, hpr']
  next r hr hl ha := by
    simp only [actS, decide_eq_true_eq] at ha
    simp only [lastS, one, Bool.or_eq_true, decide_eq_true_eq] at hl
    have hE : E tr (r + 1) = 1 := by
      have hsp := (local_ hL (r := r + 1) (by omega)).2.1
      rcases hl with h | h
      · have hs := (local_ hL (r := r + 1) (by omega)).2.2.2.2.2.2.1
        have hsg : tr.cell T_MRK (r + 1) sg = 1 := by
          have hw : tr.cell T_MRK (r + 1) wl = 1 := by
            rw [h] at hs
            rcases isBool hL (r := r + 1) (by omega) (x := wl) (by simp) with e | e <;> rw [e] at hs <;> grind
          exact ((local_ hL (r := r + 1) (by omega)).2.2.2.2.1 hw).1
        rw [hsg] at hsp
        simp only [E, h]; grind
      · rw [h] at hsp
        have hl2 := bool01 hL (r := r + 1) (by omega) (x := sl) (by simp) (by
          intro h'
          have hs := (local_ hL (r := r + 1) (by omega)).2.2.2.2.2.2.1
          rw [h'] at hs
          have hw : tr.cell T_MRK (r + 1) wl = 1 := by
            rcases isBool hL (r := r + 1) (by omega) (x := wl) (by simp) with e | e <;> rw [e] at hs <;> grind
          have hsg1 := ((local_ hL (r := r + 1) (by omega)).2.2.2.2.1 hw).1
          rw [hsg1] at hsp; grind)
        simp only [E, h, hl2]; grind
    have ne := (nodeEnd hL (r := r + 1) (by omega) hE).1
    simp only [firstS, one, Bool.or_eq_true, decide_eq_true_eq]
    rcases A_cases hL (r := r + 1 + 1) (by omega) with ⟨-, ⟨h1, -⟩ | ⟨-, h2⟩⟩ | ⟨h0, -⟩
    · exact Or.inl (ne h1)
    · exact Or.inr h2
    · rw [ha] at h0; exact absurd h0 fp_one_ne_zero
  pad r hr ha := by
    simp only [actS, decide_eq_false_iff_not] at ha ⊢
    have hA : A tr (r + 1) = 0 := by
      rcases A_cases hL (r := r + 1) (by omega) with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h ha
      · exact h
    have hrt : tr.cell T_MRK (r + 1) rt = 0 := by
      have := (local_ hL (r := r + 1) (by omega)).2.2.1; simpa using this
    rw [padRow hL (r := r + 1) (by omega) hA hrt]; exact fp_zero_ne_one
  start h0 := by
    obtain ⟨-, hA, -, -, -, -, hsf⟩ := rootRow hL (by omega)
    simp only [firstS, one, Bool.or_eq_true, decide_eq_true_eq, Nat.zero_add]
    rcases A_cases hL (r := 1) (by omega) with ⟨-, ⟨h1, -⟩ | ⟨-, h2⟩⟩ | ⟨h0', -⟩
    · exact Or.inl (hsf h1)
    · exact Or.inr h2
    · rw [hA] at h0'; exact absurd h0' fp_one_ne_zero
  stop h0 ha := by
    simp only [actS, decide_eq_true_eq] at ha
    rw [show tr.height T_MRK - 1 - 1 + 1 = tr.height T_MRK - 1 by omega, lastRow hL (by omega)] at ha
    exact absurd ha fp_zero_ne_one

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk

variable {tr : Trace Fp} {pub : List Fp}

/-- One 32-row window from row `s0` (`sg`, `wf`, `wn = w`): the first `wl` is at
offset 31 (given that some row before `s0 + L` has `wl`). -/
theorem window (hL : TableLocal Mrk.table tr T_MRK pub) {s0 L : Nat} (hH : s0 + L ≤ tr.height T_MRK)
    (hsg : tr.cell T_MRK s0 sg = 1) (hwf : tr.cell T_MRK s0 wf = 1)
    (hex : ∃ d, d < L ∧ tr.cell T_MRK (s0 + d) wl = 1) :
    31 < L ∧ tr.cell T_MRK (s0 + 31) wl = 1 ∧
    ∀ p, p < 32 → tr.cell T_MRK (s0 + p) sg = 1 ∧ tr.cell T_MRK (s0 + p) pw = ((p : Nat) : Fp) ∧
      tr.cell T_MRK (s0 + p) wn = tr.cell T_MRK s0 wn ∧ (p < 31 → tr.cell T_MRK (s0 + p) wl = 0) ∧
      (0 < p → tr.cell T_MRK (s0 + p) wf = 0) ∧
      (∀ x, x + p < 32 → tr.cell T_MRK (s0 + p) (reg x) = tr.cell T_MRK s0 (reg (x + p))) := by
  have hP : tr.height T_MRK < P := by have := height_le hL; unfold P; omega
  obtain ⟨d, ⟨hdL, hwd⟩, hmin⟩ := exists_least hex
  have hnw : ∀ p, p < d → tr.cell T_MRK (s0 + p) wl = 0 := fun p hp =>
    bool01 hL (by omega) (by simp) (fun h => hmin p hp ⟨by omega, h⟩)
  -- rows before the first `wl`
  have run : ∀ p, p ≤ d → tr.cell T_MRK (s0 + p) sg = 1 ∧ tr.cell T_MRK (s0 + p) pw = ((p : Nat) : Fp) ∧
      tr.cell T_MRK (s0 + p) wn = tr.cell T_MRK s0 wn ∧ (0 < p → tr.cell T_MRK (s0 + p) wf = 0) ∧
      (∀ x, x + p < 32 → tr.cell T_MRK (s0 + p) (reg x) = tr.cell T_MRK s0 (reg (x + p))) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact ⟨hsg, ((local_ hL (by omega : s0 + 0 < _)).2.2.2.1 hwf).2, rfl, fun h => by omega,
        fun x _ => rfl⟩
    | succ p ih =>
      intro hp
      obtain ⟨a1, a2, a3, -, a5⟩ := ih (by omega)
      obtain ⟨b1, b2, b3, b4, b5⟩ := inWin hL (r := s0 + p) (by omega) a1 (hnw p (by omega))
      rw [show s0 + (p + 1) = s0 + p + 1 by omega]
      refine ⟨b1, by rw [b3, a2, natCast_add]; rfl, by rw [b4, a3], fun _ => b2, fun x hx => ?_⟩
      rw [b5 x (by omega), a5 (x + 1) (by omega), show x + 1 + p = x + (p + 1) by omega]
  have h31 : d = 31 := by
    have e := ((local_ hL (by omega : s0 + d < _)).2.2.2.2.1 hwd).2
    rw [(run d (Nat.le_refl _)).2.1] at e
    exact ofNat_inj (by omega) (by unfold P; omega) e
  subst h31
  refine ⟨hdL, hwd, fun p hp => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := run p (by omega)
  exact ⟨a1, a2, a3, fun h => hnw p h, a4, a5⟩

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk

variable {tr : Trace Fp} {pub : List Fp}

/-- In a window started at `s0` whose rows up to `s0 + L - 1` are not
segment ends, unless one has `wl`, the end row `s0 + L - 1` cannot be a node end. -/
theorem exists_wl (hL : TableLocal Mrk.table tr T_MRK pub) {s0 L : Nat} (hH : s0 + L ≤ tr.height T_MRK)
    (hL0 : 0 < L) (hsg : tr.cell T_MRK s0 sg = 1) (hwn : tr.cell T_MRK s0 wn = 0 ∨ True)
    (hend : tr.cell T_MRK (s0 + L - 1) sl = 1 ∨ tr.cell T_MRK (s0 + L - 1) pr = 1) :
    ∃ d, d < L ∧ tr.cell T_MRK (s0 + d) wl = 1 := by
  refine Classical.byContradiction fun hne => ?_
  have hnw : ∀ p, p < L → tr.cell T_MRK (s0 + p) wl = 0 := fun p hp =>
    bool01 hL (by omega) (by simp) (fun h => hne ⟨p, hp, h⟩)
  have run : ∀ p, p < L → tr.cell T_MRK (s0 + p) sg = 1 := by
    intro p
    induction p with
    | zero => intro _; exact hsg
    | succ p ih =>
      intro hp
      have := (inWin hL (r := s0 + p) (by omega) (ih (by omega)) (hnw p (by omega))).1
      rwa [show s0 + (p + 1) = s0 + p + 1 by omega]
  have hs := run (L - 1) (by omega)
  rw [show s0 + (L - 1) = s0 + L - 1 by omega] at hs
  have hw := hnw (L - 1) (by omega)
  rw [show s0 + (L - 1) = s0 + L - 1 by omega] at hw
  have l := local_ hL (r := s0 + L - 1) (by omega)
  rcases hend with h | h
  · have := l.2.2.2.2.2.2.1; rw [h, hw] at this; grind
  · have := l.2.1; rw [hs, h] at this; grind

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk

variable {tr : Trace Fp} {pub : List Fp}

/-- What a hashed node segment at `s` looks like. -/
structure Hashed (tr : Trace Fp) (s : Nat) : Prop where
  sf1 : tr.cell T_MRK s sf = 1
  rows : ∀ p, p < 64 → tr.cell T_MRK (s + p) sg = 1 ∧ tr.cell T_MRK (s + p) pr = 0 ∧
    tr.cell T_MRK (s + p) pw = ((p % 32 : Nat) : Fp) ∧ tr.cell T_MRK (s + p) wn = (if p < 32 then 0 else 1) ∧
    (tr.cell T_MRK (s + p) wf = 1 ↔ p % 32 = 0) ∧ (∀ x ∈ nodeConst, tr.cell T_MRK (s + p) x = tr.cell T_MRK s x)
  regs : ∀ w, w < 2 → ∀ x, x < 32 → tr.cell T_MRK (s + 32 * w + x) (reg 0) = tr.cell T_MRK (s + 32 * w) (reg x)
  last : tr.cell T_MRK (s + 63) sl = 1

theorem segKind (hL : TableLocal Mrk.table tr T_MRK pub) {s' ℓ : Nat}
    (hseg : IsSeg (actS tr) (firstS tr) (lastS tr) s' ℓ) (hH : s' + ℓ ≤ tr.height T_MRK - 1) :
    (tr.cell T_MRK (s' + 1) pr = 1 ∧ tr.cell T_MRK (s' + 1) sg = 0 ∧ ℓ = 1) ∨
    (ℓ = 64 ∧ tr.cell T_MRK (s' + 1) pr = 0 ∧ Hashed tr (s' + 1)) := by
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hseg
  have hH' : s' + 1 + ℓ ≤ tr.height T_MRK := by omega
  -- the end row is a node end
  have hend : tr.cell T_MRK (s' + 1 + ℓ - 1) sl = 1 ∨ tr.cell T_MRK (s' + 1 + ℓ - 1) pr = 1 := by
    simp only [lastS, one, Bool.or_eq_true, decide_eq_true_eq] at hle
    rwa [show s' + 1 + ℓ - 1 = s' + ℓ - 1 + 1 by omega]
  -- rows strictly inside are not ends
  have hnl : ∀ p, p + 1 < ℓ → tr.cell T_MRK (s' + 1 + p) sl = 0 ∧ tr.cell T_MRK (s' + 1 + p) pr = 0 := by
    intro p hp
    have := hlast (s' + p) (by omega) (by omega)
    simp only [lastS, one, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
    rw [show s' + p + 1 = s' + 1 + p by omega] at this
    exact ⟨bool01 hL (by omega) (by simp) this.1, bool01 hL (by omega) (by simp) this.2⟩
  simp only [firstS, one, Bool.or_eq_true, decide_eq_true_eq] at hfs
  by_cases hpr : tr.cell T_MRK (s' + 1) pr = 1
  · left
    refine ⟨hpr, ?_, ?_⟩
    · have := (local_ hL (r := s' + 1) (by omega)).2.1; rw [hpr] at this
      rcases isBool hL (r := s' + 1) (by omega) (x := sg) (by simp) with h | h
      · exact h
      · rw [h] at this; grind
    · rcases Nat.lt_or_ge 1 ℓ with h | h
      · have := (hnl 0 h).2; rw [Nat.add_zero, hpr] at this; exact absurd this fp_one_ne_zero
      · omega
  · right
    have hpr0 := bool01 hL (r := s' + 1) (by omega) (by simp) hpr
    have hsf : tr.cell T_MRK (s' + 1) sf = 1 := hfs.resolve_right hpr
    have l0 := local_ hL (r := s' + 1) (by omega)
    have hwf : tr.cell T_MRK (s' + 1) wf = 1 ∧ tr.cell T_MRK (s' + 1) wn = 0 := by
      have e := l0.2.2.2.2.2.1; rw [hsf] at e
      rcases isBool hL (r := s' + 1) (by omega) (x := wf) (by simp) with a | a <;>
      rcases isBool hL (r := s' + 1) (by omega) (x := wn) (by simp) with b | b <;>
        rw [a, b] at e <;> first | exact ⟨a, b⟩ | grind
    have hsg := (l0.2.2.2.1 hwf.1).1
    -- first window
    obtain ⟨h31, hw31, w1⟩ := window hL (s0 := s' + 1) (L := ℓ) hH' hsg hwf.1
      (exists_wl hL hH' hpos hsg (Or.inr trivial) hend)
    have hwn31 : tr.cell T_MRK (s' + 1 + 31) wn = 0 := by rw [(w1 31 (by omega)).2.2.1, hwf.2]
    have hsl31 : tr.cell T_MRK (s' + 1 + 31) sl = 0 := by
      have := (local_ hL (r := s' + 1 + 31) (by omega)).2.2.2.2.2.2.1; rw [hw31, hwn31] at this; grind
    have h32 : 32 < ℓ := by
      rcases Nat.lt_or_ge 32 ℓ with h | h
      · exact h
      · exfalso
        have he : s' + 1 + ℓ - 1 = s' + 1 + 31 := by omega
        rw [he] at hend
        rcases hend with h1 | h1
        · rw [hsl31] at h1; exact fp_zero_ne_one h1
        · have := (w1 31 (by omega)).1
          have := (local_ hL (r := s' + 1 + 31) (by omega)).2.1
          rw [(w1 31 (by omega)).1, h1] at this; grind
    obtain ⟨n1, n2, n3⟩ := win0End hL (r := s' + 1 + 31) (by omega) hw31 hwn31
    rw [show s' + 1 + 31 + 1 = s' + 1 + 32 by omega] at n1 n2 n3
    -- second window
    obtain ⟨h31', hw63, w2⟩ := window hL (s0 := s' + 1 + 32) (L := ℓ - 32) (by omega) n1 n2
      (exists_wl hL (by omega) (by omega) n1 (Or.inr trivial)
        (by rwa [show s' + 1 + 32 + (ℓ - 32) - 1 = s' + 1 + ℓ - 1 by omega]))
    have hsl63 : tr.cell T_MRK (s' + 1 + 32 + 31) sl = 1 := by
      have := (local_ hL (r := s' + 1 + 32 + 31) (by omega)).2.2.2.2.2.2.1
      rw [hw63, (w2 31 (by omega)).2.2.1, n3] at this; grind
    have h64 : ℓ = 64 := by
      rcases Nat.lt_or_ge 64 ℓ with h | h
      · have := (hnl 63 (by omega)).1
        rw [show s' + 1 + 63 = s' + 1 + 32 + 31 by omega, hsl63] at this; exact absurd this fp_one_ne_zero
      · omega
    subst h64
    refine ⟨rfl, hpr0, ⟨hsf, fun p hp => ?_, fun w hw x hx => ?_, by
      rw [show s' + 1 + 63 = s' + 1 + 32 + 31 by omega]; exact hsl63⟩⟩
    · -- node constants: every row before the last is in a window and not an end
      have hcst : ∀ p, p < 64 → ∀ x ∈ nodeConst, tr.cell T_MRK (s' + 1 + p) x = tr.cell T_MRK (s' + 1) x := by
        intro p
        induction p with
        | zero => intro _ x _; rfl
        | succ p ih =>
          intro hp x hx
          have hsgp : tr.cell T_MRK (s' + 1 + p) sg = 1 := by
            rcases Nat.lt_or_ge p 32 with h | h
            · exact (w1 p h).1
            · have := (w2 (p - 32) (by omega)).1; rwa [show s' + 1 + 32 + (p - 32) = s' + 1 + p by omega] at this
          have := nodeConstStep hL (r := s' + 1 + p) (by omega) hsgp (hnl p (by omega)).1 x hx
          rw [show s' + 1 + (p + 1) = s' + 1 + p + 1 by omega, this, ih (by omega) x hx]
      rcases Nat.lt_or_ge p 32 with h | h
      · obtain ⟨a1, a2, a3, -, a5, -⟩ := w1 p h
        refine ⟨a1, ?_, by rw [a2, Nat.mod_eq_of_lt h], by rw [a3, hwf.2, if_pos h], ?_, hcst p hp⟩
        · have := (local_ hL (r := s' + 1 + p) (by omega)).2.1; rw [a1] at this; grind
        · constructor
          · intro hw1; rcases Nat.eq_zero_or_pos p with h0 | h0
            · subst h0; rfl
            · rw [a5 h0] at hw1; exact absurd hw1 fp_zero_ne_one
          · intro h0; rw [Nat.mod_eq_of_lt h] at h0; subst h0; exact hwf.1
      · have e : s' + 1 + p = s' + 1 + 32 + (p - 32) := by omega
        obtain ⟨a1, a2, a3, -, a5, -⟩ := w2 (p - 32) (by omega)
        rw [← e] at a1 a2 a3 a5
        refine ⟨a1, ?_, by rw [a2, show p % 32 = p - 32 by omega], by rw [a3, n3, if_neg (by omega)], ?_,
          hcst p hp⟩
        · have := (local_ hL (r := s' + 1 + p) (by omega)).2.1; rw [a1] at this; grind
        · constructor
          · intro hw1; rcases Nat.eq_zero_or_pos (p - 32) with h0 | h0
            · omega
            · rw [a5 h0] at hw1; exact absurd hw1 fp_zero_ne_one
          · intro h0
            have : p = 32 := by omega
            subst this; simpa using n2
    · rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl
      · have := (w1 x hx).2.2.2.2.2 0 (by omega); simpa using this
      · have := (w2 x hx).2.2.2.2.2 0 (by omega); simpa using this

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp}

/-- The node read at its first row `r`. -/
def ndAt (tr : Trace Fp) (r : Nat) : ND :=
  { j := (tr.cell T_MRK r j).toNat, i := (tr.cell T_MRK r i).toNat, sp := (tr.cell T_MRK r sp).toNat,
    s := (tr.cell T_MRK r s).toNat, odd := one tr odd r, lil := one tr lil r, top := one tr top r,
    pr := one tr pr r }

/-- Last row of a node segment and its constants. -/
theorem endRow (hL : TableLocal Mrk.table tr T_MRK pub) {s' ℓ : Nat}
    (hseg : IsSeg (actS tr) (firstS tr) (lastS tr) s' ℓ) (hH : s' + ℓ ≤ tr.height T_MRK - 1) :
    E tr (s' + ℓ) = 1 ∧ A tr (s' + 1) = 1 ∧
    ∀ x ∈ nodeConst, tr.cell T_MRK (s' + ℓ) x = tr.cell T_MRK (s' + 1) x := by
  rcases segKind hL hseg hH with ⟨hpr, hsg, rfl⟩ | ⟨rfl, hpr, hh⟩
  · have hwn := (local_ hL (r := s' + 1) (by omega)).2.2.2.2.2.2.2.1 hpr
    have hsl := (local_ hL (r := s' + 1) (by omega)).2.2.2.2.2.2.1
    rw [hwn] at hsl
    refine ⟨?_, by simp only [A, hsg, hpr]; grind, fun _ _ => rfl⟩
    simp only [E, hpr, hsl]; grind
  · have h63 := hh.rows 63 (by omega)
    have h0 := hh.rows 0 (by omega)
    rw [show s' + 1 + 63 = s' + 64 by omega] at h63
    have hl := hh.last; rw [show s' + 1 + 63 = s' + 64 by omega] at hl
    refine ⟨by simp only [E, hl, h63.2.1]; grind, by simp only [A]; rw [Nat.add_zero] at h0; rw [h0.1, hpr]; grind,
      h63.2.2.2.2.2⟩

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp}

theorem cellOne {tr : Trace Fp} (hL : TableLocal Mrk.table tr T_MRK pub) {r x : Nat}
    (hr : r < tr.height T_MRK) (hx : x ∈ [rt, sg, pr, wn, wf, wl, sf, sl, odd, lil, top, gM, gO]) :
    tr.cell T_MRK r x = if one tr x r then 1 else 0 := by
  rcases isBool hL hr hx with h | h <;> simp [one, h]

/-- Field-level node succession between consecutive segments `p0`, `p1`. -/
theorem succF (hL : TableLocal Mrk.table tr T_MRK pub) {p0 p1 : Nat × Nat}
    (hs0 : IsSeg (actS tr) (firstS tr) (lastS tr) p0.1 p0.2) (h0 : p0.1 + p0.2 ≤ tr.height T_MRK - 1)
    (hs1 : IsSeg (actS tr) (firstS tr) (lastS tr) p1.1 p1.2) (h1 : p1.1 + p1.2 ≤ tr.height T_MRK - 1)
    (hcg : p1.1 = p0.1 + p0.2) :
    (tr.cell T_MRK (p0.1 + 1) lil = 1 → tr.cell T_MRK (p0.1 + 1) top = 0) ∧
    (tr.cell T_MRK (p0.1 + 1) lil = 0 → tr.cell T_MRK (p1.1 + 1) j = tr.cell T_MRK (p0.1 + 1) j ∧
      tr.cell T_MRK (p1.1 + 1) i = tr.cell T_MRK (p0.1 + 1) i + 1 ∧
      tr.cell T_MRK (p1.1 + 1) sp = tr.cell T_MRK (p0.1 + 1) sp) ∧
    (tr.cell T_MRK (p0.1 + 1) lil = 1 → tr.cell T_MRK (p1.1 + 1) j = tr.cell T_MRK (p0.1 + 1) j + 1 ∧
      tr.cell T_MRK (p1.1 + 1) i = 0 ∧ tr.cell T_MRK (p1.1 + 1) sp = tr.cell T_MRK (p0.1 + 1) s) ∧
    tr.cell T_MRK (p1.1 + 1) q = tr.cell T_MRK (p0.1 + 1) q + tr.cell T_MRK (p0.1 + 1) sg := by
  have hpos1 := hs1.1
  obtain ⟨hE, -, hcst⟩ := endRow hL hs0 h0
  have hAb : A tr (p1.1 + 1) = 1 := (endRow hL hs1 h1).2.1
  have ne := nodeEnd hL (r := p0.1 + p0.2) (by omega) hE
  have cj := hcst j (by simp [nodeConst]); have ci := hcst i (by simp [nodeConst])
  have csp := hcst sp (by simp [nodeConst]); have cs := hcst s (by simp [nodeConst])
  have cl := hcst lil (by simp [nodeConst]); have ctop := hcst top (by simp [nodeConst])
  have cq := hcst q (by simp [nodeConst])
  have csg : tr.cell T_MRK (p0.1 + p0.2) sg = tr.cell T_MRK (p0.1 + 1) sg := by
    rcases segKind hL hs0 h0 with ⟨-, -, hl⟩ | ⟨hl, -, hh⟩
    · rw [hl]
    · rw [hl]
      have := (hh.rows 63 (by omega)).1; have h0' := (hh.rows 0 (by omega)).1
      rw [show p0.1 + 1 + 63 = p0.1 + 64 by omega] at this
      rw [Nat.add_zero] at h0'; rw [this, h0']
  simp only [cj, ci, csp, cs, cl, ctop, cq, csg] at ne
  rw [← hcg] at ne
  obtain ⟨-, n1, n2, n3, n4⟩ := ne
  have ht0 : tr.cell T_MRK (p0.1 + 1) lil = 1 → tr.cell T_MRK (p0.1 + 1) top = 0 := by
    intro hl
    rcases isBool hL (r := p0.1 + 1) (by omega) (x := top) (by simp) with h | h
    · exact h
    · rw [n3 hl h] at hAb; exact absurd hAb fp_zero_ne_one
  refine ⟨ht0, fun hl => (n1 hl).2, fun hl => ?_, n4 hAb⟩
  obtain ⟨-, e1, e2, e3⟩ := n2 hl (ht0 hl)
  exact ⟨e1, e2, e3⟩

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp} {segs : List (Nat × Nat)}

/-- Segment decomposition facts packaged. -/
structure Segs (tr : Trace Fp) (segs : List (Nat × Nat)) : Prop where
  consec : Consec 0 segs
  bound : segEnd 0 segs ≤ tr.height T_MRK - 1
  seg : ∀ p ∈ segs, IsSeg (actS tr) (firstS tr) (lastS tr) p.1 p.2
  pad : ∀ r, segEnd 0 segs ≤ r → r < tr.height T_MRK - 1 → actS tr r = false

theorem Segs.le (hS : Segs tr segs) {p : Nat × Nat} (hp : p ∈ segs) : p.1 + p.2 ≤ tr.height T_MRK - 1 := by
  have := seg_le_end segs 0 hS.consec p hp; have := hS.bound; omega

theorem Segs.nonempty (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) : 0 < segs.length := by
  rcases Nat.eq_zero_or_pos segs.length with h | h
  · exfalso
    rw [List.length_eq_zero_iff] at h; subst h
    have h2 := height_ge hL
    have := hS.pad 0 (by simp [segEnd]) (by omega)
    simp only [actS, decide_eq_false_iff_not, Nat.zero_add] at this
    exact this (rootRow hL (by omega)).2.1
  · exact h

theorem Segs.first (hS : Segs tr segs) (h : 0 < segs.length) : segs[0].1 = 0 := by
  have := hS.consec
  cases segs with
  | nil => simp at h
  | cons p rest => exact this.1

theorem Segs.next (hS : Segs tr segs) {t : Nat} (ht : t + 1 < segs.length) :
    segs[t + 1].1 = segs[t].1 + segs[t].2 := consec_get segs 0 hS.consec t ht

/-- Small counters: `1 ≤ j_t ≤ t + 1`, `i_t ≤ t`. -/
theorem bounds (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) :
    ∀ t (ht : t < segs.length), 1 ≤ (tr.cell T_MRK (segs[t].1 + 1) j).toNat ∧
      (tr.cell T_MRK (segs[t].1 + 1) j).toNat ≤ t + 1 ∧ (tr.cell T_MRK (segs[t].1 + 1) i).toNat ≤ t := by
  have hP : tr.height T_MRK < P := by have := height_le hL; unfold P; omega
  have hlen : segs.length ≤ tr.height T_MRK := by
    have := hS.bound
    have : segs.length ≤ segEnd 0 segs := by
      have key : ∀ (l : List (Nat × Nat)) s0, Consec s0 l → (∀ p ∈ l, 0 < p.2) → s0 + l.length ≤ segEnd s0 l := by
        intro l; induction l with
        | nil => intro s0 _ _; simp [segEnd]
        | cons p rest ih =>
          intro s0 hc hpos
          obtain ⟨s, ℓ⟩ := p
          obtain ⟨rfl, hc⟩ := hc
          have := ih (s + ℓ) hc (fun q hq => hpos q (by simp [hq]))
          have := hpos (s, ℓ) (by simp)
          simp only [segEnd, List.length_cons] at *; omega
      have := key segs 0 hS.consec (fun p hp => (hS.seg p hp).1); omega
    omega
  intro t
  induction t with
  | zero =>
    intro ht
    have h2 := height_ge hL
    obtain ⟨-, -, hj, hi, -⟩ := rootRow hL (by omega)
    rw [hS.first ht, Nat.zero_add, hj, hi]; decide
  | succ t ih =>
    intro ht
    obtain ⟨a1, a2, a3⟩ := ih (by omega)
    have hp0 := List.getElem_mem (l := segs) (by omega : t < segs.length)
    have hp1 := List.getElem_mem (l := segs) ht
    obtain ⟨-, f1, f2, -⟩ := succF hL (hS.seg _ hp0) (hS.le hp0) (hS.seg _ hp1) (hS.le hp1) (hS.next ht)
    rcases isBool hL (r := segs[t].1 + 1) (by have := hS.le hp0; have := (hS.seg _ hp0).1; omega)
      (x := lil) (by simp) with hl | hl
    · obtain ⟨e1, e2, -⟩ := f1 hl
      rw [toNat_eq_of e1, toNat_succ_of e2 (by omega)]; omega
    · obtain ⟨e1, e2, -⟩ := f2 hl
      rw [toNat_succ_of e1 (by omega), e2]; simp [Fp.toNat_zero]; omega

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp} {segs : List (Nat × Nat)}

def dsOf (tr : Trace Fp) (segs : List (Nat × Nat)) : List ND := segs.map fun p => ndAt tr (p.1 + 1)

theorem dsOf_get (t : Nat) (ht : t < segs.length) : (dsOf tr segs).getD t default = ndAt tr (segs[t].1 + 1) := by
  rw [getD_eq_getElem' _ _ (by simp [dsOf]; exact ht)]; simp [dsOf]

theorem one_iff {r x : Nat} : one tr x r = true ↔ tr.cell T_MRK r x = 1 := by simp [one]

theorem idx_le (hS : Segs tr segs) : ∀ t (ht : t < segs.length), t ≤ segs[t].1 := by
  intro t; induction t with
  | zero => intro _; omega
  | succ t ih =>
    intro ht; rw [hS.next ht]
    have := ih (by omega); have := (hS.seg _ (List.getElem_mem (by omega : t < segs.length))).1; omega

theorem rules (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) : Rules (dsOf tr segs) := by
  have hP : 4 * tr.height T_MRK + 4 < P := by have := height_le hL; unfold P; omega
  have hH2 := height_ge hL
  have hB0 := bounds hL hS
  have hB : ∀ t (ht : t < segs.length), _ ∧ _ ∧ _ ∧ 4 * t + 4 < ZkFormal.Algebra.P := fun t ht => by
    obtain ⟨a, b, c⟩ := hB0 t ht
    have hp := List.getElem_mem (l := segs) ht
    have := hS.le hp; have := idx_le hS t ht; have := hP
    exact ⟨a, b, c, by omega⟩
  have hlen : (dsOf tr segs).length = segs.length := by simp [dsOf]
  have hrow : ∀ t (ht : t < segs.length), segs[t].1 + 1 < tr.height T_MRK := fun t ht => by
    have hp := List.getElem_mem (l := segs) ht
    have := hS.le hp; have := (hS.seg _ hp).1; omega
  have hA : ∀ t (ht : t < segs.length), A tr (segs[t].1 + 1) = 1 := fun t ht =>
    (endRow hL (hS.seg _ (List.getElem_mem ht)) (hS.le (List.getElem_mem ht))).2.1
  refine ⟨fun t ht => ?_, fun t ht hl => ?_, fun t ht hl => ?_, fun t ht hl => ?_, fun t ht hl => ?_, fun h0 => ?_⟩
  · rw [hlen] at ht; rw [dsOf_get t ht]
    have e := (shapeRow hL (hrow t ht) (hA t ht)).2.1
    simp only [ndAt]
    rw [cellOne hL (hrow t ht) (x := pr) (by simp), cellOne hL (hrow t ht) (x := odd) (by simp),
      cellOne hL (hrow t ht) (x := lil) (by simp)] at e
    revert e
    cases one tr pr (segs[t].1 + 1) <;> cases one tr odd (segs[t].1 + 1) <;>
      cases one tr lil (segs[t].1 + 1) <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
      intro e <;> first | rfl | (exfalso; grind)
  · rw [hlen] at ht; rw [dsOf_get t ht] at hl ⊢
    simp only [ndAt] at hl ⊢
    rw [one_iff] at hl
    obtain ⟨e1, -, e3, -, -⟩ := shapeRow hL (hrow t ht) (hA t ht)
    have hs := toNat_succ_of (e3 hl).symm (by have := (hB t ht).2.2.1; have := (hB t ht).2.2.2; omega)
    refine ⟨hs.symm, ?_⟩
    have ho : (tr.cell T_MRK (segs[t].1 + 1) odd).toNat = if one tr odd (segs[t].1 + 1) then 1 else 0 := by
      rw [cellOne hL (hrow t ht) (x := odd) (by simp)]; split <;> rfl
    have hob : (tr.cell T_MRK (segs[t].1 + 1) odd).toNat ≤ 1 := by
      rw [ho]; cases one tr odd (segs[t].1 + 1) <;> decide
    have hs2 : 2 * (tr.cell T_MRK (segs[t].1 + 1) s).toNat < P := by
      have := (hB t ht).2.2.1; have := (hB t ht).2.2.2; omega
    have hs1 : 1 ≤ (tr.cell T_MRK (segs[t].1 + 1) s).toNat := by omega
    have key := lin2 e1 hob hs2 hs1
    by_cases hb : one tr odd (segs[t].1 + 1) = true
    · simp only [hb, ite_true] at ho ⊢; omega
    · simp only [hb, ite_false, Bool.false_eq_true] at ho ⊢; omega
  · rw [hlen] at ht; rw [dsOf_get t ht] at hl ⊢
    simp only [ndAt] at hl ⊢
    rw [one_iff] at hl
    obtain ⟨-, -, -, e4, e5⟩ := shapeRow hL (hrow t ht) (hA t ht)
    rw [one_iff]
    constructor
    · intro h; rw [e4 h]; rfl
    · intro h
      rcases isBool hL (hrow t ht) (x := top) (by simp) with h' | h'
      · exfalso
        have := e5 h'
        rw [← Fp.ofNat_toNat (tr.cell T_MRK (segs[t].1 + 1) s), h] at this
        exact absurd this (by
          rw [show Fp.ofNat 1 = (1 : Fp) from rfl]; intro hc; grind)
      · exact h'
  · rw [hlen] at ht; rw [dsOf_get t (by omega)] at hl; rw [dsOf_get t (by omega), dsOf_get (t + 1) ht]
    simp only [ndAt] at hl ⊢
    have hp0 := List.getElem_mem (l := segs) (by omega : t < segs.length)
    have hp1 := List.getElem_mem (l := segs) ht
    obtain ⟨-, f1, -, -⟩ := succF hL (hS.seg _ hp0) (hS.le hp0) (hS.seg _ hp1) (hS.le hp1) (hS.next ht)
    have hl0 := bool01 hL (hrow t (by omega)) (x := lil) (by simp) (by rw [← one_iff, hl]; decide)
    obtain ⟨e1, e2, e3⟩ := f1 hl0
    exact ⟨toNat_eq_of e1, toNat_succ_of e2 (by have := (hB t (by omega)).2.2.1; have := (hB t (by omega)).2.2.2; omega), toNat_eq_of e3⟩
  · rw [hlen] at ht; rw [dsOf_get t (by omega)] at hl; rw [dsOf_get t (by omega), dsOf_get (t + 1) ht]
    simp only [ndAt] at hl ⊢
    rw [one_iff] at hl
    have hp0 := List.getElem_mem (l := segs) (by omega : t < segs.length)
    have hp1 := List.getElem_mem (l := segs) ht
    obtain ⟨g0, -, f2, -⟩ := succF hL (hS.seg _ hp0) (hS.le hp0) (hS.seg _ hp1) (hS.le hp1) (hS.next ht)
    obtain ⟨e1, e2, e3⟩ := f2 hl
    refine ⟨by simp [one, g0 hl], toNat_succ_of e1 (by have := (hB t (by omega)).2.1; have := (hB t (by omega)).2.2.2; omega), ?_, toNat_eq_of e3⟩
    rw [e2]; rfl
  · rw [hlen] at h0 ⊢
    rw [dsOf_get _ (by omega)]
    simp only [ndAt, one_iff]
    have hp := List.getElem_mem (l := segs) (by omega : segs.length - 1 < segs.length)
    obtain ⟨hE, -, hcst⟩ := endRow hL (hS.seg _ hp) (hS.le hp)
    have hend := segEnd_last segs 0 hS.consec h0
    have he1 : segs[segs.length - 1].1 + segs[segs.length - 1].2 + 1 < tr.height T_MRK := by
      have := hS.le hp
      rcases Nat.lt_or_ge (segs[segs.length - 1].1 + segs[segs.length - 1].2 + 1) (tr.height T_MRK) with h | h
      · exact h
      · exfalso
        have hA' := (endRow hL (hS.seg _ hp) (hS.le hp)).1
        have hl := lastRow hL (by omega)
        rw [show tr.height T_MRK - 1 = segs[segs.length - 1].1 + segs[segs.length - 1].2 by omega] at hl
        -- the end row is active (E = 1 means sl or pr, both active)
        have hl2 := (local_ hL (r := segs[segs.length - 1].1 + segs[segs.length - 1].2) (by omega))
        simp only [E, A] at hA' hl
        rcases isBool hL (r := segs[segs.length - 1].1 + segs[segs.length - 1].2) (by omega) (x := pr) (by simp)
          with a | a
        · have hsl : tr.cell T_MRK (segs[segs.length - 1].1 + segs[segs.length - 1].2) sl = 1 := by
            rw [a] at hA'; grind
          have hw := hl2.2.2.2.2.2.2.1; rw [hsl] at hw
          have hwl : tr.cell T_MRK (segs[segs.length - 1].1 + segs[segs.length - 1].2) wl = 1 := by
            rcases isBool hL (r := segs[segs.length - 1].1 + segs[segs.length - 1].2) (by omega) (x := wl) (by simp)
              with b | b <;> rw [b] at hw <;> grind
          have := (hl2.2.2.2.2.1 hwl).1; rw [this, a] at hl; grind
        · rw [a] at hl; grind
    have hnA : A tr (segs[segs.length - 1].1 + segs[segs.length - 1].2 + 1) = 0 := by
      have := hS.pad (segs[segs.length - 1].1 + segs[segs.length - 1].2) (by omega) (by omega)
      simp only [actS, decide_eq_false_iff_not] at this
      rcases A_cases hL (r := segs[segs.length - 1].1 + segs[segs.length - 1].2 + 1) he1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h this
      · exact h
    have ne := nodeEnd hL he1 hE
    rw [hcst lil (by simp [nodeConst]), hcst top (by simp [nodeConst])] at ne
    rcases isBool hL (hrow (segs.length - 1) (by omega)) (x := lil) (by simp) with hl | hl
    · rw [(ne.2.1 hl).1] at hnA; exact absurd hnA fp_one_ne_zero
    · refine ⟨hl, ?_⟩
      rcases isBool hL (hrow (segs.length - 1) (by omega)) (x := top) (by simp) with ht | ht
      · rw [(ne.2.2.1 hl ht).1] at hnA; exact absurd hnA fp_one_ne_zero
      · exact ht

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp} {segs : List (Nat × Nat)}

abbrev cn (tr : Trace Fp) (r x : Nat) : Nat := (tr.cell T_MRK r x).toNat

def nodeOf (tr : Trace Fp) (p : Nat × Nat) : MrkNode :=
  if tr.cell T_MRK (p.1 + 1) pr = 1 then .promoted (cn tr (p.1 + 1) cId) (cn tr (p.1 + 1) cLen)
  else .hashed (cn tr (p.1 + 1) cId) (cn tr (p.1 + 1) cLen) ((List.range 32).map fun x => cn tr (p.1 + 1) (reg x))
    (cn tr (p.1 + 1 + 32) cId) (cn tr (p.1 + 1 + 32) cLen) ((List.range 32).map fun x => cn tr (p.1 + 1 + 32) (reg x))

def viewOf (tr : Trace Fp) (segs : List (Nat × Nat)) : MrkV :=
  { n := cn tr 1 sp, J := cn tr 0 mj, rootId := cn tr 0 cId, rootLen := cn tr 0 cLen, nodes := segs.map (nodeOf tr) }

def isH : MrkNode → Bool
  | .hashed .. => true
  | .promoted .. => false

theorem isH_nodeOf (p : Nat × Nat) : isH (nodeOf tr p) = !(one tr pr (p.1 + 1)) := by
  unfold nodeOf; by_cases h : tr.cell T_MRK (p.1 + 1) pr = 1 <;> simp [h, isH, one]

/-- The `q` counter counts the hashed nodes before. -/
theorem qCount (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) :
    ∀ t (ht : t < segs.length), cn tr (segs[t].1 + 1) q = hashedBefore (segs.map (nodeOf tr)) t := by
  have hP : 4 * tr.height T_MRK + 4 < P := by have := height_le hL; unfold P; omega
  intro t
  induction t with
  | zero =>
    intro ht
    have h2 := height_ge hL
    rw [hS.first ht]; simp [cn, (rootRow hL (by omega)).2.2.2.2.2.1, hashedBefore, Fp.toNat_zero]
  | succ t ih =>
    intro ht
    have hp0 := List.getElem_mem (l := segs) (by omega : t < segs.length)
    have hp1 := List.getElem_mem (l := segs) ht
    have e := (succF hL (hS.seg _ hp0) (hS.le hp0) (hS.seg _ hp1) (hS.le hp1) (hS.next ht)).2.2.2
    have hr : segs[t].1 + 1 < tr.height T_MRK := by have := hS.le hp0; have := (hS.seg _ hp0).1; omega
    have hsg : tr.cell T_MRK (segs[t].1 + 1) sg = if one tr pr (segs[t].1 + 1) then 0 else 1 := by
      rcases A_cases hL hr with ⟨-, ⟨a, b⟩ | ⟨a, b⟩⟩ | ⟨h, -⟩
      · simp [one, a, b]
      · simp [one, a, b]
      · rw [(endRow hL (hS.seg _ hp0) (hS.le hp0)).2.1] at h; exact absurd h fp_one_ne_zero
    have hq := ih (by omega)
    have hlt : hashedBefore (segs.map (nodeOf tr)) t ≤ t := by
      simp only [hashedBefore]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
    have hidx := idx_le hS t (by omega)
    have := hS.le hp0
    have key : hashedBefore (segs.map (nodeOf tr)) (t + 1) =
        hashedBefore (segs.map (nodeOf tr)) t + (if one tr pr (segs[t].1 + 1) then 0 else 1) := by
      simp only [hashedBefore]
      rw [List.take_succ, List.filter_append, List.length_append]
      congr 1
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega : t < segs.length)]
      simp only [Option.toList_some, Option.map_some]
      unfold nodeOf
      by_cases h : tr.cell T_MRK (segs[t].1 + 1) pr = 1 <;> simp [h, one]
    rw [key, ← hq]
    simp only [cn]
    rw [e, hsg]
    by_cases hb : one tr pr (segs[t].1 + 1) = true
    · simp only [hb, if_true]; rw [show tr.cell T_MRK (segs[t].1 + 1) q + 0 = tr.cell T_MRK (segs[t].1 + 1) q by grind]
      rfl
    · simp only [hb, Bool.false_eq_true, if_false]
      have : cn tr (segs[t].1 + 1) q ≤ t := by rw [hq]; exact hlt
      exact toNat_succ_of rfl (by simp only [cn] at this; omega)

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp} {segs : List (Nat × Nat)}

theorem shapeEq (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) :
    shapeOf (dsOf tr segs) = mrkShape (viewOf tr segs).n := by
  have hne := hS.nonempty hL
  have h2 := height_ge hL
  obtain ⟨-, -, hj, hi, -, -, -⟩ := rootRow hL (by omega)
  apply shape _ (rules hL hS) _ (by simp [dsOf]; omega)
  rw [dsOf_get 0 hne, hS.first hne]
  simp only [ndAt, Nat.zero_add, hj, hi, viewOf, cn]
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem posOf (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) (t : Nat) (ht : t < segs.length) :
    (mrkShape (viewOf tr segs).n).getD t (0, 0, false) =
      (cn tr (segs[t].1 + 1) j, cn tr (segs[t].1 + 1) i, isH (nodeOf tr segs[t])) := by
  rw [← shapeEq hL hS, shapeOf, getD_eq_getElem' _ _ (by simp [dsOf]; exact ht)]
  simp [dsOf, ndAt, isH_nodeOf, cn]

theorem wfOf (hL : TableLocal Mrk.table tr T_MRK pub) (hS : Segs tr segs) : MrkWf pub (viewOf tr segs) := by
  have h2 := height_ge hL
  refine ⟨fun hb hlt => ?_, ?_, ⟨?_, fun q hq => ?_⟩, fun nd hnd => ?_, ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _,
    fun nd hnd x hx => ?_⟩⟩
  · -- n is the public n
    have hsp := (rootRow hL (pub := pub) (by omega)).2.2.2.2.1
    simp only [viewOf, cn, hsp, nPubE]
    simp only [eval_sum_cons, eval_sum_nil, eval_smul, eval_pub, List.range, List.range.loop, List.map]
    have e : ∀ x, x < 4 → pub.getD (PV_N + x) 0 = Fp.ofNat (pubNat pub (PV_N + x)) := fun x _ => by
      simp [pubNat, Fp.ofNat_toNat]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
    rw [show (0 : Fp) = Fp.ofNat 0 from rfl]
    simp only [natCast_eq, ofNat_mul', ofNat_add', Fp.toNat_ofNat]
    simp only [nPubNat, List.range, List.range.loop, List.foldr, Nat.pow_succ, Nat.pow_zero] at hlt ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rcases Nat.eq_zero_or_pos (viewOf tr segs).n with h | h
    · exfalso
      have := shapeEq hL hS
      rw [h] at this
      have hne := hS.nonempty hL
      have : (shapeOf (dsOf tr segs)).length = 0 := by rw [this]; simp [mrkShape, mrkLevels]
      simp [shapeOf, dsOf] at this; subst this; simp at hne
    · exact h
  · rw [← shapeEq hL hS]; simp [shapeOf, dsOf, viewOf]
  · simp only [viewOf, List.length_map] at hq
    have := posOf hL hS q hq
    rw [this]; simp only [viewOf, List.getElem_map]
    cases h : nodeOf tr segs[q] <;> simp [isH, h]
  · simp only [viewOf, List.mem_map] at hnd
    obtain ⟨p, -, rfl⟩ := hnd
    unfold nodeOf
    by_cases h : tr.cell T_MRK (p.1 + 1) pr = 1
    · simp only [h, if_true]
    · simp only [h, if_false]; exact ⟨by simp, by simp⟩
  · simp only [viewOf, List.mem_map] at hnd
    obtain ⟨p, -, rfl⟩ := hnd
    unfold nodeOf at hx; split at hx <;> simp [MrkNode.raw] at hx <;>
      first | (rcases hx with rfl | rfl <;> exact Fp.toNat_lt _) |
        (rcases hx with rfl | rfl | rfl | rfl | ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ <;> exact Fp.toNat_lt _)

end ZkFormal.Near.MrkProof

namespace ZkFormal.Near.MrkProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Mrk MrkShape

variable {tr : Trace Fp} {pub : List Fp} {segs : List (Nat × Nat)}

theorem multNat1 (x : Nat) (r : Nat) :
    Interaction.multNat.go tr T_MRK r pub [c x] 0 = if tr.cell T_MRK r x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell T_MRK r x = 1 <;> simp [h]

def regs (tr : Trace Fp) (r : Nat) : List Fp := (List.range 32).map fun x => tr.cell T_MRK r (reg x)
def pubOut (pub : List Fp) : List Fp := (List.range 32).map fun x => pub.getD (PV_OUT + x) 0

/-- Messages of row `r` per bus and side. -/
theorem rowT (r b : Nat) (sd : Bool) :
    rowTraffic Mrk.interactions tr T_MRK r pub b sd =
      (if b = B_BYTES ∧ sd = true ∧ tr.cell T_MRK r sg = 1 then
        [[(K_MRK : Fp) + (16 : Nat) * tr.cell T_MRK r q, (32 : Nat) * tr.cell T_MRK r wn + tr.cell T_MRK r pw,
          tr.cell T_MRK r (reg 0)]] else []) ++
      (if b = B_DIGEST ∧ sd = false ∧ tr.cell T_MRK r wf = 1 then
        [[tr.cell T_MRK r cId, tr.cell T_MRK r cLen] ++ regs tr r] else []) ++
      (if b = B_DIGEST ∧ sd = false ∧ tr.cell T_MRK r rt = 1 then
        [[tr.cell T_MRK r cId, tr.cell T_MRK r cLen] ++ pubOut pub] else []) ++
      (if b = B_MPOS ∧ sd = false ∧ tr.cell T_MRK r gM = 1 then
        [[tr.cell T_MRK r mj, tr.cell T_MRK r mi, tr.cell T_MRK r cId, tr.cell T_MRK r cLen]] else []) ++
      (if b = B_MPOS ∧ sd = true ∧ tr.cell T_MRK r gO = 1 then
        [[tr.cell T_MRK r j, tr.cell T_MRK r i, tr.cell T_MRK r oId, tr.cell T_MRK r oLen]] else []) := by
  simp only [rowTraffic, Mrk.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons, List.map_nil,
    List.map_append, List.map_map, eval_c, eval_add, eval_k, eval_smul, eval_mid, eval_pub, List.append_assoc,
    regs, pubOut, Function.comp_def]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))) <;> (split <;> split <;> simp_all [eq_comm]) <;> grind

end ZkFormal.Near.MrkProof

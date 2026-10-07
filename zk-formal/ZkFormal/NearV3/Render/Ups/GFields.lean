import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.FieldFacts

/-! Serialization frame of `cFields`.  The remaining successor and window-role constraints
are not included in this theorem. -/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

/-- One-hot field state, initial tag/start, and zero index at every field start. -/
def cFieldFrame : List Expr := UpsV3.cFields.take 4

theorem fields_frame_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (ok : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cFieldFrame, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [sub (sumc states) (c qb),
    .mul (c pf) (.mul (c qb) (Dsl.not (c sTAG))),
    .mul (c pf) (.mul (c qb) (Dsl.not (c fs))), .mul (c fs) (c idx)] at hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl
  · have hs := ok.state hp
    generalize fieldAt Q.shape p = fa at hC hs
    obtain ⟨st,ix,fl,wi⟩ := fa
    have hcases : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6 ∨ st = 7 ∨ st = 8 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply cast0 <;> ups_ev [hC] <;> cellsimp <;> simp [ind]
  · apply cast0; ups_ev [hC]; cellsimp
    by_cases h : p = 0
    · subst p; rw [ok.first]; simp [ind]
    · simp [ind, h]
  · apply cast0; ups_ev [hC]; cellsimp
    by_cases h : p = 0
    · subst p; rw [ok.first]; simp [ind]
    · simp [ind, h]
  · apply cast0; ups_ev [hC]; cellsimp
    simp only [ind]; split <;> simp_all

/-- The field frame holds on the complete padded update trace.  This is an explicit
subgroup result; it does not assert the still-open `cFields` successor/window constraints. -/
theorem cFieldFrame_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cFieldFrame := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_take he
    simp [UpsV3.constraints, hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldFrame.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact fields_frame_q (hf _ (inst_mem hi) k hk) hp hC

/-- Fixed serialization widths, including the variable hex-prefix tail width. -/
def cFieldLengths : List Expr := (UpsV3.cFields.drop 17).take 9

theorem fields_lengths_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (ok : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cFieldLengths, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have hm := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; exact hp)).2
  have hn : ((fieldAt Q.shape p).1, (fieldAt Q.shape p).2.2.1) ∈
      nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← ok.shape]; exact hm
  have hl := nodeFields_length hn
  generalize fieldAt Q.shape p = fa at hC hl
  obtain ⟨st,ix,fl,wi⟩ := fa
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := hl
  change ex ∈ [
    .mul (c fe) (.mul (c sTAG) (c idx)),
    .mul (c fe) (.mul (c sHPL) (sub (c idx) (Dsl.k 3))),
    .mul (c fe) (.mul (c sHPF) (c idx)),
    .mul (c fe) (.mul (c sKEY) (sub (.add (c idx) (Dsl.k 2)) (c UpsV3.qhk))),
    .mul (c fe) (.mul (c sVLEN) (sub (c idx) (Dsl.k 3))),
    .mul (c fe) (.mul (c sVH) (sub (c idx) (Dsl.k 31))),
    .mul (c fe) (.mul (c sBM) (sub (c idx) (Dsl.k 1))),
    .mul (c fe) (.mul (c sCH) (sub (c idx) (Dsl.k 31))),
    .mul (c fe) (.mul (c sMEM) (sub (c idx) (Dsl.k 7)))] at hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply cast0 <;> ups_ev [hC] <;> cellsimp <;> simp only [ind] <;>
    (repeat' split) <;> simp_all <;> omega

/-- Every fixed-width field ends at its specified byte index. -/
theorem cFieldLengths_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cFieldLengths := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints, hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldLengths.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact fields_lengths_q (hf _ (inst_mem hi) k hk) hp hC

/-- Field-state and index advances within a part. -/
def cFieldAdvance : List Expr := (UpsV3.cFields.drop 4).take 13

set_option hygiene false in
macro "field_advance_mem" : tactic => `(tactic| (
  change ex ∈ states.map (fun x => Expr.mul (.mul (c qb) (Dsl.not (c fe))) (sub (n x) (c x))) ++
    [.mul (.mul (c qb) (Dsl.not (c fe))) (sub (n idx) (.add (c idx) (Dsl.k 1))),
     .mul (.mul (c qb) (Dsl.not (c fe))) (n fs),
     .mul (mul3 (c qb) (c fe) (Dsl.not (c pl))) (n idx),
     .mul (mul3 (c qb) (c fe) (Dsl.not (c pl))) (Dsl.not (n fs))] at hex
  simp only [states, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

theorem fields_advance_qmid {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (ok : FieldsOk Q) (hp : p + 1 < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x < 187 → D x = QC I Q k (p + 1)
      (fieldAt Q.shape (p + 1)).1 (fieldAt Q.shape (p + 1)).2.1
      (fieldAt Q.shape (p + 1)).2.2.1 (fieldAt Q.shape (p + 1)).2.2.2 u' x) :
    ∀ ex ∈ cFieldAdvance, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have hb := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; omega)).1
  by_cases he : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1
  · have hz := fieldAt_next_boundary Q.shape p (by rw [← ok.bytes]; exact hp) he
    field_advance_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;> simp [ind, he, hz]
  · have hn := fieldAt_next_inside Q.shape p (by omega)
    rw [hn] at hD
    field_advance_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;>
      simp [ind, he] <;> omega

/-- The last byte of a part does not advance a field within that part. -/
theorem fields_advance_qlast {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (hp : p + 1 = Q.q.length)
    (he : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cFieldAdvance, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  field_advance_mem <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;> simp [ind, he, hp]

/-- Field-state persistence and index advance/reset on the complete padded trace. -/
theorem cFieldAdvance_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cFieldAdvance := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints, hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldAdvance.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply fields_advance_qmid (hf _ (inst_mem hi) k hk) hp1 hC
      intro x hx
      rw [hD x hx, nextRow ok.shape hq hr (rk' := .q k (p + 1))
        (by simp only [nextRK]; rw [if_pos hp1]) x, rowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      exact fields_advance_qlast he (((ok.inst _ (inst_mem hi)).memEnd k hk p hp).1 he).2 hC

end UpsGen
end ZkFormal.NearV3.Render

import ZkFormal.NearV3.Render.Ups.ByteWindows

/-! Fresh-window byte and shift-register completeness in `cBytes`. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cFreshByte : List Expr := (UpsV3.cBytes.drop 20).take 1
def cByteShifts : List Expr := (UpsV3.cBytes.drop 21).take 31

theorem ev_fresh {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x) :
    ev C D fst lst trn P winFr = winFrV I Q st wi := by
  ups_ev [hC]; cellsimp
  exact (winFr_formula I Q st wi).symm

theorem fresh_byte_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (ok : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cFreshByte, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [.mul winFr (sub (c UpsV3.b) (c (reg 0)))] at hex
  simp only [List.mem_singleton] at hex; subst ex
  apply cast0
  change ev C D fst lst trn P winFr * (C 101 + -C 129) = 0
  rw [ev_fresh hC]
  by_cases hw : winFrV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = 1
  · have hl := ok.fresh_width hp hw
    have hb := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; exact hp)).1
    have hr := fresh_reg (k := k) (p := p) (ix := (fieldAt Q.shape p).2.1)
      (fl := (fieldAt Q.shape p).2.2.1) (u := u) (i := 0) (by decide) hw
    rw [hw,hC 101 (by decide),hC 129 (by decide),hr]
    cellsimp
    rw [if_pos (by omega)]
    simp [Int.add_right_neg]
  · have hz : winFrV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = 0 := by
      rcases ind01 (WinFrB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = true) with h | h
      · exact h
      · exact False.elim (hw h)
    rw [hz,Int.zero_mul]

theorem byte_shifts_off {C D P : Nat → Int} {fst lst trn : Int}
    (h : ev C D fst lst trn P winFr = 0) :
    ∀ ex ∈ cByteShifts, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ (List.range 31).map (fun i => mul3 winFr (Dsl.not (c fe))
    (sub (n (reg i)) (c (reg (i+1))))) at hex
  simp only [List.mem_map,List.mem_range] at hex
  obtain ⟨i,hi,rfl⟩ := hex
  apply cast0
  change (ev C D fst lst trn P winFr * (1-C 116)) * (D (129+i) + -C (129+(i+1))) = 0
  rw [h]; simp

theorem byte_shifts_qmid {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (ok : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x < 187 → D x = QC I Q k (p+1)
      (fieldAt Q.shape (p+1)).1 (fieldAt Q.shape (p+1)).2.1
      (fieldAt Q.shape (p+1)).2.2.1 (fieldAt Q.shape (p+1)).2.2.2 u' x) :
    ∀ ex ∈ cByteShifts, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  by_cases hw : winFrV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = 1
  · change ex ∈ (List.range 31).map (fun i => mul3 winFr (Dsl.not (c fe))
      (sub (n (reg i)) (c (reg (i+1))))) at hex
    simp only [List.mem_map,List.mem_range] at hex
    obtain ⟨i,hi,rfl⟩ := hex
    apply cast0
    change (ev C D fst lst trn P winFr * (1-C 116)) * (D (129+i) + -C (129+(i+1))) = 0
    rw [ev_fresh hC,hw,hC 116 (by decide)]
    change (1 * (1-ind ((fieldAt Q.shape p).2.1+1 = (fieldAt Q.shape p).2.2.1))) *
      (D (129+i) + -C (129+(i+1))) = 0
    by_cases he : (fieldAt Q.shape p).2.1+1 = (fieldAt Q.shape p).2.2.1
    · simp [ind,he]
    · have hb := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; exact hp)).1
      have hl := ok.fresh_width hp hw
      have hn := fieldAt_next_inside Q.shape p (by omega)
      have hr : D (129+i) = C (129+(i+1)) := by
        rw [hD _ (by omega),hC _ (by omega),hn]
        exact fresh_reg_shift hi (by omega) hw
      rw [hr,Int.add_right_neg,Int.mul_zero]
  · apply byte_shifts_off ?_ ex hex
    rw [ev_fresh hC]
    rcases ind01 (WinFrB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = true) with h | h
    · exact h
    · exact False.elim (hw h)

/-- The byte output equals the first register of each fresh digest window. -/
theorem cFreshByte_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cFreshByte := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFreshByte.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact fresh_byte_q (hf _ (inst_mem hi) k hk) hp hC

/-- All31 fresh-window register shifts hold across the complete padded trace. -/
theorem cByteShifts_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteShifts := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteShifts.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p+1 < (part (inst insts i) k).q.length
    · apply byte_shifts_qmid (hf _ (inst_mem hi) k hk) hp hC
      intro x hx
      rw [hD x hx,nextRow ok.shape hq hr (rk' := .q k (p+1)) (by simp [nextRK,hp1]),rowCell_q]
    · have he : p+1 = (part (inst insts i) k).q.length := by omega
      have hs := (((ok.inst _ (inst_mem hi)).memEnd k hk p hp).1 he).1
      apply byte_shifts_off
      rw [ev_fresh hC]
      simp [winFrV,WinFrB,ind,hs]

end UpsGen
end ZkFormal.NearV3.Render

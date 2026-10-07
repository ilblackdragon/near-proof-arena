import ZkFormal.NearV3.Render.Ups.GMemLengths

/-! Length-register constraints on the full generated and padded trace. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

theorem mem_lengths_mid {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (f : FieldsOk Q) (hp : p + 1 < Q.q.length)
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x < 200 → D x = QC I Q k (p + 1)
      (fieldAt Q.shape (p + 1)).1 (fieldAt Q.shape (p + 1)).2.1
      (fieldAt Q.shape (p + 1)).2.2.1 (fieldAt Q.shape (p + 1)).2.2.2 u' x) :
    ∀ ex ∈ cMemLengths, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  have hc := fieldAt_bounds Q.shape p (by rw [← f.bytes]; omega)
  have hl := nodeFields_length (by rw [← f.shape]; exact hc.2)
  apply mem_lengths_pair hC hD hc.1 hl.2.2.2.2.1 hl.2.2.2.2.2.2.2.2
  split
  · rename_i hi
    rw [fieldAt_next_inside Q.shape p hi]
    exact ⟨rfl,rfl⟩
  · rename_i hi
    exact fieldAt_next_boundary Q.shape p (by rw [← f.bytes]; exact hp) (by omega)

/-- No length-register transition is enabled on the last memory byte. -/
theorem mem_lengths_last {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p wi u : Nat} (hp : p + 1 = Q.q.length)
    (hC : ∀ x, x < 200 → C x = QC I Q k p 8 7 8 wi u x) :
    ∀ ex ∈ cMemLengths, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  mem_lengths_cases <;> apply cast0 <;> ups_ev [UpsV3.cMem, UpsV3.Lb, Nat.reduceMod, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, hC] <;> cellsimp <;>
    simp [ind, hp, Int.add_right_neg]

theorem cMemLengths_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cMemLengths := by
  apply groupOk_by ok hH (fun e he => by
    have he' : e ∈ UpsV3.cMem := List.mem_of_mem_drop he
    simp [UpsV3.constraints, he'])
  · intro i hi t ht q _ _ C D P hC _ e he
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (by decide : cMemLengths.all (vz zW (fun _ => false) false false false) = true) e he)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply mem_lengths_mid (hf _ (inst_mem hi) k hk) hp1 hC
      intro x hx
      rw [hD x hx, nextRow ok.shape hq hr (rk' := .q k (p + 1))
        (by simp only [nextRK]; rw [if_pos hp1]) x, rowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      have hm := ((ok.inst _ (inst_mem hi)).memEnd k hk p hp).1 he
      have f := hf _ (inst_mem hi) k hk
      generalize inst insts i = I at *
      generalize part I k = Q at *
      have hc := fieldAt_bounds Q.shape p (by rw [← f.bytes]; exact hp)
      have hl := nodeFields_length (by rw [← f.shape]; exact hc.2)
      have hlen : (fieldAt Q.shape p).2.2.1 = 8 := hl.2.2.2.2.2.2.2.2 hm.1
      have hix : (fieldAt Q.shape p).2.1 = 7 := by omega
      rw [hm.1, hlen, hix] at hC
      exact mem_lengths_last he hC

end UpsGen
end ZkFormal.NearV3.Render

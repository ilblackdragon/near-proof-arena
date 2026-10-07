import ZkFormal.NearV3.Render.Ups.GMemCurrent

/-! Carry-register transitions between consecutive memory bytes. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cMemCarry : List Expr := (UpsV3.cMem.drop 4).take 2

/-- The next row's carry-in is this row's exact decoded carry-out. -/
theorem mem_carry_row {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p ix wi wi' u u' : Nat}
    (hC : ∀ x, x < 200 → C x = QC I Q k p 8 ix 8 wi u x)
    (hD : ∀ x, x < 200 → D x = QC I Q k (p + 1) 8 (ix + 1) 8 wi' u' x)
    (hi : ix < 7)
    (h0 : 0 ≤ cbV I Q ix) (h1 : cbV I Q ix < 131072)
    (h2 : 0 ≤ co2V I Q ix) (h3 : co2V I Q ix < 65536) :
    ∀ e ∈ cMemCarry, ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  intro e he
  change e ∈ [.mul (.mul (c sMEM) (Dsl.not (c fe))) (sub (n ci) coE),
    .mul (.mul (c sMEM) (Dsl.not (c fe))) (sub (n ci2) ccE)] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  have hw : winFrV I Q 8 wi' = 0 := rfl
  have hn8 : ix + 1 ≠ 8 := by omega
  have hn0 : ix + 1 ≠ 0 := by omega
  rcases he with rfl | rfl <;> apply cast0
  · simp only [ev, Dsl.sub]
    rw [mem_coE hC (by omega) h0 h1]
    ups_ev [hC,hD]
    cellsimp
    simp [hw, memReg, ind, hn8, hn0, Int.add_right_neg]
  · simp only [ev, Dsl.sub]
    rw [mem_ccE hC h2 h3]
    ups_ev [hC,hD]
    cellsimp
    simp [hw, memReg, ind, hn8, hn0, Int.add_right_neg]

/-- No carry transition is enabled outside a nonfinal memory byte. -/
theorem mem_carry_off {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hC : ∀ x, x < 200 → C x = QC I Q k p st ix fl wi u x)
    (hoff : st ≠ 8 ∨ ix + 1 = fl) :
    ∀ e ∈ cMemCarry, ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  intro e he
  change e ∈ [.mul (.mul (c sMEM) (Dsl.not (c fe))) (sub (n ci) coE),
    .mul (.mul (c sMEM) (Dsl.not (c fe))) (sub (n ci2) ccE)] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;>
    rcases hoff with hs | hl <;> simp_all [ind]

/-- Carry transitions within a generated part. -/
theorem mem_carry_mid {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (f : FieldsOk Q) (m : MemOk I Q) (hp : p + 1 < Q.q.length)
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x < 200 → D x = QC I Q k (p + 1)
      (fieldAt Q.shape (p + 1)).1 (fieldAt Q.shape (p + 1)).2.1
      (fieldAt Q.shape (p + 1)).2.2.1 (fieldAt Q.shape (p + 1)).2.2.2 u' x) :
    ∀ e ∈ cMemCarry, ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  have hc := fieldAt_bounds Q.shape p (by rw [← f.bytes]; omega)
  have hl := nodeFields_length (by rw [← f.shape]; exact hc.2)
  by_cases hs : (fieldAt Q.shape p).1 = 8
  · by_cases he : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1
    · exact mem_carry_off hC (.inr he)
    · have hlen : (fieldAt Q.shape p).2.2.1 = 8 := hl.2.2.2.2.2.2.2.2 hs
      have hn := fieldAt_next_inside Q.shape p (by omega)
      rw [hn, hs, hlen] at hD
      rw [hs, hlen] at hC
      obtain ⟨h0,h1,h2,h3⟩ := m.carries (fieldAt Q.shape p).2.1 (by omega)
      exact mem_carry_row hC hD (by omega) h0 h1 h2 h3
  · exact mem_carry_off hC (.inl hs)

/-- Both carry transitions hold over the complete padded trace. -/
theorem cMemCarry_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hm : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cMemCarry := by
  apply groupOk_by ok hH (fun e he => by
    have he' : e ∈ UpsV3.cMem := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints, he'])
  · intro i hi t ht q _ _ C D P hC _ e he
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (by decide : cMemCarry.all (vz zW (fun _ => false) false false false) = true) e he)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply mem_carry_mid (hf _ (inst_mem hi) k hk) (hm _ (inst_mem hi) k hk) hp1 hC
      intro x hx
      rw [hD x hx, nextRow ok.shape hq hr (rk' := .q k (p + 1))
        (by simp only [nextRK]; rw [if_pos hp1]) x, rowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      exact mem_carry_off hC (.inr (((ok.inst _ (inst_mem hi)).memEnd k hk p hp).1 he).2)

end UpsGen
end ZkFormal.NearV3.Render

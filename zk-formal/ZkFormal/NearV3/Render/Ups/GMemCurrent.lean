import ZkFormal.NearV3.Render.Ups.GMemRow
import ZkFormal.NearV3.Render.Ups.MemInput
import ZkFormal.NearV3.Render.Ups.FieldFacts

/-! The nine current-row memory equations on the whole padded trace.
Register transitions and carry-range derivation remain separate obligations. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cMemCurrent : List Expr := UpsV3.cMem.take 4 ++ (UpsV3.cMem.drop 6).take 5

theorem mem_current {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p ix wi u : Nat}
    (hC : ∀ x, x < 200 → C x = QC I Q k p 8 ix 8 wi u x)
    (hi : ix < 8) (hn : Q.neg ≤ 1)
    (h0 : 0 ≤ cbV I Q ix) (h1 : cbV I Q ix < 131072)
    (h2 : 0 ≤ co2V I Q ix) (h3 : co2V I Q ix < 65536)
    (hb : (Q.q.getD p 0 : Int) = RV I Q / 256 ^ ix % 256) :
    ∀ e ∈ cMemCurrent, ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  intro e he
  change e ∈ [UpsV3.cMem.getD 0 (Dsl.k 0), UpsV3.cMem.getD 1 (Dsl.k 0),
    UpsV3.cMem.getD 2 (Dsl.k 0), UpsV3.cMem.getD 3 (Dsl.k 0),
    UpsV3.cMem.getD 6 (Dsl.k 0), UpsV3.cMem.getD 7 (Dsl.k 0),
    UpsV3.cMem.getD 8 (Dsl.k 0), UpsV3.cMem.getD 9 (Dsl.k 0),
    UpsV3.cMem.getD 10 (Dsl.k 0)] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_input hC
  · exact mem_extra hC
  · exact mem_initial hC _ (by change _ ∈ [UpsV3.cMem.getD 2 (Dsl.k 0), UpsV3.cMem.getD 3 (Dsl.k 0)]; simp)
  · exact mem_initial hC _ (by change _ ∈ [UpsV3.cMem.getD 2 (Dsl.k 0), UpsV3.cMem.getD 3 (Dsl.k 0)]; simp)
  · exact mem_inside hC hi h0 h1
  · exact mem_outside hC hi hn h2 h3 hb
  · exact mem_parent hC hi hn h0 h1 h2 h3 hb
  · exact mem_send_gate hC
  · exact mem_recv_gate hC

/-- Every current-row memory equation vanishes outside MEM fields. -/
theorem mem_non {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat} (hs : st ≠ 8)
    (hC : ∀ x, x < 200 → C x = QC I Q k p st ix fl wi u x) :
    ∀ e ∈ cMemCurrent, ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  intro e he
  refine vzC (zc := fun x => zQ x || [114,168,169].contains x) (fun x hx => ?_)
    (List.all_eq_true.1 (by decide : cMemCurrent.all
      (vz (fun x => zQ x || [114,168,169].contains x) (fun _ => false) false false false) = true) e he)
  simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl | rfl | rfl
  · rw [hC x (by simp [zQ] at hx; omega)]; exact zQ_cell _ _ _ _ _ _ _ _ _ _ hx
  all_goals rw [hC _ (by decide)]; cellsimp; simp [ind, hs]

/-- The current-row memory equations hold on every row, including padding. -/
theorem cMemCurrent_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hm : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cMemCurrent := by
  apply groupOk_by ok hH (fun e he => by
    have he' : e ∈ UpsV3.cMem := by
      rcases List.mem_append.mp he with he | he
      · exact List.mem_of_mem_take he
      · exact List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints, he'])
  · intro i hi t ht q _ _ C D P hC _ e he
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (by decide : cMemCurrent.all (vz zW (fun _ => false) false false false) = true) e he)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    have f := hf _ (inst_mem hi) k hk
    have m := hm _ (inst_mem hi) k hk
    have hn := ((ok.inst _ (inst_mem hi)).bits k hk).2.2.1
    generalize inst insts i = I at *
    generalize part I k = Q at *
    have hb := m.bytes p hp
    have hc := fieldAt_bounds Q.shape p (by rw [← f.bytes]; exact hp)
    have hl := nodeFields_length (by rw [← f.shape]; exact hc.2)
    generalize fieldAt Q.shape p = fa at hC hb hc hl
    obtain ⟨st, ix, fl, wi⟩ := fa
    by_cases hs : st = 8
    · subst st
      have he : fl = 8 := hl.2.2.2.2.2.2.2.2 rfl
      subst fl
      obtain ⟨h0,h1,h2,h3⟩ := m.carries ix hc.1
      exact mem_current hC hc.1 hn h0 h1 h2 h3 (hb rfl)
    · exact mem_non hs hC

end UpsGen
end ZkFormal.NearV3.Render

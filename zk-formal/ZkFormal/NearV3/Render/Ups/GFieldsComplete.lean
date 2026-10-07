import ZkFormal.NearV3.Render.Ups.GFieldSucc
import ZkFormal.NearV3.Render.Ups.GWindowCounts

/-! Completeness of every update-table field constraint, from semantic serialization,
split-child count, and source-child identity inputs. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cWindowChild : List Expr := UpsV3.cFields.drop 61

theorem window_child_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (ok : WindowOk I Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cWindowChild, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [.mul (c rdc) (sub (c rcid) (c UpsV3.cN))] at hex
  simp only [List.mem_singleton] at hex
  subst ex
  apply cast0
  ups_ev [hC]; cellsimp
  by_cases hr : RdcB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 = true
  · have hh := hr
    simp only [RdcB,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hh
    obtain ⟨⟨⟨hs,hix⟩,ht⟩,hk⟩ := hh
    rw [hs] at ht
    have hid := ok.childId p hp hs hix ht (by omega)
    simp only [rdcV,ind,hr,ite_true,Int.one_mul]
    rw [hs,hix,hid]
    omega
  · simp [rdcV,ind,hr]

theorem cWindowChild_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hw : ∀ I ∈ insts, ∀ k, k < nQ I → WindowOk I (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cWindowChild := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop he
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cWindowChild.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact window_child_q (hw _ (inst_mem hi) k hk) hp hC

/-- Every field constraint holds on the padded update trace.  Semantic inputs remain
explicit and must be constructed from the real upsert; `InstOk` is not strengthened. -/
theorem cFields_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hw : ∀ I ∈ insts, ∀ k, k < nQ I → WindowOk I (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H UpsV3.cFields := by
  change GroupOk insts H
    ((((UpsV3.cFields.take 40 ++ cWindowFlow) ++ cWindowCounts) ++ cWindowRoles) ++ cWindowChild)
  exact groupOk_append (groupOk_append (groupOk_append (groupOk_append
    (cFields_scalar_ok ok hf hH) (cWindowFlow_ok ok hf hH))
    (cWindowCounts_ok ok hf hw hH)) (cWindowRoles_ok ok hH)) (cWindowChild_ok ok hw hH)

end UpsGen
end ZkFormal.NearV3.Render

import ZkFormal.NearV3.Render.Ups.GFieldPrefix
import ZkFormal.NearV3.Render.Ups.FieldSucc

/-! The first fourteen field-kind succession constraints. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cFieldSucc : List Expr := (UpsV3.cFields.drop 26).take 14

set_option hygiene false in
macro "field_succ_mem" : tactic => `(tactic| (
  change ex ∈ [
    mul3 (c fe) (c sTAG) (sub (.add (c qtl) (c qte)) (n sHPL)),
    mul3 (c fe) (c sTAG) (sub (c qtb1) (n sBM)),
    mul3 (c fe) (c sTAG) (sub (c qtb2) (n sVLEN)),
    mul3 (c fe) (c sHPL) (Dsl.not (n sHPF)),
    mul3 (c fe) (c sHPF) (sub (Dsl.not (c nokey)) (n sKEY)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c qtl)) (n sVLEN)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c qte)) (n sCH)),
    mul3 (c fe) (c sKEY) (sub (c qtl) (n sVLEN)),
    mul3 (c fe) (c sKEY) (sub (c qte) (n sCH)),
    mul3 (c fe) (c sVLEN) (Dsl.not (n sVH)),
    mul3 (c fe) (c sVH) (sub (c qtl) (n sMEM)),
    mul3 (c fe) (c sVH) (sub (c qtb2) (n sBM)),
    mul3 (c fe) (c sBM) (sub (c UpsV3.nochild) (n sMEM)),
    mul3 (c fe) (c sBM) (sub (Dsl.not (c UpsV3.nochild)) (n sCH))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

set_option hygiene false in
macro "scalar_succ" n:num : tactic => `(tactic| (
  by_cases hst : st = $n
  · have hnext := hs
    rw [hst] at hnext
    simp only [nextFieldStates,Nat.reduceEqDiff,ite_true,ite_false,List.mem_singleton] at hnext
    simp only [ind,hst,Nat.reduceEqDiff,ite_true,ite_false,Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero]
    (repeat' split at hnext) <;> (repeat' split at hn) <;> (repeat' split) <;>
      (try simp only [Int.one_mul,Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add]) <;> omega
  · simp [ind,hst]))

theorem fields_succ_qmid {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (ok : FieldsOk Q) (hp : p + 1 < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x < 200 → D x = QC I Q k (p + 1)
      (fieldAt Q.shape (p + 1)).1 (fieldAt Q.shape (p + 1)).2.1
      (fieldAt Q.shape (p + 1)).2.2.1 (fieldAt Q.shape (p + 1)).2.2.2 u' x) :
    ∀ ex ∈ cFieldSucc, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  by_cases he : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1
  · have hs := ok.successor hp he
    have ht := ok.ty
    have hk := ok.prefixLength
    have hn := ok.nochild
    have hm := (fieldAt_bounds Q.shape p (by rw [← ok.bytes]; omega)).2
    have hmem : ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.2.1) ∈
        nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← ok.shape]; exact hm
    obtain ⟨hprefix,hkey,hvalue,hbitmap⟩ := nodeFields_types hmem
    clear hm hmem
    generalize fieldAt Q.shape p = fa at *
    generalize fieldAt Q.shape (p+1) = fb at *
    obtain ⟨st,ix,fl,wi⟩ := fa
    obtain ⟨st',ix',fl',wi'⟩ := fb
    field_succ_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;>
      clear hC hD ok <;> simp only [nokeyV,ind,he,ite_true,Int.one_mul]
    · scalar_succ 0
    · scalar_succ 0
    · scalar_succ 0
    · scalar_succ 1
    · scalar_succ 2
    · scalar_succ 2
    · scalar_succ 2
    · scalar_succ 3
    · scalar_succ 3
    · scalar_succ 4
    · scalar_succ 5
    · scalar_succ 5
    · scalar_succ 6
    · scalar_succ 6
  · field_succ_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;> simp [ind,he]

/-- The memory tail does not trigger any scalar-field successor rule. -/
theorem fields_succ_qlast {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (hs : (fieldAt Q.shape p).1 = 8)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cFieldSucc, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  field_succ_mem <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;> simp [ind,hs]

/-- Scalar field-kind succession across the complete padded trace. -/
theorem cFieldSucc_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cFieldSucc := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints, hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldSucc.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · apply fields_succ_qmid (hf _ (inst_mem hi) k hk) hp1 hC
      intro x hx
      rw [hD x hx, nextRow ok.shape hq hr (rk' := .q k (p + 1))
        (by simp only [nextRK]; rw [if_pos hp1]) x, rowCell_q]
    · have he : p + 1 = (part (inst insts i) k).q.length := by omega
      exact fields_succ_qlast (((ok.inst _ (inst_mem hi)).memEnd k hk p hp).1 he).1 hC

/-- The first forty constraints: all scalar field framing, widths and succession. -/
theorem cFields_scalar_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H (UpsV3.cFields.take 40) := by
  change GroupOk insts H (UpsV3.cFields.take 26 ++ cFieldSucc)
  exact groupOk_append (cFields_prefix_ok ok hf hH) (cFieldSucc_ok ok hf hH)

end UpsGen
end ZkFormal.NearV3.Render

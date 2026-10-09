import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.FreshValue

/-! TAG and HPL constraints derived from the ordinary NodeV3 serializer. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteFreshValue : List Expr := (UpsV3.cBytes.drop 19).take 1

theorem byte_fresh_value_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (enc : NodeEncoding Q) (hv : FreshValue I Q enc) (hL : L I < 2^24) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteFreshValue, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [mul3 (c sVLEN) (Dsl.not (c cp)) (sub (c UpsV3.b) (c (LR 0)))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  subst ex
  apply cast0
  ups_ev [hC]
  cellsimp
  by_cases hs : (fieldAt Q.shape p).1=4
  · by_cases hc : VcpB I Q=true
    · simp [cpV,CpB,hs,hc,ind,Lean.Omega.Int.natCast_ofNat]
    · have hb := hv.length_byte hL hp hs (by cases hh : VcpB I Q <;> simp_all)
      simp only [hs,Nat.reduceEqDiff,ind_True,or_true,ite_true,Nat.zero_add]
      exact gate_sub_eq hb
  · simp [ind,hs]

theorem cByteFreshValue_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hv : ∀ I (hI : I ∈ insts) k (hk : k < nQ I), FreshValue I (part I k) (he I hI k hk))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteFreshValue := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteFreshValue.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_fresh_value_q (he _ (inst_mem hi) k hk) (hv _ (inst_mem hi) k hk) (ok.inst _ (inst_mem hi)).Lsmall hp hC

end UpsGen
end ZkFormal.NearV3.Render

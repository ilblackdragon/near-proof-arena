import ZkFormal.NearV3.Render.Ups.SourceValueLayout
import ZkFormal.NearV3.Render.Ups.GByteFlags

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteSourceValue : List Expr := (UpsV3.cBytes.drop 59).take 1

theorem byte_source_value_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (enc : NodeEncoding Q) (hv : VcpB I Q=true ∨ Q.kind=3 → SourceValueLayout I Q enc)
    (hf : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteSourceValue, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [mul3 (c rd) (c sVLEN) (sub (c rb) (c (SR 0)))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  subst ex
  apply cast0
  ups_ev [hC]
  cellsimp
  by_cases hs : (fieldAt Q.shape p).1=4
  · by_cases hr : VcpB I Q=true ∨ Q.kind=3
    · have hpv := (hv hr).position hf hs
      have hbounds := fieldAt_bounds Q.shape p (by rw [← hf.bytes]; exact hp)
      have hfields : ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.2.1) ∈
          nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← hf.shape]; exact hbounds.2
      have hw := (nodeFields_length hfields).2.2.2.2.1 hs
      have hx : (fieldAt Q.shape p).2.1<4 := by omega
      have heq : rbV I Q 4 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p=
          slb Q ((fieldAt Q.shape p).2.1%4) := by
        have hnat : (sposV I Q 4 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat=Q.soff+(fieldAt Q.shape p).2.1 := by rw [hpv]; omega
        unfold rbV
        rw [hnat]
        simp [slb,Nat.mod_eq_of_lt hx,hx]
      simp only [hs,Nat.reduceEqDiff,ite_true,Nat.zero_add]
      exact gate_sub_eq heq
    · simp only [not_or] at hr
      simp [rdV,CpB,ExtraB,RdcB,hs,hr.1,hr.2,ind]
  · simp [ind,hs]

theorem cByteSourceValue_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hv : ∀ I (hI : I ∈ insts) k (hk : k < nQ I),
      VcpB I (part I k)=true ∨ (part I k).kind=3 → SourceValueLayout I (part I k) (he I hI k hk))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteSourceValue := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteSourceValue.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_source_value_q (he _ (inst_mem hi) k hk) (hv _ (inst_mem hi) k hk)
      (hf _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render

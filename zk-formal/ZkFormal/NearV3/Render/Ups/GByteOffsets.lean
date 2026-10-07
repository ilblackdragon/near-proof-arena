import ZkFormal.NearV3.Render.Ups.GByteWindows

/-! Inserted-slot offset flags, the last five update-byte constraints. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteOffsets : List Expr := UpsV3.cBytes.drop 71

theorem byte_offsets_q {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hs : st < 9)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ cByteOffsets, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    mul3 (c kRBV) (sumc [sBM,sCH,sMEM]) (Dsl.not (c aft)),
    mul3 (c kRBV) (sumc [sTAG,sVLEN,sVH]) (c aft),
    mul3 (c kRBI) (sumc [sTAG,sVLEN,sVH,sBM]) (c aft),
    mul3 (c kRBI) (c sCH) (sub (c aft) (.mul (Dsl.not (c fw)) (c ts1))),
    mul3 (c kRBI) (c sMEM) (Dsl.not (c aft))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;>
    rcases (show st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 ∨ st=6 ∨ st=7 ∨ st=8 by omega)
      with hst | hst | hst | hst | hst | hst | hst | hst | hst <;>
    simp only [hst,Nat.reduceEqDiff,ind_True,ind_False,Int.zero_mul,Int.mul_zero,Int.zero_add,Int.add_zero] <;>
    by_cases h4 : Q.kind=4 <;> by_cases h5 : Q.kind=5 <;>
    by_cases hw : wi=0 <;> by_cases ht : I.ts=1 <;>
    simp [ind,aftV,AftB,fwV,FwB,hst,h4,h5,hw,ht] <;> omega

/-- Insertion offsets follow the serialized field and child-window position. -/
theorem cByteOffsets_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteOffsets := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop he
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteOffsets.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_offsets_q ((hf _ (inst_mem hi) k hk).state hp) hC

end UpsGen
end ZkFormal.NearV3.Render

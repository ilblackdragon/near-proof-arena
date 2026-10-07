import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.NodeBitmapBytes

/-! TAG and HPL constraints derived from the ordinary NodeV3 serializer. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteSplitBitmap : List Expr := (UpsV3.cBytes.drop 52).take 1

theorem byte_split_bitmap_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (enc : NodeEncoding Q) (hb : SplitBitmap I Q enc) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteSplitBitmap, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [mul3 (c kSPB) (c sBM) (sub (c UpsV3.b) (.add (.mul (c fs) (c bmL)) (.mul (Dsl.not (c fs)) (c bmH))))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  subst ex
  apply cast0
  ups_ev [hC]
  cellsimp
  by_cases hs : (fieldAt Q.shape p).1=6
  · by_cases hk : Q.kind=10
    · have he := hb.byte hk hp hs
      have heq : (Q.q.getD p 0 : Int)=ind ((fieldAt Q.shape p).2.1=0)*bmLV I +
          (1 + -ind ((fieldAt Q.shape p).2.1=0))*bmHV I := by
        rw [he]
        by_cases hx : (fieldAt Q.shape p).2.1=0 <;> simp [ind,hx]
      simpa only [Lean.Omega.Int.natCast_ofNat] using gate_sub_eq (g := ind (Q.kind=10)*ind ((fieldAt Q.shape p).1=6)) heq
    · simp [ind,hk]
  · simp [ind,hs]

theorem cByteSplitBitmap_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hb : ∀ I (hI : I ∈ insts) k (hk : k < nQ I), SplitBitmap I (part I k) (he I hI k hk))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteSplitBitmap := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteSplitBitmap.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_split_bitmap_q (he _ (inst_mem hi) k hk) (hb _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render

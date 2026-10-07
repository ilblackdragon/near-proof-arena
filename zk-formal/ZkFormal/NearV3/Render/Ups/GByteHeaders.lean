import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes
import ZkFormal.NearV3.Render.Node.ByteFacts

/-! TAG and HPL constraints derived from the ordinary NodeV3 serializer. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteHeaders : List Expr := (UpsV3.cBytes.drop 11).take 3

theorem tagByte_formula {ty : Nat} (ht : ty < 4) :
    (tagByte ty : Int) = ind (ty=2) + (2*ind (ty=3) + 3*ind (ty=1)) := by
  rcases (show ty=0 ∨ ty=1 ∨ ty=2 ∨ ty=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem byte_headers_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (enc : NodeEncoding Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteHeaders, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [.mul (c sTAG) (sub (c UpsV3.b) tagE),
    mul3 (c sHPL) (c fs) (sub (c qha) (c UpsV3.b)),
    mul3 (c sHPL) (c fs) (sub (c qhs) (Dsl.k 1))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl <;> apply cast0 <;> ups_ev [qha,qhs,hC] <;> cellsimp
  · by_cases hs : (fieldAt Q.shape p).1 = 0
    · have ht : Q.ty < 4 := by
        rw [enc.ty]
        cases enc.node with
        | leaf => simp [nodeTypeCode]
        | ext => simp [nodeTypeCode]
        | branch sv => cases sv <;> simp [nodeTypeCode]
      have hb : (Q.q.getD p 0 : Int) = ind (Q.ty=2) + (2*ind (Q.ty=3)+3*ind (Q.ty=1)) := by
        rw [enc.tag hp hs]; exact tagByte_formula ht
      exact gate_sub_eq hb
    · simp [ind,hs]
  · by_cases hs : (fieldAt Q.shape p).1 = 1
    · by_cases hi : (fieldAt Q.shape p).2.1 = 0
      · have hb := enc.hpl hp hs
        rw [hi] at hb
        have ha := NodeGen3.le256_take_one (u32Bytes Q.qhk)
          (by intro he; have := u32Bytes_length Q.qhk; rw [he] at this; contradiction)
        simp only [List.getD_eq_getElem?_getD] at hb ha
        simp [hs,hi,winFrV,WinFrB,ind,ha,hb,Int.add_right_neg]
      · simp [ind,hi]
    · simp [ind,hs]
  · by_cases hs : (fieldAt Q.shape p).1 = 1
    · by_cases hi : (fieldAt Q.shape p).2.1 = 0
      · simp [hs,hi,winFrV,WinFrB,ind]
      · simp [ind,hi]
    · simp [ind,hs]

/-- Header byte constraints over the padded trace, from ordinary node serialization. -/
theorem cByteHeaders_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteHeaders := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteHeaders.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_headers_q (he _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render

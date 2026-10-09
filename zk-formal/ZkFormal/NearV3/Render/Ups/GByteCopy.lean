import ZkFormal.NearV3.Render.Ups.CopyByte
import ZkFormal.NearV3.Render.Ups.GByteFlags

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteCopy : List Expr := (UpsV3.cBytes.drop 10).take 1

theorem byte_copy_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (copy : CopyFields I Q) (hf : FieldsOk Q) (hkind : Q.kind<12) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteCopy, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [.mul (c cp) (sub (c UpsV3.b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0)) (.mul (Dsl.not (c fs)) (c ba1))))))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  subst ex
  apply cast0
  ups_ev [hC]
  cellsimp
  by_cases hc : CpB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2=true
  · have heq := copy.byte hf hkind hp hc
    rw [bitmapDelta_flags] at heq
    simpa only [Lean.Omega.Int.natCast_ofNat] using gate_sub_eq (g := cpV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2) heq
  · simp [cpV,ind,hc]

/-- The final copied-byte constraint follows from whole-field semantic preservation.
The actual upsert constructor must still establish CopyFields for its output parts. -/
theorem cByteCopy_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hc : ∀ I ∈ insts, ∀ k, k < nQ I → CopyFields I (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hk : ∀ I ∈ insts, ∀ k, k < nQ I → (part I k).kind<12)
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteCopy := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteCopy.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk' hp q _ _ C D P hC _
    exact byte_copy_q (hc _ (inst_mem hi) k hk') (hf _ (inst_mem hi) k hk')
      (hk _ (inst_mem hi) k hk') hp hC

end UpsGen
end ZkFormal.NearV3.Render

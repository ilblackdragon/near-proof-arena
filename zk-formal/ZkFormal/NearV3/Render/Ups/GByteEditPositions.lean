import ZkFormal.NearV3.Render.Ups.GByteFlags
import ZkFormal.NearV3.Render.Ups.SourcePositions

/-! TAG and HPL constraints derived from the ordinary NodeV3 serializer. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cByteEditPositions : List Expr := (UpsV3.cBytes.drop 61).take 3

theorem byte_edit_positions_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (e : Q.kind ∈ [0,1,2,3,4,5,11] → SourceLayout Q) (f : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cByteEditPositions, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    mul3 (c rd) (sumc [kRDB,kRDE,kRLP,kRBR,kPT]) (sub (c spos) (c qpos)),
    mul3 (c rd) (c kRBV) (sub (.add (c spos) (smul 36 (c aft))) (c qpos)),
    mul3 (c rd) (c kRBI) (sub (.add (c spos) (smul 32 (c aft))) (c qpos))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl <;> apply cast0 <;> ups_ev [hC] <;> cellsimp
  · by_cases hk : Q.kind ∈ [0,1,2,3,11]
    · exact gate_sub_eq ((e (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; omega)).preserved_position f hp hk)
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
      simp [ind,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2]
  · by_cases hk : Q.kind=4
    · simpa only [Lean.Omega.Int.natCast_ofNat] using gate_sub_eq (g := rdV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 * ind (Q.kind=4)) ((e (by simp [hk])).value_position (I:=I) f hp hk)
    · simp [ind,hk]
  · by_cases hk : Q.kind=5
    · simpa only [Lean.Omega.Int.natCast_ofNat] using gate_sub_eq (g := rdV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 * ind (Q.kind=5)) ((e (by simp [hk])).child_position (I:=I) f hp hk)
    · simp [ind,hk]

/-- Read positions follow the source node's actual serializer-field edit. -/
theorem cByteEditPositions_ok {insts : List UpsInst} (ok : UpsOk insts)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → (part I k).kind ∈ [0,1,2,3,4,5,11] → SourceLayout (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cByteEditPositions := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteEditPositions.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_edit_positions_q (he _ (inst_mem hi) k hk) (hf _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render

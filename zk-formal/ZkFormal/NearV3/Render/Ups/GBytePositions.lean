import ZkFormal.NearV3.Render.Ups.GByteOffsets

/-! Inserted-slot offset flags, the last five update-byte constraints. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cBytePositions : List Expr := (UpsV3.cBytes.drop 60).take 1 ++ (UpsV3.cBytes.drop 64).take 7

theorem byte_positions_q {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hs : st < 9)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ cBytePositions, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [
    mul3 (c rd) (c sMEM) (sub (.add (c spos) (Dsl.k 8)) (.add (c plen) (c idx))),
    mul3 (c rd) kM (.mul (c sTAG) (sub (c spos) (Dsl.k 5))),
    mul3 (c rd) kM (.mul (c sHPL) (sub (c spos) (Dsl.k 1))),
    mul3 (c rd) kM (.mul (sumc [sHPF,sKEY,sVLEN,sVH,sCH])
      (sub (.add (c spos) (c UpsV3.qhk)) (.add (c qpos) (c phk)))),
    mul3 (c rd) (c kSPB) (.mul (c sTAG) (sub (c spos) (Dsl.k 5))),
    mul3 (c rd) (c kSPB) (.mul (c sBM) (sub (c spos) (Dsl.k 1))),
    mul3 (c rd) (c kSPB) (.mul (.add (c sVLEN) (c sVH))
      (sub (.add (c spos) (Dsl.k 45)) (.add (c plen) (c qpos)))),
    mul3 (c rd) (c kSPB) (.mul (c sCH)
      (sub (.add (c spos) (Dsl.k 40)) (.add (c plen) (c idx))))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply cast0 <;> ups_ev [hC] <;> cellsimp
  · by_cases hs : st=8
    · have h : sposV I Q st ix wi p + 8 = (Q.pb.length : Int) + ix := by simp [sposV,hs]; omega
      exact gate_sub_eq h
    · simp [ind,hs]
  all_goals
    rcases (show st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 ∨ st=6 ∨ st=7 ∨ st=8 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceEqDiff,ind_True,ind_False,Int.zero_mul,Int.mul_zero,Int.zero_add,Int.add_zero] <;>
    by_cases h6 : Q.kind=6 <;> by_cases h7 : Q.kind=7 <;> by_cases h10 : Q.kind=10 <;>
    simp_all [ind,sposV,Lean.Omega.Int.natCast_ofNat] <;> omega

/-- Source cursor rules fixed by the renderer, independent of byte contents. -/
theorem cBytePositions_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cBytePositions := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := by
      rcases List.mem_append.1 he with h | h <;>
        exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cBytePositions.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_positions_q ((hf _ (inst_mem hi) k hk).state hp) hC

end UpsGen
end ZkFormal.NearV3.Render

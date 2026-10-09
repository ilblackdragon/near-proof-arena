import ZkFormal.NearV3.Render.Ups.ValueTraffic
import ZkFormal.NearV3.Render.Ups.Traffic

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Algebra UpsRows

theorem recsI_value (I : UpsInst) {p : Nat} (hp : p<L I) :
    (recsI I).getD (4+p) default=RK.v p := by
  simp [recsI,List.getD_eq_getElem?_getD,List.getElem?_append,
    show 4+p<4+L I by omega,show ¬4+p<4 by omega,hp]

/-- Concrete physical fresh-value row, including its offset in the complete list. -/
theorem physical_value_cell {insts : List UpsInst} {i p : Nat}
    (hi : i<insts.length) (hp : p<L (inst insts i)) (x : Nat) :
    cell insts (start insts i+(4+p)) x=VC (inst insts i) p x := by
  have hd : 4+p<(recsI (inst insts i)).length := by
    rw [recsI_length_exact]; omega
  have hend : start insts i+(recsI (inst insts i)).length≤R insts := by
    rw [←start_succ,←start_len]
    exact sum_mono (by omega)
  rw [cell,if_pos (by omega),recs_seg hi hd,recsI_value _ hp]
  rfl

/-- Exact physical SPOST and BYTES messages of every fresh-value row. -/
theorem physical_value_messages {insts : List UpsInst} {i p : Nat}
    (hi : i<insts.length) (hp : p<L (inst insts i)) (D : URow) (bb : Nat) (sd : Bool) :
    uMsgs (fun x=>((cell insts (start insts i+(4+p)) x : Int) : Fp).toNat) D bb sd =
      (if B_SPOST=bb ∧ false=sd then
        [[(inst insts i).tau%P,p%P,((inst insts i).v.getD p 0)%P]] else []) ++
      (if B_BYTES=bb ∧ true=sd then
        [[upsIdN (inst insts i).tau 0,p%P,((inst insts i).v.getD p 0)%P]] else []) := by
  simp only [physical_value_cell hi hp]
  exact valueRow_messages (inst insts i) p bb D sd
end ZkFormal.NearV3.Render.UpsGen

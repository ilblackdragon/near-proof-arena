import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes
import ZkFormal.NearV3.Render.Ups.PlanInput
import ZkFormal.NearV3.Render.Node.HeaderBounds

/-! Header bounds follow from existing row and plan inputs. -/
namespace ZkFormal.NearV3.Render.UpsGen

private theorem member_flatMap_length {α β : Type} (xs : List α) (f : α → List β)
    (a : α) (ha : a ∈ xs) : (f a).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.flatMap_cons,List.length_append]
    rcases ha with rfl | ha
    · omega
    · have := ih ha; omega

theorem part_length_le_R {insts : List UpsInst} {i k : Nat} (hi : i<insts.length)
    (hk : k<nQ (inst insts i)) : (part (inst insts i) k).q.length ≤ R insts := by
  have hp := member_flatMap_length (List.range (nQ (inst insts i)))
    (fun k => (List.range (part (inst insts i) k).q.length).map (RK.q k)) k (by simpa)
  have hr := member_flatMap_length (List.range insts.length)
    (fun j => (recsI (inst insts j)).map ((j, ·))) i (by simpa)
  simp only [List.length_map,List.length_range] at hp hr
  have hh : (recsI (inst insts i)).length = 4 + L (inst insts i) +
      ((List.range (nQ (inst insts i))).flatMap fun k =>
        (List.range (part (inst insts i) k).q.length).map (RK.q k)).length := by
    simp [recsI,Nat.add_assoc]
  change (recsI (inst insts i)).length ≤ R insts at hr
  omega

theorem NodeEncoding.hplen_le_length {Q : UpsPartI} (e : NodeEncoding Q) : Q.qhk ≤ Q.q.length := by
  rw [e.hplen,e.bytes]
  exact NodeGen3.hplen_le_ser e.node

theorem output_hplen_lt24 {insts : List UpsInst} (ok : UpsOk insts) {i k : Nat}
    (hi : i<insts.length) (hk : k<nQ (inst insts i))
    (e : NodeEncoding (part (inst insts i) k)) : (part (inst insts i) k).qhk < 16777216 := by
  have hp := part_length_le_R hi hk
  have hn := e.hplen_le_length
  have hc := ok.cap
  omega

theorem moved_hplen_lt24 {insts : List UpsInst} (ok : UpsOk insts) {i k : Nat}
    (hi : i<insts.length) (hk : k<nQ (inst insts i))
    (e : NodeEncoding (part (inst insts i) k))
    (hp : PartOk (inst insts i) k (part (inst insts i) k))
    (hm : (part (inst insts i) k).kind=6 ∨ (part (inst insts i) k).kind=7) :
    (part (inst insts i) k).phk < 16777216 := by
  have hq := part_length_le_R hi hk
  have hn := e.hplen_le_length
  have hc := ok.cap
  have hmv := hp.mv hm
  have hti := (ok.inst _ (inst_mem hi)).ti
  have hb := ((ok.inst _ (inst_mem hi)).bits k hk).1
  omega

end ZkFormal.NearV3.Render.UpsGen

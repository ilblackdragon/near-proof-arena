import ZkFormal.NearV3.Rcpt.Candidates.UpsGeneratedTraffic
import ZkFormal.NearV3.Candidates.CompactPhysicalShaBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

/-- Removing fresh-value rows and relaying their SHA bytes changes neither
walk interaction family. -/
theorem compact_walk_messages (C D : URow) (bus : Nat)
    (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    compactMsgs C D bus sd=uMsgs C D bus sd := by
  rcases hb with rfl|rfl <;> cases sd <;>
    simp [compactMsgs,compactInteractions,uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,
      B_EDGE,B_BMAP,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD]

def compactGeneratedRow (Is : List UpsInst) (q : Nat) (r : Nat×RK) : URow :=
  fun c=>((compactRowCell Is q r c : Int):Fp).toNat

theorem compact_walk_row (Is : List UpsInst) (q i t : Nat) (D : URow)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    compactMsgs (compactGeneratedRow Is q (i,.w t)) D bus sd=
      uMsgs (upsCellRow (inst Is i) t) (fun _=>0) bus sd := by
  rw [compact_walk_messages _ _ bus hb sd]
  exact walk_generated_interactions Is q i t D bus hb sd

theorem compact_part_silent (Is : List UpsInst) (q i k p : Nat) (D : URow)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    compactMsgs (compactGeneratedRow Is q (i,.q k p)) D bus sd=[] := by
  rw [compact_walk_messages _ _ bus hb sd]
  exact interaction_modes_zero _ D rfl rfl rfl bus hb sd

theorem compact_padding_silent (D : URow) (bus : Nat)
    (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    compactMsgs (fun _=>0) D bus sd=[] := by
  rw [compact_walk_messages _ _ bus hb sd]
  exact padding_interactions_silent D bus hb sd

theorem compact_instance_traffic (Is : List UpsInst) (i : Nat)
    (pos : RK→Nat) (next : RK→URow) (bus : Nat)
    (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    ((compactRecsI (inst Is i)).flatMap (fun r=>
      compactMsgs (compactGeneratedRow Is (pos r) (i,r)) (next r) bus sd))=
      upsWalkMessages [inst Is i] bus sd := by
  simp only [compactRecsI,List.flatMap_append,List.flatMap_map,List.flatMap_assoc]
  simp [compact_walk_row Is _ _ _ _ bus hb sd,compact_part_silent Is _ _ _ _ _ bus hb sd]
  have hz {α : Type} (xs : List α) : xs.flatMap (fun _=>([] : List ZkFormal.Near.Msg))=[] := by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simpa using ih
  simp only [hz,List.append_nil]
  simp [upsWalkMessages,List.range_succ,List.ofFn_succ]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

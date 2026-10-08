import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayConstructor
import ZkFormal.NearV3.Rcpt.Candidates.NodePostChildren
import ZkFormal.NearV3.Assembly.ValueIndex

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- Only actual receipt-write slots request VPOST/VSLOT. Unchanged slots are
not marked written merely because the post array also contains their bytes. -/
def writtenValueIds (pre : PTrie) (writes : List (List Nat×Bytes)) : List Nat :=
  writes.filterMap (fun w=>valueIndex pre w.1)

/-- Concrete original-record inputs. Node IDs follow oldPost's preorder, while
write activation uses the original prestate's stable compact value IDs. -/
def oldTreeInputs (pre oldPost : PTrie) (writes : List (List Nat×Bytes)) : Inputs where
  child := fun n=>((occs oldPost).map nodeEnc).getD n []
  value := fun v=>if v∈writtenValueIds pre writes then (valsOf oldPost)[v]? else none

theorem oldTreeInputs_child {pre oldPost child : PTrie} {writes : List (List Nat×Bytes)}
    {n : Nat} (h : (occs oldPost)[n]?=some child) :
    (oldTreeInputs pre oldPost writes).child n=nodeEnc child := by
  simp [oldTreeInputs,List.getD_eq_getElem?_getD,List.getElem?_map,h]

theorem oldTreeInputs_value {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    {v : Nat} {bytes : Bytes} (ha : v∈writtenValueIds pre writes)
    (h : (valsOf oldPost)[v]?=some bytes) :
    (oldTreeInputs pre oldPost writes).value v=some bytes := by
  simp [oldTreeInputs,ha,h]

theorem oldTreeInputs_unwritten (pre oldPost : PTrie) (writes : List (List Nat×Bytes))
    (v : Nat) (h : v∉writtenValueIds pre writes) :
    (oldTreeInputs pre oldPost writes).value v=none := by simp [oldTreeInputs,h]

/-- A concrete post-child occurrence supplies the actual authenticated byte
preimage, with no assumed arbitrary Inputs child function. -/
theorem oldTreeInputs_child_post {pre oldPost before after : PTrie}
    {writes : List (List Nat×Bytes)} {n : Nat}
    (hp : isNode before=true) (hq : isNode after=true)
    (h : (occs oldPost)[n]?=some after) :
    (kid (oldTreeInputs pre oldPost writes) (viewKid n before)).bytes true=
      after.hashOf.map UInt8.toNat :=
  native_child_post _ n before after hp hq (oldTreeInputs_child h)

/-- Native account values use the same compact ID and preserved length. -/
theorem oldTreeInputs_slot_post {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    {v : Nat} {before after : Bytes} (ha : v∈writtenValueIds pre writes)
    (h : (valsOf oldPost)[v]?=some after) (hl : after.length=before.length) :
    (slot (oldTreeInputs pre oldPost writes) (viewSlot v (.val before))).bytes true=
      (Slot.val after).valueRef.map UInt8.toNat :=
  native_slot_post _ v before after (oldTreeInputs_value ha h) hl

/-- Same-index payload lengths come from the actual sized native replay. -/
theorem oldTreeInputs_replay_slot {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (hr : SizedAccountRun pre writes oldPost) {v : Nat} {before after : Bytes}
    (ha : v∈writtenValueIds pre writes) (hb : (valsOf pre)[v]?=some before)
    (hp : (valsOf oldPost)[v]?=some after) :
    (slot (oldTreeInputs pre oldPost writes) (viewSlot v (.val before))).bytes true=
      (Slot.val after).valueRef.map UInt8.toNat := by
  have hh:=congrArg (fun xs : List Nat=>xs[v]?) hr.value_lengths
  simp only [List.getElem?_map,hb,hp,Option.map_some,Option.some.injEq] at hh
  exact oldTreeInputs_slot_post ha hp hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

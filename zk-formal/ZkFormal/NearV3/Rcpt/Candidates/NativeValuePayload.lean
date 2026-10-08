import ZkFormal.NearV3.Rcpt.Candidates.NativeUntouchedValues
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupValueProvider

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- The actual post byte payload, with a write marker only where needed. -/
def ValuePayload (u : Inputs) (i : Nat) (pre post : Bytes) : Prop :=
  (u.value i=some post ∨ (u.value i=none ∧ post=pre)) ∧ post.length=pre.length

/-- Complete slot post encoding, including the unmodified-value case. -/
theorem slot_payload_post (u : Inputs) (i : Nat) (pre post : Bytes)
    (h : ValuePayload u i pre post) :
    (slot u (viewSlot i (.val pre))).bytes true=(Slot.val post).valueRef.map UInt8.toNat := by
  rcases h.1 with hw|⟨hu,rfl⟩
  · exact native_slot_post u i pre post hw h.2
  · simp [slot,viewSlot,hu,NSlot3.bytes,Slot.valueRef,List.map_append]

/-- Every actual compact value occurrence supplies a complete payload fact:
changed slots are active and untouched slots are literally unchanged. -/
theorem oldTreeInputs_payload {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes oldPost) {i : Nat} {before after : Bytes}
    (hb : (valsOf pre)[i]?=some before) (hp : (valsOf oldPost)[i]?=some after) :
    ValuePayload (oldTreeInputs pre oldPost writes) i before after := by
  have hl:=congrArg (fun xs : List Nat=>xs[i]?) h.value_lengths
  simp only [List.getElem?_map,hb,hp,Option.map_some,Option.some.injEq] at hl
  refine ⟨?_,hl⟩
  by_cases ha:i∈writtenValueIds pre writes
  · exact Or.inl (oldTreeInputs_value ha hp)
  · have he:=AccountWriteRun.untouched h.forget i ha
    rw [native_valsOf_eq,native_valsOf_eq,hb,hp] at he
    exact Or.inr ⟨oldTreeInputs_unwritten _ _ _ i ha,Option.some.inj he⟩

/-- No separate post length or untouched-value hypothesis is required. -/
theorem oldTreeInputs_all_slot_bytes {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes oldPost) {i : Nat} {before after : Bytes}
    (hb : (valsOf pre)[i]?=some before) (hp : (valsOf oldPost)[i]?=some after) :
    (slot (oldTreeInputs pre oldPost writes) (viewSlot i (.val before))).bytes true=
      (Slot.val after).valueRef.map UInt8.toNat :=
  slot_payload_post _ i before after (oldTreeInputs_payload h hb hp)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

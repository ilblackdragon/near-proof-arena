import ZkFormal.NearV3.Render.Ups.GByteHpl
import ZkFormal.NearV3.Render.Ups.GByteCopy
import ZkFormal.NearV3.Render.Ups.GByteHeaders
import ZkFormal.NearV3.Render.Ups.GByteFreshPrefix
import ZkFormal.NearV3.Render.Ups.GByteFreshValue
import ZkFormal.NearV3.Render.Ups.GByteMovedPrefix
import ZkFormal.NearV3.Render.Ups.GByteSplitBitmap
import ZkFormal.NearV3.Render.Ups.GByteSourceHeader
import ZkFormal.NearV3.Render.Ups.GByteSourceValue
import ZkFormal.NearV3.Render.Ups.GBytePositions
import ZkFormal.NearV3.Render.Ups.GByteEditPositions

/-! All 81 update-byte constraints. The structured semantic inputs are explicit:
this is completeness for the renderer given correctly constructed node edits, not yet
an unconditional construction theorem for real trie upserts. -/
set_option maxHeartbeats 2000000
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

/-- Semantic obligations on one constructed part. No polynomial evaluations occur here.
The actual upsert constructor must derive every field from its source/output node edits. -/
structure ByteInput (I : UpsInst) (Q : UpsPartI) where
  output : NodeEncoding Q
  kind : Q.kind<12
  nochild : Q.nochild=if nodeChildren output.node=0 then 1 else 0
  freshPrefix : FreshPrefix I Q output
  freshValue : FreshValue I Q output
  splitBitmap : SplitBitmap I Q output
  sourceBytes : SourceBytes Q
  sourceLayout : Q.kind ∈ [0,1,2,3,4,5,11] → SourceLayout Q
  sourceHeader : HeaderInput I Q
  movedPrefix : Q.kind=6 ∨ Q.kind=7 → MovedPrefix I Q output
  sourceValue : (Q.ty=0 ∨ Q.ty=3) → VcpB I Q=true ∨ Q.kind=3 → SourceValueLayout I Q output
  copyFields : CopyFields I Q

theorem ByteInput.fieldsOk {I : UpsInst} {Q : UpsPartI} (h : ByteInput I Q) : FieldsOk Q :=
  h.output.fieldsOk h.nochild

def byteGroups : List Expr := cByteFlags ++ cByteCopy ++ cByteHeaders ++ cByteMovedPrefix ++
  cByteFreshPrefix ++ cByteFreshValue ++ cFreshByte ++ cByteShifts ++ cByteSplitBitmap ++
  cByteReadBits ++ cByteSourceHeader ++ cByteSourceValue ++ cBytePositions ++ cByteEditPositions ++ cByteOffsets ++ cByteHpl

theorem byteGroups_cover : UpsV3.cBytes ⊆ byteGroups := by decide

/-- Every update-byte constraint holds on the complete padded trace under the explicit
ordinary serialization and edit inputs. Constructing ByteInput from upsert remains required. -/
theorem cBytes_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hi : ∀ I ∈ insts, ∀ k, k<nQ I → ByteInput I (part I k))
    {H : Nat} (hH : R insts+1≤H) : GroupOk insts H UpsV3.cBytes := by
  let he := fun I hI k hk => (hi I hI k hk).output
  have hf := fun I hI k hk => (hi I hI k hk).fieldsOk
  have hk := fun I hI k hk => (hi I hI k hk).kind
  have hb := fun I hI k hk => (hi I hI k hk).sourceBytes
  have hall : GroupOk insts H byteGroups := by
    unfold byteGroups
    exact (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append (cByteFlags_ok ok hf hk hH)
      (cByteCopy_ok ok (fun I hI k hk => (hi I hI k hk).copyFields) hf hk hH))
      (cByteHeaders_ok ok he hH))
      (cByteMovedPrefix_ok ok he (fun I hI k hk => (hi I hI k hk).movedPrefix) hb hf hH))
      (cByteFreshPrefix_ok ok he (fun I hI k hk => (hi I hI k hk).freshPrefix) hH))
      (cByteFreshValue_ok ok he (fun I hI k hk => (hi I hI k hk).freshValue) hH))
      (cFreshByte_ok ok hf hH))
      (cByteShifts_ok ok hf hH))
      (cByteSplitBitmap_ok ok he (fun I hI k hk => (hi I hI k hk).splitBitmap) hH))
      (cByteReadBits_ok ok hb hH))
      (cByteSourceHeader_ok ok (fun I hI k hk => (hi I hI k hk).sourceHeader) hb hf hH))
      (cByteSourceValue_ok ok he (fun I hI k hk => (hi I hI k hk).sourceValue) hf hH))
      (cBytePositions_ok ok hf hH))
      (cByteEditPositions_ok ok (fun I hI k hk => (hi I hI k hk).sourceLayout) hf hH))
      (cByteOffsets_ok ok hf hH))
      (cByteHpl_ok ok he hf hH))
  intro q hq C D P hC hD e he
  exact hall q hq C D P hC hD e (byteGroups_cover he)

end UpsGen
end ZkFormal.NearV3.Render

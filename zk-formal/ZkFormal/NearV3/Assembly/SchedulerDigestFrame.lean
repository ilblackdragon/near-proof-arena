import ZkFormal.NearV3.Assembly.CompactPartJobIds
import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts

namespace ZkFormal.NearV3.Assembly
open NearSpec UpsRows Render.UpsGen

/-- Runtime dispatch data retained by the same concrete encoded instance. -/
def NativeDigestFrame (run : TreeRun) (I : Render.UpsInst) : Prop :=
  I.ci=run.terminal.ix ∧ I.ti=run.matched ∧ nQ I=run.parts.length ∧
  ∀k p,run.parts[k]?=some p→(part I k).kind=p.kind.ix

/-- The frame is derived from the actual encoder, not assumed to identify an
arbitrary AIR instance with a native plan. Signed memory changes no kind. -/
theorem nativeInstance_digest_frame (recordId : PTrie→Nat) (baseI : Render.UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] value=some run)
    (base : Nat→Render.UpsPartI) {Qs : List Render.UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) :
    NativeDigestFrame run (nativeInstance recordId baseI root run value Qs) := by
  have hlen:=encodeNativeParts_length recordId hr base he
  refine ⟨rfl,rfl,?_,?_⟩
  · exact (nativeInstance_nQ _ _ _ _ _ _).trans hlen
  · intro k p hp
    have hk:k<Qs.length:=by rw [hlen];exact (List.getElem?_eq_some_iff.mp hp).1
    obtain ⟨p',Q,hp',hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
    rw [hp] at hp'
    cases hp'
    rw [hpart]
    change Q.kind=p.kind.ix
    exact encodeTreePart_kind henc

private theorem case_decode (cs : UCase) : UCase.all.getD cs.ix .LP=cs := by cases cs <;> rfl
private theorem kind_decode (kind : UKind) : UKind.all.getD kind.ix .RDB=kind := by cases kind <;> rfl

/-- The concrete physical demand-ID permutation is now expressed in the
actual runtime part/case, retaining field reduction and branch ordering. -/
theorem physical_native_part_job_ids {run : TreeRun} {I : Render.UpsInst}
    (hframe : NativeDigestFrame run I) (hi : InstOk I) {k : Nat} {p : TreePart}
    (hpart : run.parts[k]?=some p) (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k))
    (hw : WindowOk I (part I k))
    (hn : (part I k).kind=0∨(part I k).kind=5→0<nWin (part I k).shape) :
    (CompactPhysicalDigests.digestJobIds ((List.range (part I k).q.length).flatMap
      (CompactPhysicalDigests.nodeDigestMsgs I k))).Perm
      ((partDigestUses run.terminal k p.kind).map (CompactPhysicalDigests.fieldJob I)) := by
  have h:=CompactPhysicalDigests.physical_part_job_ids I k hi hf hp hw hn
  rwa [hframe.1,hframe.2.2.2 k p hpart,case_decode,kind_decode] at h

end ZkFormal.NearV3.Assembly

import ZkFormal.NearV3.Assembly.SchedulerFreshOnlyTargets
import ZkFormal.NearV3.Assembly.SchedulerSignedFreshDigest
import ZkFormal.NearV3.Assembly.SchedulerNativeBytesAt
import ZkFormal.NearV3.Assembly.SchedulerDigestFrame

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- All value-only parts, including ESl1's copied child, request precisely the
same actual native value job0. No additional SHA request is introduced. -/
theorem nativeInstance_fresh_only_digest (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p)
    (hk : p.kind=.RLP∨p.kind=.RBR∨p.kind=.RBV∨p.kind=.NLF∨(p.kind=.SPB ∧ run.terminal=.ESl1))
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=
      [(digMsg (upsertJobId I.tau 0) v.length ((sha256 v).map UInt8.toNat)).toFp] := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hframe:=nativeInstance_digest_frame recordId baseI hr base he
  have hkb:k<nQ I:=by rw [hframe.2.2.1];exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨_,hf,hplan,hwin,_⟩:=hparts k hkb
  have hpk:(part I k).kind=p.kind.ix:=hframe.2.2.2 k p hp
  have hcase:I.ci=run.terminal.ix:=rfl
  have htargets : (part I k).kind=2∨(part I k).kind=3∨(part I k).kind=4∨(part I k).kind=8∨
      ((part I k).kind=10 ∧ I.ci=8) := by
    rw [hpk,hcase]
    rcases hk with h|h|h|h|⟨h,hc⟩ <;> simp_all [h,UpsRows.UKind.ix,UpsRows.UCase.ix]
  have hL:L I=v.length:=by simp [I,nativeInstance,signedInstance,positionedInstance,traceInstance,L]
  have hsha:=nativeInstance_fresh_digest recordId baseI hr base he hp
    (by rcases hk with h|h|h|h|⟨h,hc⟩ <;> simp_all [freshDigestKind,h])
    (nativeInstance_bytes_at recordId baseI hr hw base he hp)
  change ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=_
  rw [CompactPhysicalDigests.fresh_only_target I k hf hplan hwin htargets,hL,List.map_cons,List.map_nil]
  exact congrArg (fun m=>[m]) hsha

end ZkFormal.NearV3.Assembly

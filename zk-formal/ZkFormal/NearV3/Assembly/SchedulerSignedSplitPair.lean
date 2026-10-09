import ZkFormal.NearV3.Assembly.SchedulerSplitPairSlices
import ZkFormal.NearV3.Assembly.SchedulerSplitChildLength
import ZkFormal.NearV3.Assembly.SchedulerNativeBytesAt
import ZkFormal.NearV3.Assembly.CompactSplitChildTargets
import ZkFormal.NearV3.Assembly.CompactDigestSlice
import ZkFormal.NearV3.Render.Ups.NativeChildLengths

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Complete physical LSc/ESn0 payload order: two actual native node jobs.
Every byte and both lengths are derived from the same native instance. -/
theorem nativeInstance_split_pair_digests (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    {k : Nat} {p : TreePart} (hp : run.parts[k]?=some p) (hkind : p.kind=.SPB)
    (hc : run.terminal=.LSc ∨ run.terminal=.ESn0)
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    ∃a b,run.parts[0]?=some a ∧ run.parts[1]?=some b ∧ k=2 ∧
      ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=
      (if I.ts=1 then
        [digMsg (upsertJobId I.tau 2) (nodeEnc b.output).length ((sha256 (nodeEnc b.output)).map UInt8.toNat),
         digMsg (upsertJobId I.tau 1) (nodeEnc a.output).length ((sha256 (nodeEnc a.output)).map UInt8.toNat)]
       else
        [digMsg (upsertJobId I.tau 1) (nodeEnc a.output).length ((sha256 (nodeEnc a.output)).map UInt8.toNat),
         digMsg (upsertJobId I.tau 2) (nodeEnc b.output).length ((sha256 (nodeEnc b.output)).map UInt8.toNat)]).map Msg.toFp := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hk:k<Qs.length:=by rw [encodeNativeParts_length recordId hr (nativeSourceBase recordId run base) he];exact (List.getElem?_eq_some_iff.mp hp).1
  have hkI:k<nQ I:=by rw [nativeInstance_nQ];exact hk
  obtain ⟨_,hf,hplan,hwin,_⟩:=hparts k hkI
  obtain ⟨p',Q,hp',_,henc,hpart⟩:=nativeInstance_part recordId baseI hr (nativeSourceBase recordId run base) he k hk
  rw [hp] at hp';cases hp'
  have hpk:(part I k).kind=10:=by rw [hpart];change Q.kind=10;rw [encodeTreePart_kind henc,hkind];rfl
  have hci:I.ci=6∨I.ci=9:=by
    change run.terminal.ix=6∨run.terminal.ix=9
    rcases hc with h|h <;> rw [h] <;> simp [UpsRows.UCase.ix]
  have hprev:k-1<nQ I:=by omega
  obtain ⟨_,hfp,hpp,_⟩:=hparts (k-1) hprev
  have hlenparts:=spb_previous_length (I:=I) (by omega) hpk hplan hfp hpp
  have hk2:k=2:=hlenparts.2.2.2 hci
  obtain ⟨a,b,ha,hb,h3,h35⟩:=traceUpsert_split_pair_slices hr hw (List.mem_of_getElem? hp) hkind hc
  have hqb:=nativeInstance_bytes_at recordId baseI hr hw (nativeSourceBase recordId run base) he hb
  have hblen:(nodeEnc b.output).length=50:=by
    have hh:=hlenparts.2.1
    rw [hk2] at hh
    change (part I 1).q.length=50 at hh
    rw [hqb,List.length_map] at hh
    exact hh
  change PartOk I k (part I k) at hplan
  have hj:(part I k).jm=1:=hplan.jmS hpk (by omega)
  obtain ⟨a',ha',hlen⟩:=nativeInstance_nativeChildLength recordId baseI hr base he k hk
  change run.parts[(part I k).jm-1]?=some a' at ha'
  rw [hj,Nat.sub_self,ha] at ha';cases ha'
  change (part I k).clen=(nodeEnc a.output).length at hlen
  have hq:=nativeInstance_bytes_at recordId baseI hr hw (nativeSourceBase recordId run base) he hp
  have hts:I.ts=run.splitCursor [0,15]:=rfl
  refine ⟨a,b,ha,hb,hk2,?_⟩
  change ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp=_
  rw [CompactPhysicalDigests.split_two_child_targets I k hf hplan hwin hpk hci]
  rw [hlen,←hblen,hk2]
  change _ = (if I.ts=1 then
    [digMsg (upsertJobId I.tau 2) (nodeEnc b.output).length ((sha256 (nodeEnc b.output)).map UInt8.toNat),
     digMsg (upsertJobId I.tau 1) (nodeEnc a.output).length ((sha256 (nodeEnc a.output)).map UInt8.toNat)] else
    [digMsg (upsertJobId I.tau 1) (nodeEnc a.output).length ((sha256 (nodeEnc a.output)).map UInt8.toNat),
     digMsg (upsertJobId I.tau 2) (nodeEnc b.output).length ((sha256 (nodeEnc b.output)).map UInt8.toNat)]).map Msg.toFp
  by_cases ht:I.ts=1 <;> simp only [ht,ite_true,ite_false,List.map_cons,List.map_nil]
  all_goals have ht':=(show I.ts=run.splitCursor [0,15] from hts)
  all_goals rw [←hts] at h3 h35
  all_goals simp only [ht,ite_true,ite_false] at h3 h35
  all_goals congr 1
  all_goals first
    | (apply CompactPhysicalDigests.digest_window_slice; rw [←hk2,hq,←List.map_drop,←List.map_take,h3]; simp)
    | (congr 1; apply CompactPhysicalDigests.digest_window_slice; rw [←hk2,hq,←List.map_drop,←List.map_take,h35]; simp)

end ZkFormal.NearV3.Assembly

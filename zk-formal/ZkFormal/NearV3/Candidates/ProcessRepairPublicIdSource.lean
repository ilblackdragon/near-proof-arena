import ZkFormal.NearV3.Candidates.ProcessRepairPublicPacket
import ZkFormal.NearV3.Candidates.ProcessRepairPublicSenderBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairPublicIdSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
/-- Every actual bus70 supplier has the authentic prepared ID at its reported
index. Repeated IDs are retained and no uniqueness assumption is used. -/
theorem sender {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (hdl:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=70) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) :
    ∃tau j,tau<33 ∧ j<sp.ids.length ∧ i.msgVal tr t r pub=
      [Fp.ofNat tau,Fp.ofNat j,Fp.ofNat (ProcPriorIdLimbs.lo (sp.ids.getD j 0)),
        Fp.ofNat (ProcPriorIdLimbs.mid (sp.ids.getD j 0)),Fp.ofNat (ProcPriorIdLimbs.hi (sp.ids.getD j 0))] := by
  have he:t=0:=Classical.byContradiction (fun hn=>ProcPriorRoutedPublicId.other_tables
    (AP:=ProcessRepairBalance.reference AP) rfl t (by simpa [ProcessRepairBalance.reference,←view.length] using ht)
    hn i (by simpa only [view.wires t,ProcessRepairBalance.reference] using hi) hs hb)
  subst t
  rw [view.wires] at hi
  have he:=ProcPriorRoutedPublicId.sender_eq hi hb hs
  subst i
  change (interaction ProcPriorCodecActual.publicId).multNat tr 0 r pub≠0 at hm
  rw [mult] at hm
  have hg:=ProcPriorPublicSenderBound.gate hm
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hstart:=ProcPriorCodecSoundGeometry.public_id_start hL hr hg
  have hS:=(ProcPriorCodecSoundGeometry.start hL hr hstart).1
  have hA:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).2.1
  have hlen:(p.sched.map instOf).length≤33:=by simpa only [List.length_map] using prepD0_len hp
  have hn:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64:=by
    intro P0 hP
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hP
    have h:=prepD0_sched hp s hs
    exact ⟨h.n1,h.n64⟩
  have htau:=(ProcessRepairCodecParameters.active_small view hpub I _ fwd hpar hlen hn hr hA).1
  obtain ⟨hj,hmsg⟩:=ProcessRepairPublicPacket.prepared_packet view hpub I hp sp hsp fwd hdl hpar r hr hg
  refine ⟨cv (codec tr) 0 r Codec.tau,cv (codec tr) 0 r Codec.srcC,htau,hj,?_⟩
  change (interaction ProcPriorCodecActual.publicId).msgVal tr 0 r pub=_
  rw [message]
  exact hmsg
end ZkFormal.NearV3.Candidates.ProcessRepairPublicIdSource

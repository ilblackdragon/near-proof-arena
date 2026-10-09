import ZkFormal.NearV3.Candidates.ProcPriorCodecGridPublic
import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicFlags
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem header_n {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {f:Nat} (hf:f<tr.height 0) (hF:cv (codec tr) 0 f Codec.kF=1) :
    cv (codec tr) 0 f Codec.nn=sp.ids.length := by
  have hlen:(p.sched.map instOf).length<2013265921:=by have :=prepD0_len hp;rw [List.length_map];omega
  obtain ⟨ht,hpacket⟩:=ProcessRepairCodecParameters.first_par view hpub I _ fwd hpar hlen hf hF
  have hn:=ProcPriorCodecSoundParameters.header_n _ _ hpacket
  have hmem:(p.sched.map instOf).getD (cv (codec tr) 0 f Codec.tau) instD∈p.sched.map instOf:=by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht,Option.getD_some]
    exact List.getElem_mem ht
  obtain ⟨sp',hs',he⟩:=List.mem_map.mp hmem
  rw [←he] at hn
  obtain ⟨ids,hids⟩:=prepD0_ids hp
  have hid:sp'.ids=sp.ids:=(hids sp' hs').trans (hids sp hsp).symm
  change cv (codec tr) 0 f Codec.nn=sp'.ids.length%P at hn
  have hb:sp.ids.length≤64:=(prepD0_sched hp sp hsp).n64
  simpa only [hid,Nat.mod_eq_of_lt (show sp.ids.length<P by rw [P_val];omega)] using hn

/-- All prepared layout IDs have actual Codec senders in each actual Codec instance. -/
theorem sender {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (hdl:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {f j:Nat} (hf:f<tr.height 0) (hF:cv (codec tr) 0 f Codec.kF=1) (hj:j<sp.ids.length) :
    ∃r,r<tr.height 0 ∧ (interaction ProcPriorCodecActual.publicId).multNat tr 0 r pub=1 ∧
      (interaction ProcPriorCodecActual.publicId).msgVal tr 0 r pub=
      [Fp.ofNat (cv (codec tr) 0 f Codec.tau),Fp.ofNat j,
       Fp.ofNat (ProcPriorIdLimbs.lo (sp.ids.getD j 0)),
       Fp.ofNat (ProcPriorIdLimbs.mid (sp.ids.getD j 0)),
       Fp.ofNat (ProcPriorIdLimbs.hi (sp.ids.getD j 0))] := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hn:=header_n view hpub I hp sp hsp fwd hpar hf hF
  have hs:=prepD0_sched hp sp hsp
  have hb:=hs.n64
  have hp1:=hs.n1
  have K:=ProcPriorCodecSoundGeometry.kinds hL hf
  have ha:cv (codec tr) 0 f Codec.act=1:=by omega
  have hsq:=ProcPriorCodecSoundRecordBound.active_square hL hf ha (by omega)
  rw [hn] at hsq
  obtain ⟨r,hr,hrs,hrz,hsj,htau,hm⟩:=ProcPriorCodecGridPublic.sender hL hf hF hn (by omega) hs.n64 hsq hj
  have hg:=ProcPriorPublicSenderBound.gate (show ProcPriorCodecActual.publicId.multNat (codec tr) 0 r pub≠0 by omega)
  obtain ⟨_,hpkt⟩:=ProcessRepairPublicPacket.prepared_packet view hpub I hp sp hsp fwd hdl hpar r hr hg
  refine ⟨r,hr,?_,?_⟩
  · rw [mult];exact hm
  · rw [message]
    change ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval (codec tr) 0 r pub)=_
    simpa only [hsj,htau] using hpkt
end ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend

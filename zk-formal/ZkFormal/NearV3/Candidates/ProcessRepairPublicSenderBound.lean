import ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
import ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
import ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairPublicSenderBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection ProcPriorPublicSenderBound
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem public64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64) :
    ProcPriorIdSoundBound.PublicSendBound AP tr pub 64 := by
  intro ts hts r hr i hi hb hs hm
  have he:ts=0:=Classical.byContradiction (fun hn=>ProcPriorRoutedPublicId.other_tables (AP:=ProcessRepairBalance.reference AP) rfl ts (by simpa [ProcessRepairBalance.reference,←view.length] using hts) hn i (by simpa only [view.wires ts,ProcessRepairBalance.reference] using hi) hs hb)
  subst ts
  rw [view.wires] at hi
  have he:=ProcPriorRoutedPublicId.sender_eq hi hb hs
  subst i
  change (interaction ProcPriorCodecActual.publicId).multNat tr 0 r pub≠0 at hm
  rw [mult] at hm
  have hg:=gate hm
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hn:∀q,q<(codec tr).height 0→cv (codec tr) 0 q Codec.act=1→
      1≤cv (codec tr) 0 q Codec.nn ∧ cv (codec tr) 0 q Codec.nn≤64:=by
    intro q hq ha
    have h:=ProcessRepairCodecParameters.active_small view hpub I Ps fwd hrec hlen hns hq ha
    exact ⟨h.2.2.1,h.2.2.2.1⟩
  have hh:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
  have hbnd:=ProcPriorCodecPublicBound.ordinal_bound hL hh hn hr hg
  have hstart:=ProcPriorCodecSoundGeometry.public_id_start hL hr hg
  have hS:=(ProcPriorCodecSoundGeometry.start hL hr hstart).1
  have hA:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).2.1
  have h64:=(hn r hr hA).2
  change (((interaction ProcPriorCodecActual.publicId).msgVal tr 0 r pub)[1]!).toNat<64
  rw [message]
  have he:(ProcPriorCodecActual.publicId.msgVal (codec tr) 0 r pub)[1]! = Fp.ofNat (cv (codec tr) 0 r Codec.srcC):=by
    simp [ProcPriorCodecActual.publicId,Interaction.msgVal,Codec.ev_c]
  rw [he,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show cv (codec tr) 0 r Codec.srcC<P from cv_lt _ _)]
  omega

/-- Selected-family found-result bound without an assumed public-ID sender
contract. Public SPAR ownership/inventory remains the public input binding. -/
theorem prepared_public64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true) (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par) :
    ProcPriorIdSoundBound.PublicSendBound AP tr pub 64 := by
  apply public64 view hpub I (p.sched.map instOf) fwd hrec
  · simpa only [List.length_map] using prepD0_len hp
  · intro P0 hP
    obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hP
    have hs:=prepD0_sched hp sp hsp
    exact ⟨hs.n1,hs.n64⟩

end ZkFormal.NearV3.Candidates.ProcessRepairPublicSenderBound

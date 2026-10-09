import ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
import ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecByteTag
namespace ZkFormal.NearV3.Candidates.ProcessRepairCodecByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
open ProcPriorRoutedCodecByteTag (active sender_eq)
set_option maxRecDepth 32768
theorem tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0) {i:Interaction}
    (hi:i∈ProcPriorCodecActual.interactions) (hb:i.bus=ZkFormal.Near.B_BYTES) (hs:i.send=true)
    (hm:(interaction i).multNat tr 0 r pub≠0) :
    ((interaction i).msgVal tr 0 r pub)[0]!.toNat%16=11 ∨
      ((interaction i).msgVal tr 0 r pub)[0]!.toNat%16=12 := by
  rw [mult] at hm
  have ha:=active (ProcessRepairCodecParameters.local_codec v) hr hi hb hs hm
  have ht:cv (codec tr) 0 r Codec.tau<33:=
    (ProcessRepairCodecParameters.active_small v hpub I Ps fwd hrec hlen hns hr ha).1
  rw [message]
  have hc:(codec tr).cell 0 r Codec.tau=Fp.ofNat (cv (codec tr) 0 r Codec.tau):=(Fp.ofNat_toNat _).symm
  rcases sender_eq hi hb hs with rfl|rfl
  · right
    change (Fp.ofNat 12+Fp.ofNat 16*(Fp.ofNat 512*(codec tr).cell 0 r Codec.tau)).toNat%16=12
    rw [hc,ZkFormal.Near.ofNat_mul',ZkFormal.Near.ofNat_mul',ZkFormal.Near.ofNat_add',Fp.toNat_ofNat]
    have hsmall:12+16*(512*cv (codec tr) 0 r Codec.tau)<P:=by rw [P_val];omega
    rw [Nat.mod_eq_of_lt hsmall]
    omega
  · left
    change (Fp.ofNat 11+Fp.ofNat 16*(codec tr).cell 0 r Codec.tau).toNat%16=11
    rw [hc,ZkFormal.Near.ofNat_mul',ZkFormal.Near.ofNat_add',Fp.toNat_ofNat]
    have hsmall:11+16*cv (codec tr) 0 r Codec.tau<P:=by rw [P_val];omega
    rw [Nat.mod_eq_of_lt hsmall]
    omega
theorem prepared {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {r:Nat} (hr:r<tr.height 0) {i:Interaction}
    (hi:i∈ProcPriorCodecActual.interactions) (hb:i.bus=ZkFormal.Near.B_BYTES) (hs:i.send=true)
    (hm:(interaction i).multNat tr 0 r pub≠0) :
    ((interaction i).msgVal tr 0 r pub)[0]!.toNat%16≠7 ∧
      ((interaction i).msgVal tr 0 r pub)[0]!.toNat%16≠8 ∧
      ((interaction i).msgVal tr 0 r pub)[0]!.toNat%16≠9 := by
  have hl:(p.sched.map instOf).length≤33:=by rw [List.length_map];exact prepD0_len hprep
  have hn:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64:=by
    intro P0 hm
    obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hm
    have h:=prepD0_sched hprep sp hsp
    exact ⟨h.n1,h.n64⟩
  have h:=tag v hpub I _ fwd hrec hl hn hr hi hb hs hm
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairCodecByteTag

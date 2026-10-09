import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryBounds
import ZkFormal.NearV3.Candidates.ProcPriorRoutedPreparedQuery
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
set_option maxRecDepth 32768

theorem sender_eq {i:Interaction} (hi:i∈ProcPriorCodecActual.interactions)
    (hb:i.bus=ZkFormal.Near.B_BYTES) (hs:i.send=true) :
    i=ProcPriorCodecActual.interactions[1]! ∨ i=ProcPriorCodecActual.interactions[2]! := by
  have hf:i∈ProcPriorCodecActual.interactions.filter (fun j=>j.bus==ZkFormal.Near.B_BYTES && j.send):=
    List.mem_filter.mpr ⟨hi,by simp [hb,hs]⟩
  have he:ProcPriorCodecActual.interactions.filter (fun j=>j.bus==ZkFormal.Near.B_BYTES && j.send)=
    [ProcPriorCodecActual.interactions[1]!,ProcPriorCodecActual.interactions[2]!] := rfl
  rw [he] at hf
  simpa only [List.mem_cons,List.mem_nil_iff,or_false] using hf

theorem active {tr:Trace Fp} {pub:List Fp} {r:Nat}
    (hL:ProcPriorCodecSoundRows.CLocal tr 0 pub) (hr:r<tr.height 0)
    {i:Interaction} (hi:i∈ProcPriorCodecActual.interactions)
    (hb:i.bus=ZkFormal.Near.B_BYTES) (hs:i.send=true) (hm:i.multNat tr 0 r pub≠0) :
    cv tr 0 r Codec.act=1 := by
  have hk:=ProcPriorCodecSoundGeometry.kinds hL hr
  by_cases ha:cv tr 0 r Codec.act=0
  · have hH:tr.cell 0 r Codec.kH=0:=by
      have hz:cv tr 0 r Codec.kH=0:=by omega
      have h:=Fp.ofNat_toNat (tr.cell 0 r Codec.kH)
      rw [show (tr.cell 0 r Codec.kH).toNat=0 from hz] at h
      exact h.symm
    have hR:tr.cell 0 r Codec.kR=0:=by
      have hz:cv tr 0 r Codec.kR=0:=by omega
      have h:=Fp.ofNat_toNat (tr.cell 0 r Codec.kR)
      rw [show (tr.cell 0 r Codec.kR).toNat=0 from hz] at h
      exact h.symm
    have hZ:tr.cell 0 r Codec.kZ=0:=by
      have hz:cv tr 0 r Codec.kZ=0:=by omega
      have h:=Fp.ofNat_toNat (tr.cell 0 r Codec.kZ)
      rw [show (tr.cell 0 r Codec.kZ).toNat=0 from hz] at h
      exact h.symm
    have hA:tr.cell 0 r Codec.kA=0:=by
      have hz:cv tr 0 r Codec.kA=0:=by omega
      have h:=Fp.ofNat_toNat (tr.cell 0 r Codec.kA)
      rw [show (tr.cell 0 r Codec.kA).toNat=0 from hz] at h
      exact h.symm
    rcases sender_eq hi hb hs with rfl|rfl
    · change (if tr.cell 0 r Codec.kH+(tr.cell 0 r Codec.kR+tr.cell 0 r Codec.kZ)=1 then 1 else 0)+0≠0 at hm
      rw [hH,hR,hZ] at hm
      have hz:(0:Fp)+(0+0)≠1:=by decide +kernel
      simp [hz] at hm
    · change (if tr.cell 0 r Codec.kZ+tr.cell 0 r Codec.kA=1 then 1 else 0)+0≠0 at hm
      rw [hZ,hA] at hm
      have hz:(0:Fp)+0≠1:=by decide +kernel
      simp [hz] at hm
  · omega

theorem tag {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
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
  have ha:=active (ProcPriorRoutedCodecParameters.local_codec hH htables) hr hi hb hs hm
  have ht:cv (codec tr) 0 r Codec.tau<33:=
    (ProcPriorRoutedCodecParameters.active_small hH htables hpub I Ps fwd hrec hlen hns hr ha).1
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
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
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
  have h:=tag hH htables hpub I _ fwd hrec hl hn hr hi hb hs hm
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecByteTag

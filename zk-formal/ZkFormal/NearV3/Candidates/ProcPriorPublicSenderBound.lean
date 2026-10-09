import ZkFormal.NearV3.Candidates.ProcPriorRoutedPublicId
import ZkFormal.NearV3.Candidates.ProcPriorRoutedIdBound
namespace ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection

theorem gate {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hm:ProcPriorCodecActual.publicId.multNat tr t r pub≠0) :
    (.mul (c Codec.rs) (c Codec.nzb) : Expr).eval tr t r pub=1 := by
  by_cases h:(.mul (c Codec.rs) (c Codec.nzb) : Expr).eval tr t r pub=1
  · exact h
  · simp only [ProcPriorCodecActual.publicId,Interaction.multNat,Interaction.multNat.go,h,
      ite_false,Nat.zero_add] at hm
    exact (hm rfl).elim

/-- The actual fused Codec is the only public70 supplier. Its ordinal is
bounded by the real corrected record grid and public SPAR parameters. -/
theorem public64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64) :
    ProcPriorIdSoundBound.PublicSendBound AP tr pub 64 := by
  intro ts hts r hr i hi hb hs hm
  have he:ts=0:=Classical.byContradiction (fun hn=>ProcPriorRoutedPublicId.other_tables htables ts hts hn i hi hs hb)
  subst ts
  rw [htables] at hi
  have he:=ProcPriorRoutedPublicId.sender_eq hi hb hs
  subst i
  change (interaction ProcPriorCodecActual.publicId).multNat tr 0 r pub≠0 at hm
  rw [mult] at hm
  have hg:=gate hm
  have hL:=ProcPriorRoutedCodecParameters.local_codec hH htables
  have hn:∀q,q<(codec tr).height 0→cv (codec tr) 0 q Codec.act=1→
      1≤cv (codec tr) 0 q Codec.nn ∧ cv (codec tr) 0 q Codec.nn≤64:=by
    intro q hq ha
    have h:=ProcPriorRoutedCodecParameters.active_small hH htables hpub I Ps fwd hrec hlen hns hq ha
    exact ⟨h.2.2.1,h.2.2.2.1⟩
  have ht0:0<AP.tables.length:=by rw [htables];decide +kernel
  have hh:tr.height 0≤2^22:=height_le hH ht0
    (show AP.tables[0]! = ProcPriorComparatorRoutedFamily.tables[0]! by rw [htables]) (by rfl)
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
theorem result64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    (hpub70:∀msg,pubCount AP pub 70 true msg=0) (hpub72:∀msg,pubCount AP pub 72 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=72) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) (hf:(i.msgVal tr tc r pub)[2]! = Fp.ofNat 1) :
    ((i.msgVal tr tc r pub)[3]!).toNat<64 :=
  ProcPriorRoutedIdBound.result_bound hH htables 64 hpub70
    (public64 hH htables hpub I Ps fwd hrec hlen hns) hpub72 ht hr hi hb hs hm hf
theorem prepared_public64 {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true) (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par) :
    ProcPriorIdSoundBound.PublicSendBound AP tr pub 64 := by
  apply public64 hH htables hpub I (p.sched.map instOf) fwd hrec
  · simpa only [List.length_map] using prepD0_len hp
  · intro P0 hP
    obtain ⟨sp,hsp,rfl⟩:=List.mem_map.mp hP
    have hs:=prepD0_sched hp sp hsp
    exact ⟨hs.n1,hs.n64⟩

end ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound

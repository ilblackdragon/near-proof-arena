import ZkFormal.NearV3.Candidates.ProcessRepairSdlIndex
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundPacket
namespace ZkFormal.NearV3.Candidates.ProcessRepairPublicPacket
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundPacket
open ProcPriorRoutedCodecProjection (codec)
theorem live_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height 0) (hncell:cv (codec tr) 0 r nn=ids.length)
    (hm:(Expr.mul (c rs) (c nzb)).eval (codec tr) 0 r pub=1) :
    cv (codec tr) 0 r srcC<ids.length ∧ cv (codec tr) 0 r kidx/ids.length=cv (codec tr) 0 r srcC := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  have hS:=(ProcPriorCodecSoundGeometry.start hL hr hs).1
  have hk:=ProcessRepairSdlIndex.sender_index_bound view I ids hn hrec r hr hS
  have hh:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
  have hi:=(ProcPriorCodecSoundIndex.live_index hL hr hh (by omega) hm).2
  rw [hncell] at hi
  have hp:0<ids.length := by
    by_cases hz:ids.length=0
    · rw [hz] at hk;omega
    · omega
  have hb:cv (codec tr) 0 r srcC<ids.length := Nat.lt_of_mul_lt_mul_right (by rwa [←hi])
  refine ⟨hb,?_⟩
  rw [hi,Nat.mul_div_cancel _ hp]

theorem packet {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hids:∀id∈ids,id<2^64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height 0) (hncell:cv (codec tr) 0 r nn=ids.length)
    (hm:(Expr.mul (c rs) (c nzb)).eval (codec tr) 0 r pub=1) :
    cv (codec tr) 0 r srcC<ids.length ∧
    ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval (codec tr) 0 r pub)=
      [Fp.ofNat (cv (codec tr) 0 r tau),Fp.ofNat (cv (codec tr) 0 r srcC),
       Fp.ofNat (ProcPriorIdLimbs.lo (ids.getD (cv (codec tr) 0 r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.mid (ids.getD (cv (codec tr) 0 r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.hi (ids.getD (cv (codec tr) 0 r srcC) 0))] := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  obtain ⟨hsbound,hdiv⟩:=live_source view I ids hn hrec r hr hncell hm
  obtain ⟨_,hpost⟩:=ProcessRepairSdlIds.start_bytes view I ids hn hrec r hr hs
  have hreg:=(ProcPriorCodecSoundGeometry.start_bytes hL hr hs).2.1
  have hid:ids.getD (cv (codec tr) 0 r srcC) 0<2^64 := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hsbound,Option.getD_some]
    exact hids _ (List.getElem_mem hsbound)
  have hb:∀i,i<8→cv (codec tr) 0 r (prbit i)=(ids.getD (cv (codec tr) 0 r srcC) 0)/256^i%256 := by
    intro i hi
    rw [(hreg i hi).1,hpost i hi]
    simp only [idByte,if_pos hi,hdiv,Nat.mod_eq_of_lt hi]
  obtain ⟨hl,hmd,hh⟩:=packed_of_bytes (pub:=pub) _ hid hb
  refine ⟨hsbound,?_⟩
  simp only [ProcPriorCodecActual.publicId,List.map_cons,List.map_nil,ev_c,hl,hmd,hh]

/-- A live publicID packet is the actual prepared layout's sender index and
canonical 24/24/16-bit ID limbs. SPAR authenticates the shard count, SDL
 authenticates bytes, and physical height justifies natural index arithmetic. -/
theorem prepared_packet {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd : List (Nat×Nat))
    (hrec:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    (r : Nat) (hr:r<tr.height 0)
    (hm:(Expr.mul (c rs) (c nzb)).eval (codec tr) 0 r pub=1) :
    cv (codec tr) 0 r srcC<sp.ids.length ∧
    ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval (codec tr) 0 r pub)=
      [Fp.ofNat (cv (codec tr) 0 r tau),Fp.ofNat (cv (codec tr) 0 r srcC),
       Fp.ofNat (ProcPriorIdLimbs.lo (sp.ids.getD (cv (codec tr) 0 r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.mid (sp.ids.getD (cv (codec tr) 0 r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.hi (sp.ids.getD (cv (codec tr) 0 r srcC) 0))] := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  have hS:=(ProcPriorCodecSoundGeometry.start hL hr hs).1
  have ha:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).2.1
  have hn:sp.ids.length≤64 := (prepD0_sched hprep sp hsp).n64
  obtain ⟨ids,hids⟩:=prepD0_ids hprep
  have hp:I.recs B_SDL true=dlRecs 0 sp.ids := by
    rw [hrec,render_dlSend]
    cases he:p.sched with
    | nil=>simp [he] at hsp
    | cons a as=>
      have hid:a.ids=sp.ids := (hids a (by simp [he])).trans (hids sp hsp).symm
      simp only [he,List.map_cons,List.getD_cons_zero,instOf,hid]
  have hlen:(p.sched.map instOf).length<2013265921 := by
    have hl:=prepD0_len hprep
    rw [List.length_map];omega
  obtain ⟨f,hfr,hF,hconst⟩:=ProcPriorCodecSoundOrigin.instance_origin hL r hr ha
  obtain ⟨htau,hpacket⟩:=ProcessRepairCodecParameters.first_par view hpub I
    (p.sched.map instOf) fwd hpar hlen (by omega) hF
  have hncell:=ProcPriorCodecSoundParameters.header_n _ _ hpacket
  have hct:=hconst tau (by simp)
  have hcn:=hconst nn (by simp)
  rw [hct] at htau
  rw [hct,hcn] at hncell
  have hmem:(p.sched.map instOf).getD (cv (codec tr) 0 r tau) instD∈p.sched.map instOf := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem htau,Option.getD_some]
    exact List.getElem_mem htau
  obtain ⟨sp',hsp',he⟩:=List.mem_map.mp hmem
  rw [←he] at hncell
  have hid:sp'.ids=sp.ids := (hids sp' hsp').trans (hids sp hsp).symm
  change cv (codec tr) 0 r nn=sp'.ids.length%P at hncell
  rw [hid,Nat.mod_eq_of_lt (by simp only [P];omega)] at hncell
  exact packet view I sp.ids hn (prepD0_ids64 hprep sp hsp) hp r hr hncell hm
end ZkFormal.NearV3.Candidates.ProcessRepairPublicPacket

import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndexSdl
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundPacket
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

theorem live_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hncell:cv tr tc r nn=ids.length)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr tc r pub=1) :
    cv tr tc r srcC<ids.length ∧ cv tr tc r kidx/ids.length=cv tr tc r srcC := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  have hS:=(ProcPriorCodecSoundGeometry.start hL hr hs).1
  have hk:=ProcPriorCodecSoundIndexSdl.sender_index_bound hH tc ht htab own I ids hn hrec r hr hS
  have hh:=height_le hH ht htab (by rfl : ProcPriorCodecActual.table.maxLog=22)
  have hi:=(ProcPriorCodecSoundIndex.live_index hL hr hh (by omega) hm).2
  rw [hncell] at hi
  have hp:0<ids.length := by
    by_cases hz:ids.length=0
    · rw [hz] at hk;omega
    · omega
  have hb:cv tr tc r srcC<ids.length := Nat.lt_of_mul_lt_mul_right (by rwa [←hi])
  refine ⟨hb,?_⟩
  rw [hi,Nat.mul_div_cancel _ hp]

theorem packed_of_bytes {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (id : Nat) (hid:id<2^64)
    (hb:∀i,i<8→cv tr t r (prbit i)=id/256^i%256) :
    ProcPriorCodecActual.idLo.eval tr t r pub=Fp.ofNat (ProcPriorIdLimbs.lo id) ∧
    ProcPriorCodecActual.idMid.eval tr t r pub=Fp.ofNat (ProcPriorIdLimbs.mid id) ∧
    ProcPriorCodecActual.idHi.eval tr t r pub=Fp.ofNat (ProcPriorIdLimbs.hi id) := by
  obtain ⟨hl,hm,hh⟩:=ProcPriorCodecSoundPublicId.packed_eval tr t r pub
  rw [hb 0 (by decide),hb 1 (by decide),hb 2 (by decide)] at hl
  rw [hb 3 (by decide),hb 4 (by decide),hb 5 (by decide)] at hm
  rw [hb 6 (by decide),hb 7 (by decide)] at hh
  refine ⟨hl.trans ?_,hm.trans ?_,hh.trans ?_⟩
  all_goals congr 1
  all_goals simp only [ProcPriorIdLimbs.lo,ProcPriorIdLimbs.mid,ProcPriorIdLimbs.hi]
  all_goals omega

theorem packet {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hids:∀id∈ids,id<2^64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hncell:cv tr tc r nn=ids.length)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr tc r pub=1) :
    cv tr tc r srcC<ids.length ∧
    ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval tr tc r pub)=
      [Fp.ofNat (cv tr tc r tau),Fp.ofNat (cv tr tc r srcC),
       Fp.ofNat (ProcPriorIdLimbs.lo (ids.getD (cv tr tc r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.mid (ids.getD (cv tr tc r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.hi (ids.getD (cv tr tc r srcC) 0))] := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  obtain ⟨hsbound,hdiv⟩:=live_source hH tc ht htab own I ids hn hrec r hr hncell hm
  obtain ⟨_,hpost⟩:=ProcPriorCodecSoundSdlIds.start_bytes hH tc ht htab own I ids hn hrec r hr hs
  have hreg:=(ProcPriorCodecSoundGeometry.start_bytes hL hr hs).2.1
  have hid:ids.getD (cv tr tc r srcC) 0<2^64 := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hsbound,Option.getD_some]
    exact hids _ (List.getElem_mem hsbound)
  have hb:∀i,i<8→cv tr tc r (prbit i)=(ids.getD (cv tr tc r srcC) 0)/256^i%256 := by
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
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc) (SO:SparOwn AP)
    (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd : List (Nat×Nat))
    (hrec:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    (r : Nat) (hr:r<tr.height tc)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr tc r pub=1) :
    cv tr tc r srcC<sp.ids.length ∧
    ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval tr tc r pub)=
      [Fp.ofNat (cv tr tc r tau),Fp.ofNat (cv tr tc r srcC),
       Fp.ofNat (ProcPriorIdLimbs.lo (sp.ids.getD (cv tr tc r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.mid (sp.ids.getD (cv tr tc r srcC) 0)),
       Fp.ofNat (ProcPriorIdLimbs.hi (sp.ids.getD (cv tr tc r srcC) 0))] := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
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
  obtain ⟨htau,hncell⟩:=ProcPriorCodecSoundParameters.active_parameters hH ht htab SO I
    (p.sched.map instOf) fwd hpar hlen hr ha
  have hmem:(p.sched.map instOf).getD (cv tr tc r tau) instD∈p.sched.map instOf := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem htau,Option.getD_some]
    exact List.getElem_mem htau
  obtain ⟨sp',hsp',he⟩:=List.mem_map.mp hmem
  rw [←he] at hncell
  have hid:sp'.ids=sp.ids := (hids sp' hsp').trans (hids sp hsp).symm
  change cv tr tc r nn=sp'.ids.length%P at hncell
  rw [hid,Nat.mod_eq_of_lt (by simp only [P];omega)] at hncell
  exact packet hH tc ht htab own I sp.ids hn (prepD0_ids64 hprep sp hsp) hp r hr hncell hm
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundPacket

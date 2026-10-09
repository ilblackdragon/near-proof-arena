import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlFinite
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlIds
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

theorem record_index {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hR:cv tr t r kR=1) : (cv tr t r klo+256*cv tr t r khi)%2013265921=cv tr t r kidx := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorCodecSoundGeometry.rec_member
    (.mul (c kR) (sub (c kidx) (.add (c klo) (smul 256 (c khi))))) (by simp [cRec]) (by decide +kernel))
  zs hq [hR]
  have := Codec.lt (tr:=tr) (t:=t) r kidx
  omega

theorem sender_index_next {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hS:cv tr t r fS=1) (hg:cv tr t r g<7) : cv tr t (r+1) kidx=cv tr t r kidx := by
  obtain ⟨hR,hA,_⟩:=ProcPriorCodecSoundGeometry.sender_kind hL hr hS
  have h7:=ProcPriorCodecSoundGeometry.e7_zero hL hr hR hg
  have hr1:=ProcPriorCodecSoundGeometry.act_next hL hr hA
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorCodecSoundGeometry.rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  zs hq [hR,h7,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) r kidx
  have := Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  omega

theorem sender_index {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r rs=1) : ∀i,i<8→cv tr t (r+i) kidx=cv tr t r kidx := by
  intro i
  induction i with
  | zero=>intro _;simp
  | succ i ih=>
    intro hi
    obtain ⟨hri,hS,hg,_,_⟩:=ProcPriorCodecSoundGeometry.sender_walk hL hr hs i (by omega)
    rw [show r+(i+1)=r+i+1 by omega,sender_index_next hL hri hS (by omega)]
    exact ih (by omega)

/-- Public SDL records, not downstream bus70 lookup rows, authenticate current
layout ID bytes. Global balance/ownership plus finite physical height supply
the public origin, with no supplied payload equality or timestamp bound. -/
theorem sender_byte {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hS:cv tr tc r fS=1) (hg:cv tr tc r g<8) :
    cv tr tc r bpost=idByte ids (cv tr tc r kidx) (cv tr tc r g) := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hrow:=ProcPriorCodecSoundSdlRows.sender_row hL hr hS
  obtain ⟨seed,hseed,hpublic⟩:=ProcPriorCodecSoundSdlFinite.public_origin hH tc ht htab own r hr
    (by rw [hrow.1];decide)
  rw [I.count,hrec] at hpublic
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hpublic)
  have hR:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).1
  have hk:=record_index hL hr hR
  have ho:oE.eval tr tc r pub=Fp.ofNat (cv tr tc r g) := by
    have he:=hrow.2.2.1
    rw [(ProcPriorCodecSoundSdlDescent.messages tr tc r pub).1] at he
    have hh:=congrArg (fun xs:List Fp=>xs[3]!) he
    simpa only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,
      List.getElem!_cons_succ,List.getElem!_cons_zero] using hh
  exact (dl_pub hn hmem hseed (cv_lt r klo) (cv_lt r khi) (by omega) (cv_lt r bpost) hk
    (by simp only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,ho])).2

theorem start_bytes {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hs:cv tr tc r rs=1) :
    r+7<tr.height tc ∧ ∀i,i<8→cv tr tc (r+i) bpost=idByte ids (cv tr tc r kidx) i := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hw:=ProcPriorCodecSoundGeometry.sender_walk hL hr hs
  refine ⟨(hw 7 (by decide)).1,?_⟩
  intro i hi
  obtain ⟨hri,hS,hg,_,_⟩:=hw i hi
  have he:=sender_byte hH tc ht htab own I ids hn hrec (r+i) hri hS (by omega)
  rwa [hg,sender_index hL hr hs i hi] at he
/-- Prepared public SDL seed records authenticate the sender bytes of every
corrected record start to the actual current layout. One-layout preparation
allows any actual prepared scheduler instance to name that layout. -/
theorem prepared_start_bytes {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd : List (Nat×Nat))
    (hrec:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (r : Nat) (hr:r<tr.height tc) (hs:cv tr tc r rs=1) :
    r+7<tr.height tc ∧ ∀i,i<8→cv tr tc (r+i) bpost=idByte sp.ids (cv tr tc r kidx) i := by
  have hn:sp.ids.length≤64 := (prepD0_sched hprep sp hsp).n64
  have hp:I.recs B_SDL true=dlRecs 0 sp.ids := by
    rw [hrec,render_dlSend]
    obtain ⟨ids,hids⟩:=prepD0_ids hprep
    cases he:p.sched with
    | nil=>simp [he] at hsp
    | cons a as=>
      have ha:a∈p.sched := by simp [he]
      have hid:a.ids=sp.ids := (hids a ha).trans (hids sp hsp).symm
      simp only [he,List.map_cons,List.getD_cons_zero,instOf,hid]
  exact start_bytes hH tc ht htab own I sp.ids hn hp r hr hs
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlIds

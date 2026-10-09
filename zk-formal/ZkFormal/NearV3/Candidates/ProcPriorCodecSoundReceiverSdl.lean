import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundReceiver
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundReceiverSdl
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
theorem receiver_row {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hR:cv tr t r fR=1) :
    (ProcPriorCodecActual.interactions[7]!).multNat tr t r pub=1 ∧
    (ProcPriorCodecActual.interactions[8]!).multNat tr t r pub=1 ∧
    (ProcPriorCodecActual.interactions[7]!).msgVal tr t r pub=
      [cv tr t r tau,cv tr t r klo,cv tr t r khi,8+cv tr t r g,cv tr t r bpost].map Fp.ofNat ∧
    (ProcPriorCodecActual.interactions[8]!).msgVal tr t r pub=
      [cv tr t r tau+1,cv tr t r klo,cv tr t r khi,8+cv tr t r g,cv tr t r bpost].map Fp.ofNat := by
  have hk:=ProcPriorCodecSoundGeometry.kinds hL hr
  have hS:cv tr t r fS=0 := by omega
  have ho:oE.eval tr t r pub=Fp.ofNat (8+cv tr t r g) := ev_of (by
    simp only [oE,zev_add,zev_smul,zev_c,cur_cv,hS,hR]
    omega)
  rw [ProcPriorCodecSoundSdlRows.receive_same,ProcPriorCodecSoundSdlRows.send_same,i7_def,i8_def]
  refine ⟨?_,?_,?_,?_⟩
  · apply mult_of (e:=.add (c fS) (c fR)) rfl
    simp only [zev_add,zev_c,cur_cv,hS,hR]
    rfl
  · apply mult_of (e:=.add (c fS) (c fR)) rfl
    simp only [zev_add,zev_c,cur_cv,hS,hR]
    rfl
  · simp only [Interaction.msgVal,List.map_cons,List.map_nil,ev_c,ho]
  · have ht:(Expr.add (c tau) (k 1)).eval tr t r pub=Fp.ofNat (cv tr t r tau+1) := ev_of (by
      simp only [zev_add,zev_c,zev_k,cur_cv]
      omega)
    simp only [Interaction.msgVal,List.map_cons,List.map_nil,ev_c,ho,ht]

theorem receiver_byte {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hRr:cv tr tc r fR=1) (hg:cv tr tc r g<8) :
    cv tr tc r bpost=idByte ids (cv tr tc r kidx) (8+cv tr tc r g) := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hrow:=receiver_row hL hr hRr
  obtain ⟨seed,hseed,hpublic⟩:=ProcPriorCodecSoundSdlFinite.public_origin hH tc ht htab own r hr
    (by rw [hrow.1];decide)
  rw [I.count,hrec] at hpublic
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hpublic)
  have hR:=(ProcPriorCodecSoundReceiver.receiver_kind hL hr hRr).1
  have hk:=ProcPriorCodecSoundSdlIds.record_index hL hr hR
  have ho:oE.eval tr tc r pub=Fp.ofNat (8+cv tr tc r g) := by
    have he:=hrow.2.2.1
    rw [(ProcPriorCodecSoundSdlDescent.messages tr tc r pub).1] at he
    have hh:=congrArg (fun xs:List Fp=>xs[3]!) he
    simpa only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,
      List.getElem!_cons_succ,List.getElem!_cons_zero] using hh
  exact (dl_pub hn hmem hseed (cv_lt r klo) (cv_lt r khi) (by omega) (cv_lt r bpost) hk
    (by simp only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,ho])).2


/-- All receiver bytes follow from a single actual record start and genuine
public SDL ownership. No independent receiver-row shape is assumed. -/
theorem start_bytes {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hs:cv tr tc r rs=1) :
    r+15<tr.height tc ∧ ∀i,i<8→
      cv tr tc (r+8+i) bpost=idByte ids (cv tr tc r kidx) (8+i) := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hw:=ProcPriorCodecSoundReceiver.receiver_walk hL hr hs
  refine ⟨by simpa only [show r+8+7=r+15 by omega] using (hw 7 (by decide)).1,?_⟩
  intro i hi
  obtain ⟨hri,hR,hg,hk,_⟩:=hw i hi
  have he:=receiver_byte hH tc ht htab own I ids hn hrec (r+8+i) hri hR (by omega)
  rwa [hg,hk] at he

theorem prepared_receiver_bytes {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd : List (Nat×Nat))
    (hrec:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (r : Nat) (hr:r<tr.height tc) (hs:cv tr tc r rs=1) :
    r+15<tr.height tc ∧ ∀i,i<8→cv tr tc (r+8+i) bpost=idByte sp.ids (cv tr tc r kidx) (8+i) := by
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

/-- The authenticated second field is precisely the little-endian receiver ID
selected by the actual record index, even when layout IDs repeat. -/
theorem prepared_receiver_id {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p)
    (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd : List (Nat×Nat))
    (hrec:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (r : Nat) (hr:r<tr.height tc) (hs:cv tr tc r rs=1) :
    r+15<tr.height tc ∧ ∀i,i<8→cv tr tc (r+8+i) bpost=
      sp.ids.getD (cv tr tc r kidx % sp.ids.length) 0 / 256^i % 256 := by
  obtain ⟨hend,hbytes⟩:=prepared_receiver_bytes hH tc ht htab own I hprep sp hsp fwd hrec r hr hs
  refine ⟨hend,?_⟩
  intro i hi
  rw [hbytes i hi]
  simp only [idByte,show ¬8+i<8 by omega,if_false,show (8+i)%8=i by omega]
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundReceiverSdl

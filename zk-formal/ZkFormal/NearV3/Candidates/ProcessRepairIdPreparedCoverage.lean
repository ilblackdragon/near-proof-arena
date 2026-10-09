import ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedSend
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedCoverage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection ProcPriorRoutedIdBound
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem coverage {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h70:∀seg∈AP.pubSegs,seg.bus≠70)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (hdl:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {f j:Nat} (hf:f<tr.height 0) (hF:cv (codec tr) 0 f Codec.kF=1) (hj:j<sp.ids.length) :
    let pt:=ProcPriorRoutedRawSource.raw tr
    ∃q,q<tr.height 0 ∧ cv pt 0 q (ProcPriorVertical4Linear.stage 1)=1 ∧
      cv pt 0 q ProcPriorIdTable.act=1 ∧ cv pt 0 q ProcPriorIdTable.isPublic=1 ∧
      cv pt 0 q ProcPriorIdTable.tau=cv (codec tr) 0 f Codec.tau ∧
      cv pt 0 q ProcPriorIdTable.ordinal=j ∧
      cv pt 0 q ProcPriorIdTable.keyLo=ProcPriorIdLimbs.lo (sp.ids.getD j 0) ∧
      cv pt 0 q ProcPriorIdTable.keyMid=ProcPriorIdLimbs.mid (sp.ids.getD j 0) ∧
      cv pt 0 q ProcPriorIdTable.keyHi=ProcPriorIdLimbs.hi (sp.ids.getD j 0) := by
  let pt:=ProcPriorRoutedRawSource.raw tr
  obtain ⟨r,hr,hm,hmsg⟩:=ProcessRepairIdPreparedSend.sender view hpub I hp sp hsp fwd hdl hpar hf hF hj
  have ht0:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:(interaction ProcPriorCodecActual.publicId)∈AP.tables[0]!.interactions:=by
    rw [view.wires]
    apply ProcPriorRoutedCodecProjection.member
    · exact List.mem_iff_getElem?.mpr ⟨13,rfl⟩
    · decide +kernel
  obtain ⟨q,hq,hqm,hqmsg⟩:=ProcessRepairIdPublicReceiver.matched view h70 ht0 hr hi
    (show (interaction ProcPriorCodecActual.publicId).bus=70 by rfl)
    (show (interaction ProcPriorCodecActual.publicId).send=true by rfl) (by omega)
  have hmap:=HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyId.offset)
    ProcessRepairIdPublicFlags.verticalRead.mult tr pt 0 q 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr 0 q ProcPriorRoutedFamilyId.offset pub e)
  change publicRead.multNat tr 0 q pub=ProcessRepairIdPublicFlags.verticalRead.multNat pt 0 q pub at hmap
  rw [hmap] at hqm
  obtain ⟨hst,hact,hP⟩:=ProcessRepairIdPublicFlags.flags (ProcessRepairRawBytes.overlay_local view) hq hqm
  change cv pt 0 q (ProcPriorVertical4Linear.stage 1)=1 at hst
  change cv pt 0 q ProcPriorIdTable.act=1 at hact
  change cv pt 0 q ProcPriorIdTable.isPublic=1 at hP
  have he:publicRead.msgVal tr 0 q pub=
      [Fp.ofNat (cv pt 0 q ProcPriorIdTable.tau),Fp.ofNat (cv pt 0 q ProcPriorIdTable.ordinal),
       Fp.ofNat (cv pt 0 q ProcPriorIdTable.keyLo),Fp.ofNat (cv pt 0 q ProcPriorIdTable.keyMid),Fp.ofNat (cv pt 0 q ProcPriorIdTable.keyHi)]:=by
    simp only [publicRead,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
    change [(HorizontalTables.expression ProcPriorRoutedFamilyId.offset (ZkFormal.Chacha.Table.E.c ProcPriorIdTable.tau)).eval tr 0 q pub,
      (HorizontalTables.expression ProcPriorRoutedFamilyId.offset (ZkFormal.Chacha.Table.E.c ProcPriorIdTable.ordinal)).eval tr 0 q pub,
      (HorizontalTables.expression ProcPriorRoutedFamilyId.offset (ZkFormal.Chacha.Table.E.c ProcPriorIdTable.keyLo)).eval tr 0 q pub,
      (HorizontalTables.expression ProcPriorRoutedFamilyId.offset (ZkFormal.Chacha.Table.E.c ProcPriorIdTable.keyMid)).eval tr 0 q pub,
      (HorizontalTables.expression ProcPriorRoutedFamilyId.offset (ZkFormal.Chacha.Table.E.c ProcPriorIdTable.keyHi)).eval tr 0 q pub]=_
    simp only [HorizontalTrace.expression_eval,Codec.ev_c,pt]
    rfl
  rw [he,hmsg] at hqmsg
  have hid:sp.ids.getD j 0<18446744073709551616:=by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
    exact prepD0_ids64 hp sp hsp _ (List.getElem_mem hj)
  have hb:=ProcPriorIdLimbs.bounds _ hid
  have hn:sp.ids.length≤64:=(prepD0_sched hp sp hsp).n64
  have eq (x y:Nat) (hx:x<P) (hy:y<P) (he:Fp.ofNat x=Fp.ofNat y):x=y:=
    ProcPriorCodecSoundPublicId.nat_eq x y hx hy he
  have h0:=congrArg (fun xs:List Fp=>xs[0]!) hqmsg
  have h1:=congrArg (fun xs:List Fp=>xs[1]!) hqmsg
  have h2:=congrArg (fun xs:List Fp=>xs[2]!) hqmsg
  have h3:=congrArg (fun xs:List Fp=>xs[3]!) hqmsg
  have h4:=congrArg (fun xs:List Fp=>xs[4]!) hqmsg
  simp only [List.getElem!_cons_zero,List.getElem!_cons_succ] at h0 h1 h2 h3 h4
  have hpv:P=2013265921:=P_val
  exact ⟨q,hq,hst,hact,hP,eq _ _ (cv_lt _ _) (cv_lt _ _) h0,
    eq _ _ (cv_lt _ _) (by omega) h1,eq _ _ (cv_lt _ _) (by omega) h2,
    eq _ _ (cv_lt _ _) (by omega) h3,eq _ _ (cv_lt _ _) (by omega) h4⟩
end ZkFormal.NearV3.Candidates.ProcessRepairIdPreparedCoverage

import ZkFormal.NearV3.Candidates.ProcessRepairPublicIdSource
import ZkFormal.NearV3.Candidates.ProcessRepairIdBound
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPublicRow
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedIdBound ProcPriorRoutedFamilyId
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem authenticated {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h70:∀msg,pubCount AP pub 70 true msg=0)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)
    (sp:NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched) (fwd:List (Nat×Nat))
    (hdl:I.recs B_SDL true=(render (p.sched.map instOf) fwd).dlSend)
    (hpar:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (HorizontalTrace.project offset tr) 0 r (ProcPriorVertical4Linear.stage 1)=1)
    (ha:cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.act=1)
    (hP:cv (HorizontalTrace.project offset tr) 0 r ProcPriorIdTable.isPublic=1) :
    let pt:=HorizontalTrace.project offset tr
    cv pt 0 r ProcPriorIdTable.tau<33 ∧ cv pt 0 r ProcPriorIdTable.ordinal<sp.ids.length ∧
    cv pt 0 r ProcPriorIdTable.keyLo=ProcPriorIdLimbs.lo (sp.ids.getD (cv pt 0 r ProcPriorIdTable.ordinal) 0) ∧
    cv pt 0 r ProcPriorIdTable.keyMid=ProcPriorIdLimbs.mid (sp.ids.getD (cv pt 0 r ProcPriorIdTable.ordinal) 0) ∧
    cv pt 0 r ProcPriorIdTable.keyHi=ProcPriorIdLimbs.hi (sp.ids.getD (cv pt 0 r ProcPriorIdTable.ordinal) 0) := by
  let pt:=HorizontalTrace.project offset tr
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:publicRead∈AP.tables[0]!.interactions:=by rw [view.wires];exact public_member
  have hm:publicRead.multNat tr 0 r pub=1 := by
    have he:=HorizontalTraffic.mult_map (HorizontalTables.expression offset)
      (ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[0]!)).mult
      tr pt 0 r 0 pub (by intro e he;exact HorizontalTrace.expression_eval tr 0 r offset pub e)
    change publicRead.multNat tr 0 r pub=_ at he
    rw [he]
    apply Codec.mult_of rfl
    change zev (tenv pt 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (c ProcPriorIdTable.isPublic)))=1
    simp only [zev_mul,zev_c,cur_cv,pt,hs,ha,hP]
    rfl
  rcases recv_src view.valid ht hr hi (show publicRead.bus=70 from rfl)
    (show publicRead.send=false from rfl) (by omega : publicRead.multNat tr 0 r pub≠0) with hpbad|hsrc
  · exact (hpbad (h70 _)).elim
  · obtain ⟨t,ht,q,hq,i,hi,hb,hdir,hmsg,hmi⟩:=hsrc
    obtain ⟨tau,j,htau,hj,hpacket⟩:=ProcessRepairPublicIdSource.sender view hpub I hp sp hsp fwd hdl hpar ht hq hi hb hdir hmi
    have he:publicRead.msgVal tr 0 r pub=
      [Fp.ofNat (cv pt 0 r ProcPriorIdTable.tau),Fp.ofNat (cv pt 0 r ProcPriorIdTable.ordinal),
       Fp.ofNat (cv pt 0 r ProcPriorIdTable.keyLo),Fp.ofNat (cv pt 0 r ProcPriorIdTable.keyMid),Fp.ofNat (cv pt 0 r ProcPriorIdTable.keyHi)] := by
      simp only [publicRead,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
      change [(HorizontalTables.expression offset (c ProcPriorIdTable.tau)).eval tr 0 r pub,
        (HorizontalTables.expression offset (c ProcPriorIdTable.ordinal)).eval tr 0 r pub,
        (HorizontalTables.expression offset (c ProcPriorIdTable.keyLo)).eval tr 0 r pub,
        (HorizontalTables.expression offset (c ProcPriorIdTable.keyMid)).eval tr 0 r pub,
        (HorizontalTables.expression offset (c ProcPriorIdTable.keyHi)).eval tr 0 r pub]=_
      simp only [HorizontalTrace.expression_eval,Codec.ev_c,pt]
    rw [hpacket,he] at hmsg
    have hid:sp.ids.getD j 0<18446744073709551616 := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
      exact prepD0_ids64 hp sp hsp _ (List.getElem_mem hj)
    have hbounds:=ProcPriorIdLimbs.bounds _ hid
    have hn:sp.ids.length≤64:=(prepD0_sched hp sp hsp).n64
    have eq (x y:Nat) (hx:x<P) (hy:y<P) (he:Fp.ofNat x=Fp.ofNat y):x=y :=
      ProcPriorCodecSoundPublicId.nat_eq x y hx hy he
    have h0:=congrArg (fun xs:List Fp=>xs[0]!) hmsg
    have h1:=congrArg (fun xs:List Fp=>xs[1]!) hmsg
    have h2:=congrArg (fun xs:List Fp=>xs[2]!) hmsg
    have h3:=congrArg (fun xs:List Fp=>xs[3]!) hmsg
    have h4:=congrArg (fun xs:List Fp=>xs[4]!) hmsg
    simp only [List.getElem!_cons_zero,List.getElem!_cons_succ] at h0 h1 h2 h3 h4
    have hpv:P=2013265921:=P_val
    have et:=eq _ _ (by omega) (cv_lt _ _) h0
    have ej:=eq _ _ (by omega) (cv_lt _ _) h1
    have el:=eq _ _ (by omega) (cv_lt _ _) h2
    have em:=eq _ _ (by omega) (cv_lt _ _) h3
    have eh:=eq _ _ (by omega) (cv_lt _ _) h4
    change cv pt 0 r ProcPriorIdTable.tau<33 ∧ _
    rw [←et,←ej]
    exact ⟨htau,hj,el.symm,em.symm,eh.symm⟩
end ZkFormal.NearV3.Candidates.ProcessRepairIdPublicRow

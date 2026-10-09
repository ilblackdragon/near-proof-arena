import ZkFormal.NearV3.Candidates.ProcPriorRoutedIdBound
import ZkFormal.NearV3.Candidates.ProcessRepairFamilyId
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRoutedFamilyId ProcPriorRoutedIdBound
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem public_bound {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (n : Nat)
    (hpub:∀msg,pubCount AP pub 70 true msg=0)
    (hs:ProcPriorIdSoundBound.PublicSendBound AP tr pub n)
    {q : Nat} (hq:q<tr.height 0)
    (hst:cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 1)=1)
    (ha:cv (HorizontalTrace.project offset tr) 0 q ProcPriorIdTable.act=1)
    (hp:cv (HorizontalTrace.project offset tr) 0 q ProcPriorIdTable.isPublic=1) :
    cv (HorizontalTrace.project offset tr) 0 q ProcPriorIdTable.ordinal<n := by
  let pt:=HorizontalTrace.project offset tr
  have ht0:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:publicRead∈AP.tables[0]!.interactions:=by rw [view.wires];exact public_member
  have hm:publicRead.multNat tr 0 q pub=1 := by
    have he:=HorizontalTraffic.mult_map (HorizontalTables.expression offset)
      (ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[0]!)).mult
      tr pt 0 q 0 pub (by intro e he;exact HorizontalTrace.expression_eval tr 0 q offset pub e)
    change publicRead.multNat tr 0 q pub=_ at he
    rw [he]
    apply Codec.mult_of rfl
    change zev (tenv pt 0 q pub) (.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (c ProcPriorIdTable.isPublic)))=1
    simp only [zev_mul,zev_c,cur_cv,pt,hst,ha,hp]
    rfl
  have he:(publicRead.msgVal tr 0 q pub)[1]! = Fp.ofNat (cv pt 0 q ProcPriorIdTable.ordinal):=by
    simp only [publicRead,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
    change (HorizontalTables.expression offset (c ProcPriorIdTable.ordinal)).eval tr 0 q pub=_
    rw [HorizontalTrace.expression_eval]
    exact Codec.ev_c _ _
  rcases recv_src view.valid ht0 hq hi (by rfl : publicRead.bus=70) (by rfl : publicRead.send=false)
      (by omega : publicRead.multNat tr 0 q pub≠0) with hbad|hsrc
  · exact (hbad (hpub _)).elim
  · obtain ⟨ts,hts,r,hr,i,hi,hb,hdir,hmsg,hmi⟩:=hsrc
    have hbnd:=hs ts hts r hr i hi hb hdir hmi
    rw [hmsg,he,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show cv pt 0 q ProcPriorIdTable.ordinal<P from cv_lt _ _)] at hbnd
    exact hbnd

/-- Actual selected routed family: live found-result indices are bounded by
actual authenticated public70 suppliers. No standalone ownership premise. -/
theorem result_bound {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (n : Nat)
    (hpub70:∀msg,pubCount AP pub 70 true msg=0)
    (hpublic:ProcPriorIdSoundBound.PublicSendBound AP tr pub n)
    (hpub72:∀msg,pubCount AP pub 72 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=72) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) (hf:(i.msgVal tr tc r pub)[2]! = Fp.ofNat 1) :
    ((i.msgVal tr tc r pub)[3]!).toNat<n := by
  obtain ⟨q,hq,hstage,hact,hmsg⟩:=ProcessRepairFamilyId.family_result_source view hpub72 ht hr hi hb hs hm
  let pt:=HorizontalTrace.project offset tr
  have hfield:verticalResult.msgVal pt 0 q pub=
      [Fp.ofNat (cv pt 0 q ProcPriorIdTable.tau),Fp.ofNat (cv pt 0 q ProcPriorIdTable.ordinal),
       Fp.ofNat (cv pt 0 q ProcPriorIdTable.found),Fp.ofNat (cv pt 0 q ProcPriorIdTable.index)] := by
    simp [verticalResult,ProcPriorVertical4Linear.interaction,ProcPriorVertical4Linear.expression,
      ProcPriorIdTable.interactions,Interaction.msgVal,c,Codec.ev_c]
    exact ⟨(Fp.ofNat_toNat _).symm,(Fp.ofNat_toNat _).symm,(Fp.ofNat_toNat _).symm,(Fp.ofNat_toNat _).symm⟩
  have hfound:cv pt 0 q ProcPriorIdTable.found=1:=by
    rw [←hmsg,hfield] at hf
    simp only [List.getElem!_cons_succ,List.getElem!_cons_zero] at hf
    exact ProcPriorCodecSoundPublicId.nat_eq _ _ (cv_lt _ _) (by decide +kernel) hf
  have ht0:0<AP.tables.length:=by rw [view.length];decide +kernel
  obtain ⟨v,hv,hvs,hva,hvp,hvi⟩:=ProcPriorVerticalIdOrigin.origin (ProcessRepairRawBytes.overlay_local view) hq hstage hact hfound
  have hvbound:=public_bound view n hpub70 hpublic (by omega : v<tr.height 0) hvs hva hvp
  rw [←hmsg,hfield]
  simp only [List.getElem!_cons_succ,List.getElem!_cons_zero,Fp.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show cv pt 0 q ProcPriorIdTable.index<P from cv_lt _ _)]
  exact hvi ▸ hvbound

end ZkFormal.NearV3.Candidates.ProcessRepairIdBound

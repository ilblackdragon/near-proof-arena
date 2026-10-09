import ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthSource
import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedRawBytes

theorem entry {tr:Trace Fp} {pub:List Fp} {es:List ValE}
    (hw:ValWf es) (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {q:Nat} (hq:q<tr.height 0) (hg:cv (value tr) 0 q ValV3.vf=1) :
    ∃e,e∈es ∧ e.vid=cv (value tr) 0 q ValV3.vid ∧ e.len=cv (value tr) 0 q ValV3.len := by
  let i:Interaction:=ValV3.interactions[2]!
  have hi:i∈ValV3.interactions:=by simp [i,ValV3.interactions]
  have hm:i.multNat (value tr) 0 q pub≠0:=by
    have hc:(value tr).cell 0 q ValV3.vf=Fp.ofNat 1:=by rw [←hg];exact (Fp.ofNat_toNat _).symm
    change (if (value tr).cell 0 q ValV3.vf=1 then 1 else 0)+0≠0
    rw [hc];decide +kernel
  have hqv:q<(value tr).height 0:=hq
  have hc:=tableBusCount_pos hqv hi hm
  change tableBusCount ValV3.interactions (value tr) 0 pub B_VPARENT false (i.msgVal (value tr) 0 q pub)≠0 at hc
  rw [(hT _ _).2] at hc
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hc)
  obtain ⟨m,hm,hme⟩:=List.mem_map.mp hmem
  change m∈valRecvs es B_VPARENT at hm
  rw [Link3.vparentR] at hm
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hm
  have hcan:=hw.canon e he
  have e0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hme
  have e1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hme
  change (Fp.ofNat e.vid).toNat=cv (value tr) 0 q ValV3.vid at e0
  change (Fp.ofNat e.len).toNat=cv (value tr) 0 q ValV3.len at e1
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hcan.1] at e0
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hcan.2.1] at e1
  exact ⟨e,he,e0,e1⟩

theorem indexed {tr:Trace Fp} {pub:List Fp} {es:List ValE}
    (hw:ValWf es) (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {q:Nat} (hq:q<tr.height 0) (hg:cv (value tr) 0 q ValV3.vf=1) :
    let id:=cv (value tr) 0 q ValV3.vid
    id<es.length ∧ es[id]!.vid=id ∧ es[id]!.bytes.length=cv (value tr) 0 q ValV3.len := by
  obtain ⟨e,he,hid,hlen⟩:=entry hw hT hq hg
  obtain ⟨k,hk,rfl⟩:=List.getElem_of_mem he
  have hkid:k=cv (value tr) 0 q ValV3.vid:=
    (ProcPriorRoutedValueBytes.value_id_at hw k hk).symm.trans hid
  have hshape:=hw.shape _ (List.getElem_mem hk)
  have hlen':es[k].bytes.length=es[k].len:=by
    cases hz:es[k].vz with
    | false=>exact (hshape.2 hz).1
    | true=>rw [(hshape.1 hz).2,(hshape.1 hz).1];rfl
  dsimp only
  rw [←hkid,getElem!_pos es k hk]
  exact ⟨hk,ProcPriorRoutedValueBytes.value_id_at hw k hk,hlen'.trans hlen⟩
/-- Every live installed length response names the SAME extracted Value
entry, including its actual byte length rather than an unchecked field. -/
theorem source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 73 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=73) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃id,id<es.length ∧ es[id]!.vid=id ∧
      i.msgVal tr t r pub=[Fp.ofNat id,Fp.ofNat es[id]!.bytes.length] := by
  obtain ⟨q,hq,hg,hmsg⟩:=ProcPriorRoutedLengthSource.source hH htables hpub ht hr hi hb hs hm
  have hhead:=ProcPriorRoutedLengthSource.header hH htables hq hg
  obtain ⟨hid,hvid,hlen⟩:=indexed hw hT hq hhead
  refine ⟨cv (value tr) 0 q ValV3.vid,hid,hvid,?_⟩
  rw [←hmsg,hlen]
  change [(value tr).cell 0 q ValV3.vid,(value tr).cell 0 q ValV3.len]=_
  simp only [cv,Fp.ofNat_toNat]
end ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthView

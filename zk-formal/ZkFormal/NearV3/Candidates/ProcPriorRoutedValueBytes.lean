import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueView
import ZkFormal.NearV3.Link.Vals3
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedRawBytes
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem value_count {es:List ValE} (hw:ValWf es) :es.length≤2^22 := by
  have hp:∀e∈es,1≤if e.vz then 1 else e.len := by
    intro e he
    have hs:=hw.shape e he
    cases hz:e.vz with
    | false=>simp only [Bool.false_eq_true,ite_false];have hh:=(hs.2 hz).2;omega
    | true=>simp
  have hsum:∀ls:List ValE,(∀e∈ls,1≤if e.vz then 1 else e.len)→
      ls.length≤(ls.map (fun e=>if e.vz then 1 else e.len)).sum := by
    intro ls
    induction ls with
    | nil=>simp
    | cons e ls ih=>
      intro hp
      have he:=hp e (by simp)
      have hh:=ih (fun a ha=>hp a (List.mem_cons_of_mem _ ha))
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  have hs:=hsum es hp
  have hr:=hw.rows
  omega

/-- The extracted list retains its actual physical value IDs. There is no
fresh renumbering or independent native value list in this statement. -/
theorem value_id_at {es:List ValE} (hw:ValWf es) (k:Nat) (hk:k<es.length) :es[k].vid=k := by
  have hn:=value_count hw
  have he:=Link3.vid_at hw hn k hk
  have h0:Link3.vid0 es=0 := by
    cases es with
    | nil=>simp at hk
    | cons e es=>
      have hf:=hw.first (by simp)
      simpa [Link3.vid0] using hf
  rw [h0,Nat.zero_add,Nat.mod_eq_of_lt (show k<P by rw [P_val];omega)] at he
  exact he

theorem byte_entry {tr:Trace Fp} {pub:List Fp} {es:List ValE}
    (hw:ValWf es) (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {q:Nat} (hq:q<tr.height 0) (hg:cv (value tr) 0 q ValV3.gb=1) :
    ∃e,e∈es ∧ e.vid=cv (value tr) 0 q ValV3.vid ∧
      cv (value tr) 0 q ValV3.pos<e.bytes.length ∧
      cv (value tr) 0 q ValV3.b=e.bytes.getD (cv (value tr) 0 q ValV3.pos) 0 := by
  let i:Interaction:=ValV3.interactions[1]!
  have hi:i∈ValV3.interactions := by simp [i,ValV3.interactions]
  have hm:i.multNat (value tr) 0 q pub≠0 := by
    have hc:(value tr).cell 0 q ValV3.gb=Fp.ofNat 1 := by rw [←hg];exact (Fp.ofNat_toNat _).symm
    change (if (value tr).cell 0 q ValV3.gb=1 then 1 else 0)+0≠0
    rw [hc]
    decide +kernel
  have hqv:q<(value tr).height 0:=hq
  have hc:=tableBusCount_pos hqv hi hm
  change tableBusCount ValV3.interactions (value tr) 0 pub B_VBYTES false (i.msgVal (value tr) 0 q pub)≠0 at hc
  rw [(hT _ _).2] at hc
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hc)
  obtain ⟨m,hm,hme⟩:=List.mem_map.mp hmem
  change m∈valRecvs es B_VBYTES at hm
  simp only [valRecvs,ite_true] at hm
  obtain ⟨e,he,hm⟩:=List.mem_flatMap.mp hm
  cases hz:e.vz with
  | true=>simp [hz] at hm
  | false=>
    simp only [hz,Bool.false_eq_true,ite_false] at hm
    obtain ⟨p,hp,hpm⟩:=List.mem_map.mp hm
    have hpr:p<e.bytes.length:=List.mem_range.mp hp
    subst m
    have hshape:=(hw.shape e he).2 hz
    have hcan:=hw.canon e he
    have hpb:p<P := by omega
    have hbyte:e.bytes.getD p 0<P := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hpr,Option.getD_some]
      exact hcan.2.2.2 _ (List.getElem_mem hpr)
    have e0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hme
    have e1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hme
    have e2:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hme
    change (Fp.ofNat e.vid).toNat=cv (value tr) 0 q ValV3.vid at e0
    change (Fp.ofNat p).toNat=cv (value tr) 0 q ValV3.pos at e1
    change (Fp.ofNat (e.bytes.getD p 0)).toNat=cv (value tr) 0 q ValV3.b at e2
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hcan.1] at e0
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hpb] at e1
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hbyte] at e2
    exact ⟨e,he,e0,by omega,by rw [←e1];exact e2.symm⟩

/-- Every present RawFrame byte comes from the same extracted Value list,
with its exact natural vid and position. -/
theorem raw_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1)
    (hpres:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1) :
    ∃e,e∈es ∧ e.vid=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos<e.bytes.length ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=
        e.bytes.getD (cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos) 0 := by
  obtain ⟨q,hq,hg,hid,hpos,hbyte⟩:=byte_source hH htables hpub hr hs ha hpres
  obtain ⟨e,he,heid,hep,heb⟩:=byte_entry hw hT hq hg
  exact ⟨e,he,heid.trans hid,by rwa [hpos] at hep,by rw [←hbyte,heb,hpos]⟩
theorem raw_byte_index {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1)
    (hpres:cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1) :
    let id:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid
    let pos:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos
    id<es.length ∧ es[id]!.vid=id ∧ pos<es[id]!.bytes.length ∧
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=es[id]!.bytes.getD pos 0 := by
  obtain ⟨e,he,heid,hep,heb⟩:=raw_byte hH htables hpub hw hT hr hs ha hpres
  obtain ⟨k,hk,rfl⟩:=List.getElem_of_mem he
  have hkid:k=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid :=
    (value_id_at hw k hk).symm.trans heid
  dsimp only
  rw [←hkid,getElem!_pos es k hk]
  rw [←hkid] at heid
  exact ⟨hk,heid,hep,heb⟩

/-- A single extracted view serves all present RawFrame bytes. -/
theorem raw_view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES) :
    ∃es:List ValE,ValWf es ∧ ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es) ∧
    ∀r,r<tr.height 0→cv (ProcPriorRoutedRawSource.raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1→
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.act=1→
      cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.present=1→
      let id:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.vid
      let pos:=cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.pos
      id<es.length ∧ es[id]!.vid=id ∧ pos<es[id]!.bytes.length ∧
        cv (ProcPriorRoutedRawSource.raw tr) 0 r ProcPriorRawFrame.byte=es[id]!.bytes.getD pos 0 := by
  obtain ⟨es,hw,hT⟩:=ProcPriorRoutedValueView.view hH htables
  exact ⟨es,hw,hT,fun _ hr hs ha hp=>raw_byte_index hH htables hpub hw hT hr hs ha hp⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedValueBytes

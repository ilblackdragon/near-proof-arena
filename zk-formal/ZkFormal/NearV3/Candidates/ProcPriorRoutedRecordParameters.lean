import ZkFormal.NearV3.Candidates.ProcPriorRecordOrigin
import ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecParameters
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordParameters
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def recordTrace (tr:Trace Fp):Trace Fp:=HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr
def send :Interaction:=ProcPriorRoutedCodecProjection.interaction ProcPriorCodecParameter.interaction
def verticalRecv :Interaction:=ProcPriorVertical4Linear.interaction 3
  (ProcPriorRecordLinear.interactions 75 71 72 67 76)[7]!
def recv :Interaction:=HorizontalTables.interaction ProcPriorRoutedFamilyWrite.offset verticalRecv

theorem raw_senders :ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==76 && i.send)=[send] := rfl

theorem recv_member :recv∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hf:ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==76 && !i.send)=[recv] := rfl
  have hraw:recv∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    have hh:recv∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==76 && !i.send) := by
      rw [hf];exact List.mem_singleton_self _
    exact (List.mem_filter.mp hh).1
  have hp:recv∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠recv := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠recv := by
    intro he
    have hb:=congrArg Interaction.bus he
    change 0=76 at hb
    omega
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠recv) (hd true) (hd false)).mp hall) _ hp rfl

theorem sender_eq {i:Interaction} (hi:i∈ProcPriorComparatorRoutedFamily.fused.interactions)
    (hb:i.bus=76) (hs:i.send=true) :i=send := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=76→j.send=true→j=send := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==76 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=76→j.send=true→j=send :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=76→j.send=true→j=send)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs

theorem other_tables {AP:AirP} (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠76 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 76)))=true := by decide +kernel
  intro t ht hn i hi hs
  rw [htables] at ht hi
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
    have he:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t-1]?=some (ProcPriorComparatorRoutedFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he,List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hs] using hv

theorem recv_message (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    recv.msgVal tr t r pub=verticalRecv.msgVal (recordTrace tr) t r pub := by
  simp only [recv,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e

theorem recv_mult (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    recv.multNat tr t r pub=verticalRecv.multNat (recordTrace tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyWrite.offset) _ tr (recordTrace tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e)

theorem header_live {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hs:cv (recordTrace tr) t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) t r ProcPriorRecordTable.act=1)
    (hw:cv (recordTrace tr) t r ProcPriorRecordTable.sender+
      cv (recordTrace tr) t r ProcPriorRecordTable.receiver+cv (recordTrace tr) t r ProcPriorRecordTable.amount=0) :
    recv.multNat tr t r pub≠0 := by
  rw [recv_mult]
  have hcell (x v:Nat) (hx:cv (recordTrace tr) t r x=v):(recordTrace tr).cell t r x=Fp.ofNat v := by
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  have hsend:cv (recordTrace tr) t r ProcPriorRecordTable.sender=0 := by omega
  have hrec:cv (recordTrace tr) t r ProcPriorRecordTable.receiver=0 := by omega
  have hamt:cv (recordTrace tr) t r ProcPriorRecordTable.amount=0 := by omega
  have h1:=hcell _ _ hs
  have h2:=hcell _ _ ha
  have h3:=hcell _ _ hsend
  have h4:=hcell _ _ hrec
  have h5:=hcell _ _ hamt
  change (if (recordTrace tr).cell t r (ProcPriorVertical4Linear.stage 3)*
    ((recordTrace tr).cell t r ProcPriorRecordTable.act+
      -((recordTrace tr).cell t r ProcPriorRecordTable.sender+
        (recordTrace tr).cell t r ProcPriorRecordTable.receiver+
        (recordTrace tr).cell t r ProcPriorRecordTable.amount))=1 then 1 else 0)+0≠0
  rw [h1,h2,h3,h4,h5]
  decide +kernel

/-- The real bus76 supplier is the SPAR-authenticated Codec first header. -/
theorem header_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) 0 r ProcPriorRecordTable.act=1)
    (hw:cv (recordTrace tr) 0 r ProcPriorRecordTable.sender+
      cv (recordTrace tr) 0 r ProcPriorRecordTable.receiver+cv (recordTrace tr) 0 r ProcPriorRecordTable.amount=0) :
    cv (recordTrace tr) 0 r ProcPriorRecordTable.tau<33 ∧
    1≤cv (recordTrace tr) 0 r ProcPriorRecordTable.shards ∧ cv (recordTrace tr) 0 r ProcPriorRecordTable.shards≤64 := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hi:recv∈AP.tables[0]!.interactions := by rw [htables];exact recv_member
  rcases recv_src hH ht hr hi (show recv.bus=76 from rfl) (show recv.send=false from rfl) (header_live hs ha hw) with hp|hp
  · exact (hp (h76 _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables htables t' ht' hn j hj hjs hjb)
    subst t'
    rw [htables] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    unfold send at hjm hmsg
    rw [ProcPriorRoutedCodecProjection.mult] at hjm
    rw [ProcPriorRoutedCodecProjection.message,recv_message] at hmsg
    have hF:cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.kF=1 := by
      have hh:(c Codec.kF).eval (ProcPriorRoutedCodecProjection.codec tr) 0 q pub=1 := by
        by_cases he:(c Codec.kF).eval (ProcPriorRoutedCodecProjection.codec tr) 0 q pub=1
        · exact he
        · simp only [ProcPriorCodecParameter.interaction,Interaction.multNat,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hjm
          exact (hjm rfl).elim
      change (ProcPriorRoutedCodecProjection.codec tr).cell 0 q Codec.kF=1 at hh
      unfold cv
      rw [hh]
      rfl
    have hL:=ProcPriorRoutedCodecParameters.local_codec hH htables
    have hk:=ProcPriorCodecSoundGeometry.kinds hL hq
    have hact:cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.act=1 := by omega
    have hb:=ProcPriorRoutedCodecParameters.active_small hH htables hpub I Ps fwd hrec hlen hns hq hact
    have he0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
    have he1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
    change cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.tau=cv (recordTrace tr) 0 r ProcPriorRecordTable.tau at he0
    change cv (ProcPriorRoutedCodecProjection.codec tr) 0 q Codec.nn=cv (recordTrace tr) 0 r ProcPriorRecordTable.shards at he1
    omega
/-- Every arbitrary active Record row carries authentic bounded parameters,
via its actual header and the concrete Codec-to-Record bus76 join. -/
theorem active_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat) (Ps:List InstPub) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render Ps fwd).par) (hlen:Ps.length≤33)
    (hns:∀P0∈Ps,1≤P0.n ∧ P0.n≤64)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) 0 r ProcPriorRecordTable.act=1) :
    cv (recordTrace tr) 0 r ProcPriorRecordTable.tau<33 ∧
    1≤cv (recordTrace tr) 0 r ProcPriorRecordTable.shards ∧ cv (recordTrace tr) 0 r ProcPriorRecordTable.shards≤64 := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  obtain ⟨f,hfr,hfs,hfa,hfw,hft,hfn⟩:=ProcPriorRecordOrigin.header_origin hv r hr hs ha
  have hb:=header_bounds hH htables hpub h76 I Ps fwd hrec hlen hns (show f<tr.height 0 by omega) hfs hfa hfw
  change cv (recordTrace tr) 0 f ProcPriorRecordTable.tau=cv (recordTrace tr) 0 r ProcPriorRecordTable.tau at hft
  change cv (recordTrace tr) 0 f ProcPriorRecordTable.shards=cv (recordTrace tr) 0 r ProcPriorRecordTable.shards at hfn
  rw [hft,hfn] at hb
  exact hb

theorem prepared_active_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (recordTrace tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (recordTrace tr) 0 r ProcPriorRecordTable.act=1) :
    cv (recordTrace tr) 0 r ProcPriorRecordTable.tau<33 ∧
    1≤cv (recordTrace tr) 0 r ProcPriorRecordTable.shards ∧ cv (recordTrace tr) 0 r ProcPriorRecordTable.shards≤64 := by
  have hl:(p.sched.map instOf).length≤33 := by
    rw [List.length_map];exact prepD0_len hprep
  have hn:∀P0∈p.sched.map instOf,1≤P0.n ∧ P0.n≤64 := by
    intro P0 hm
    obtain ⟨sp,hsp,he⟩:=List.mem_map.mp hm
    subst P0
    have hs:=prepD0_sched hprep sp hsp
    exact ⟨hs.n1,hs.n64⟩
  exact active_bounds hH htables hpub h76 I _ fwd hrec hl hn hr hs ha
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordParameters

import ZkFormal.NearV3.Candidates.ProcPriorRawSound
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRawSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset:Nat:=ProcPriorRoutedFamilyWrite.offset
def raw (tr:Trace Fp):Trace Fp:=HorizontalTrace.project offset tr
def verticalRead:Interaction:=ProcPriorVertical4Linear.interaction 2
  (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)[4]!
def read:Interaction:=HorizontalTables.interaction offset verticalRead

theorem raw_senders :ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==75 && i.send)=[read] := rfl


theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=75) (hs:i.send=true) :i=read := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=75→j.send=true→j=read := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==75 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=75→j.send=true→j=read :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=75→j.send=true→j=read)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs


theorem projected_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    read.msgVal tr t r pub=verticalRead.msgVal (HorizontalTrace.project offset tr) t r pub := by
  simp only [read,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r offset pub e

theorem projected_mult (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    read.multNat tr t r pub=verticalRead.multNat (HorizontalTrace.project offset tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression offset) _ tr (HorizontalTrace.project offset tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r offset pub e)

theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠75 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 75)))=true := by decide +kernel
  intro t ht hn i hi hs
  rw [htables] at ht hi
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
    have he:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t-1]?=some (ProcPriorComparatorRoutedFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he]
      rw [List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hs] using hv


theorem flags {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:verticalRead.multNat tr t r pub≠0) :
    cv tr t r (ProcPriorVertical4Linear.stage 2)=1 ∧ cv tr t r ProcPriorRawFrame.rec=1 ∧ cv tr t r ProcPriorRawFrame.act=1 := by
  have hg:(Expr.mul (c (ProcPriorVertical4Linear.stage 2)) (c ProcPriorRawFrame.rec)).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c (ProcPriorVertical4Linear.stage 2)) (c ProcPriorRawFrame.rec)).eval tr t r pub=1
    · exact he
    · have hmult:verticalRead.mult=[Expr.mul (c (ProcPriorVertical4Linear.stage 2)) (c ProcPriorRawFrame.rec)] := rfl
      simp only [Interaction.multNat,hmult,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 2)) (by simp [ProcPriorVertical4Linear.windows]))
  change tr.cell t r (ProcPriorVertical4Linear.stage 2)*tr.cell t r ProcPriorRawFrame.rec=1 at hg
  have hcell (x:Nat):tr.cell t r x=Fp.ofNat (cv tr t r x) := (Fp.ofNat_toNat _).symm
  have hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
    · rw [hcell _,hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by change (0:Fp)*_=1 at hg;grind only)).elim
    · exact hz
  rw [hcell (ProcPriorVertical4Linear.stage 2),hs] at hg
  have hre:tr.cell t r ProcPriorRawFrame.rec=1 := by change (1:Fp)*_=1 at hg;grind only
  have hrn:cv tr t r ProcPriorRawFrame.rec=1 := by unfold cv;rw [hre];rfl
  have hk:=ProcPriorRawSound.kinds hL hr hs
  have ha:=ProcPriorRawSound.flag hL hr hs ProcPriorRawFrame.act (by simp)
  exact ⟨hs,hrn,by omega⟩

/-- Every actual record-byte receiver is supplied by an actual stage2
RawFrame record row with the exact four-field payload. -/
theorem record_source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 75 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=75) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃q,q<tr.height 0 ∧ cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv (raw tr) 0 q ProcPriorRawFrame.rec=1 ∧ cv (raw tr) 0 q ProcPriorRawFrame.act=1 ∧
      verticalRead.msgVal (raw tr) 0 q pub=i.msgVal tr t r pub := by
  rcases recv_src hH ht hr hi hb hs hm with hp|hp
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables htables t' ht' hn j hj hjs hjb)
    subst t'
    rw [htables] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hjm
    have ht0:0<AP.tables.length := by rw [htables];decide +kernel
    have hL:=local_of_holdsP hH ht0
    rw [htables] at hL
    have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
    obtain ⟨hst,hrec,hact⟩:=flags hv hq hjm
    exact ⟨q,hq,hst,hrec,hact,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRawSource

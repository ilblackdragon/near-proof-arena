import ZkFormal.NearV3.Candidates.ProcPriorRoutedValueView
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
def offset:Nat:=ProcPriorRoutedRawBytes.valueOffset
def announcement:Interaction:=ProcPriorValueLength.interaction 73
def sender:Interaction:=HorizontalTables.interaction offset announcement
theorem raw_senders :ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==73 && i.send)=[sender] := rfl


theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=73) (hs:i.send=true) :i=sender := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=73→j.send=true→j=sender := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==73 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=73→j.send=true→j=sender :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=73→j.send=true→j=sender)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs


theorem projected_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    sender.msgVal tr t r pub=announcement.msgVal (HorizontalTrace.project offset tr) t r pub := by
  simp only [sender,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r offset pub e

theorem projected_mult (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    sender.multNat tr t r pub=announcement.multNat (HorizontalTrace.project offset tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression offset) _ tr (HorizontalTrace.project offset tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r offset pub e)

theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠73 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 73)))=true := by decide +kernel
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


theorem source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 73 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=73) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃q,q<tr.height 0 ∧ cv (ProcPriorRoutedRawBytes.value tr) 0 q ProcPriorValueLength.gate=1 ∧
      announcement.msgVal (ProcPriorRoutedRawBytes.value tr) 0 q pub=i.msgVal tr t r pub := by
  rcases recv_src hH ht hr hi hb hs hm with hp|hp
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0:=Classical.byContradiction (fun hn=>other_tables htables t' ht' hn j hj hjs hjb)
    subst t'
    rw [htables] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hjm
    have hg:(ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1:=by
      by_cases he:(ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1
      · exact he
      · change (if (ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1 then 1 else 0)+0≠0 at hjm
        simp only [he,ite_false,Nat.zero_add] at hjm
        exact (hjm rfl).elim
    refine ⟨q,hq,?_,hmsg⟩
    unfold cv
    rw [hg]
    rfl
theorem header {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {q:Nat} (hq:q<tr.height 0)
    (hg:cv (ProcPriorRoutedRawBytes.value tr) 0 q ProcPriorValueLength.gate=1) :
    cv (ProcPriorRoutedRawBytes.value tr) 0 q ValV3.vf=1 := by
  let e:Expr:=.mul (c ProcPriorValueLength.gate) (ZkFormal.Near.Dsl.not (c ValV3.vf))
  have hem:HorizontalTables.expression offset e∈ProcPriorComparatorRoutedFamily.fused.constraints:=by
    change _∈ProcPriorComparatorRoutedFamily.raw.constraints
    apply List.mem_flatMap.mpr
    refine ⟨_,ProcPriorRoutedValueView.location,List.mem_map.mpr ⟨e,?_,rfl⟩⟩
    change e∈Rcpt.Candidates.EmptyValueFusion.valueTable.constraints
    simp [e,Rcpt.Candidates.EmptyValueFusion.valueTable,ProcPriorValueLength.table,c,ZkFormal.Near.Dsl.c]
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hc:=local_of_holdsP hH ht q hq (HorizontalTables.expression offset e)
  rw [htables] at hc
  have heq:=hc hem
  rw [HorizontalTrace.expression_eval] at heq
  have hgc:(ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate=1:=by
    rw [←Fp.ofNat_toNat ((ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate)]
    change Fp.ofNat (cv (ProcPriorRoutedRawBytes.value tr) 0 q ProcPriorValueLength.gate)=1
    rw [hg];rfl
  change (ProcPriorRoutedRawBytes.value tr).cell 0 q ProcPriorValueLength.gate *
    (1 + - (ProcPriorRoutedRawBytes.value tr).cell 0 q ValV3.vf)=0 at heq
  rw [hgc] at heq
  have hvc:(ProcPriorRoutedRawBytes.value tr).cell 0 q ValV3.vf=1:=by grind
  unfold cv
  rw [hvc]
  rfl
end ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthSource

import ZkFormal.NearV3.Candidates.ProcessRepairNativeIdQuery
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordIdSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
open ProcPriorRoutedRawSource (raw)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def query:Interaction:=HorizontalTables.interaction ProcPriorRoutedFamilyWrite.offset ProcPriorRecordQueryActivity.query

theorem raw_senders:ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==71 && i.send)=[query]:=rfl
theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=71) (hs:i.send=true) :i=query := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=71→j.send=true→j=query := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==71 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=71→j.send=true→j=query :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=71→j.send=true→j=query)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs


theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠71 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 71)))=true := by decide +kernel
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


theorem message (tr:Trace Fp) (t r:Nat) (pub:List Fp):
    query.msgVal tr t r pub=ProcPriorRecordQueryActivity.query.msgVal (raw tr) t r pub:=by
  simp only [query,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e

theorem mult (tr:Trace Fp) (t r:Nat) (pub:List Fp):
    query.multNat tr t r pub=ProcPriorRecordQueryActivity.query.multNat (raw tr) t r pub:=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyWrite.offset) _ tr (raw tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e)

theorem source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 71 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=71) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0):
    ∃q,q<tr.height 0 ∧ ProcPriorRecordQueryActivity.query.multNat (raw tr) 0 q pub≠0 ∧
      ProcPriorRecordQueryActivity.query.msgVal (raw tr) 0 q pub=i.msgVal tr t r pub:=by
  rcases recv_src view.valid ht hr hi hb hs hm with hp|hp
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0:=Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t'
      (by simpa [ProcessRepairBalance.reference,←view.length] using ht') hn j
      (by simpa only [view.wires t',ProcessRepairBalance.reference] using hj) hjs hjb)
    subst t'
    rw [view.wires] at hj
    have he:=sender_eq hj hjb hjs
    subst j
    rw [message] at hmsg
    rw [mult] at hjm
    exact ⟨q,hq,hjm,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRecordIdSource

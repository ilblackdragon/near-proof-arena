import ZkFormal.NearV3.Candidates.ProcPriorRoutedMemoryOrder
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def read :Interaction:=ProcPriorCodecFamilyRead.read

theorem raw_senders :ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==68 && i.send)=[read] := rfl

theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=68) (hs:i.send=true) :i=read := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=68→j.send=true→j=read := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==68 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=68→j.send=true→j=read :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=68→j.send=true→j=read)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs

theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠68 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 68)))=true := by decide +kernel
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

/-- Actual repaired-family prior68 semantics with no supplied comparison,
order, gate, ownership, window or Local premise. Only authenticated packed
address/write-stamp bounds remain before original decoded-write identification. -/
theorem consumer {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub68:∀msg,pubCount AP pub 68 true msg=0)
    (hpub40:∀seg∈AP.pubSegs,seg.bus≠40)
    (haddr:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29)
    (hstamp:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→
      cv (memory tr) 0 r stamp+1<2^29)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.tables[0]! := by rw [htables]
  rcases recv_src hH ht hr hi hib his him with hp|hs
  · exact (hp (hpub68 _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hs
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables htables t' ht' hn j hj hjs hjb)
    subst t'
    rw [htab] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    change ProcPriorCodecFamilyRead.read.msgVal tr 0 q pub=i.msgVal tr tc r pub at hmsg
    change ProcPriorCodecFamilyRead.read.multNat tr 0 q pub≠0 at hjm
    rw [ProcPriorCodecFamilyRead.projected_message] at hmsg
    rw [ProcPriorCodecFamilyRead.projected_mult] at hjm
    have hp:=ProcPriorRoutedMemoryOrder.local_memory hH htables
    obtain ⟨hstage,ha,hquery⟩:=ProcPriorVerticalReadSound.flags hp hq hjm
    obtain ⟨ho,hb,hst⟩:=ProcPriorRoutedMemoryOrder.order_predicates hH htables hpub40 haddr hstamp
    exact ⟨q,hq,⟨hstage,ha⟩,hquery,hmsg,
      ProcPriorVerticalLastWrite.query_last_write hp ho hb hst hq ⟨hstage,ha⟩ hquery⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedLastWrite

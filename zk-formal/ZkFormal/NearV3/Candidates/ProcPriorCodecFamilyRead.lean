import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyProjection
import ZkFormal.NearV3.Candidates.InteractionTriplesTransport
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset : Nat:=((ProcPriorCodecActualFamily.selected.take 19).map (·.width)).sum
def read : Interaction:=HorizontalTables.interaction offset ProcPriorVerticalReadSound.read

theorem raw_senders :ProcPriorCodecActualFamily.raw.interactions.filter (fun i=>i.bus==68 && i.send)=[read] := rfl

theorem overlay_location :HorizontalTables.shifted offset ProcPriorCodecActualFamily.overlay∈
    HorizontalTables.layout 0 ProcPriorCodecActualFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorCodecActualFamily.selected)[19]?=
    some (HorizontalTables.shifted offset ProcPriorCodecActualFamily.overlay) := rfl
  exact List.mem_iff_getElem?.mpr ⟨19,he⟩

theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorCodecActualFamily.tables[0]!).interactions)
    (hb:i.bus=68) (hs:i.send=true) :i=read := by
  have hp:∀j∈ProcPriorCodecActualFamily.paired.interactions,j.bus=68→j.send=true→j=read := by
    intro j hj hb hs
    have hj':j∈ProcPriorCodecActualFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorCodecActualFamily.raw.interactions.filter (fun i=>i.bus==68 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorCodecActualFamily.paired.interactions,
      j.bus=68→j.send=true→j=read :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=68→j.send=true→j=read)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs

theorem projected_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:Local (ProcPriorCodecActualFamily.tables[0]!).constraints tr t pub) :
    ProcPriorVerticalMemorySound.LocalV (HorizontalTrace.project offset tr) t pub := by
  rw [ProcPriorCodecFamilyProjection.constraints_same] at hL
  intro r hr e he
  rw [←HorizontalTrace.expression_eval]
  have hem:e∈ProcPriorCodecActualFamily.overlay.constraints := by
    rw [ProcPriorCodecFamilyProjection.overlay_constraints];exact he
  exact hL r hr _ (List.mem_flatMap.mpr ⟨HorizontalTables.shifted offset ProcPriorCodecActualFamily.overlay,
    overlay_location,List.mem_map.mpr ⟨e,hem,rfl⟩⟩)

theorem projected_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    read.msgVal tr t r pub=ProcPriorVerticalReadSound.read.msgVal (HorizontalTrace.project offset tr) t r pub := by
  simp only [read,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r offset pub e

theorem projected_mult (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    read.multNat tr t r pub=ProcPriorVerticalReadSound.read.multNat (HorizontalTrace.project offset tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression offset) _ tr (HorizontalTrace.project offset tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r offset pub e)

theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorCodecActualFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠68 := by
  have hall:((ProcPriorCodecActualFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 68)))=true := by decide +kernel
  intro t ht hn i hi hs
  rw [htables] at ht hi
  have hm:ProcPriorCodecActualFamily.tables[t]!∈ProcPriorCodecActualFamily.tables.drop 1 := by
    have he:(ProcPriorCodecActualFamily.tables.drop 1)[t-1]?=some (ProcPriorCodecActualFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he]
      rw [List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorCodecActualFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hs] using hv

/-- Every actual family bus68 consumer is matched to the physical stage0
memory query, with horizontal offsets, pairing and triple packing eliminated.
Only public-bus exclusion and exclusivity against other physical tables are
assumed; local memory/window shape is extracted from actual family validity. -/
theorem query_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (ht0:0<AP.tables.length)
    (htab:AP.tables[0]! =ProcPriorCodecActualFamily.tables[0]!)
    (honly:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠68)
    (hpub:∀msg,pubCount AP pub 68 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=68) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 0)=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (HorizontalTrace.project offset tr) 0 q pub=i.msgVal tr tc r pub ∧
      ((cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.lo=0 ∧
        cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.hi=0) ∨
       ∃v,q=v+1 ∧ cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.act=1 ∧
         cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.query=0 ∧
         ProcPriorMemoryTable.addr.eval (HorizontalTrace.project offset tr) 0 v pub=
           ProcPriorMemoryTable.addr.eval (HorizontalTrace.project offset tr) 0 q pub ∧
         cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.lo=cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.lo ∧
         cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.hi=cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.hi) := by
  rcases recv_src hH ht hr hi hb hs hm with hp|hs'
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hs'
    have he:t'=0 := Classical.byContradiction (fun hn=>honly t' ht' hn j hj hjs hjb)
    subst t'
    rw [htab] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hjm
    have hL:=local_of_holdsP hH ht0
    rw [htab] at hL
    have hp:=projected_local hL
    obtain ⟨hstage,ha,hquery⟩:=ProcPriorVerticalReadSound.flags hp hq hjm
    exact ⟨q,hq,hstage,hmsg,ProcPriorVerticalMemorySound.query_origin hp hq hstage ha hquery⟩
theorem family_query_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorCodecActualFamily.tables)
    (hpub:∀msg,pubCount AP pub 68 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=68) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 0)=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (HorizontalTrace.project offset tr) 0 q pub=i.msgVal tr tc r pub ∧
      ((cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.lo=0 ∧
        cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.hi=0) ∨
       ∃v,q=v+1 ∧ cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.act=1 ∧
         cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.query=0 ∧
         ProcPriorMemoryTable.addr.eval (HorizontalTrace.project offset tr) 0 v pub=
           ProcPriorMemoryTable.addr.eval (HorizontalTrace.project offset tr) 0 q pub ∧
         cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.lo=cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.lo ∧
         cv (HorizontalTrace.project offset tr) 0 v ProcPriorMemoryTable.hi=cv (HorizontalTrace.project offset tr) 0 q ProcPriorMemoryTable.hi) := by
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorCodecActualFamily.tables[0]! := by rw [htables]
  exact query_source hH ht0 htab (other_tables htables) hpub ht hr hi hb hs hm
end ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead

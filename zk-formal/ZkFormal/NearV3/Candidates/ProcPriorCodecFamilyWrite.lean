import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead
import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyProjection
import ZkFormal.NearV3.Candidates.InteractionTriplesTransport
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32767
set_option maxHeartbeats 1000000

def offset : Nat:=((ProcPriorCodecActualFamily.selected.take 19).map (·.width)).sum
def verticalWrite : Interaction:=ProcPriorVertical4Linear.interaction 3 ((ProcPriorRecordLinear.interactions 75 71 72 67 76)[6]!)
def write : Interaction:=HorizontalTables.interaction offset verticalWrite

theorem raw_senders :ProcPriorCodecActualFamily.raw.interactions.filter (fun i=>i.bus==67 && i.send)=[write] := rfl

theorem overlay_location :HorizontalTables.shifted offset ProcPriorCodecActualFamily.overlay∈
    HorizontalTables.layout 0 ProcPriorCodecActualFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorCodecActualFamily.selected)[19]?=
    some (HorizontalTables.shifted offset ProcPriorCodecActualFamily.overlay) := rfl
  exact List.mem_iff_getElem?.mpr ⟨19,he⟩

theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorCodecActualFamily.tables[0]!).interactions)
    (hb:i.bus=67) (hs:i.send=true) :i=write := by
  have hp:∀j∈ProcPriorCodecActualFamily.paired.interactions,j.bus=67→j.send=true→j=write := by
    intro j hj hb hs
    have hj':j∈ProcPriorCodecActualFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorCodecActualFamily.raw.interactions.filter (fun i=>i.bus==67 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorCodecActualFamily.paired.interactions,
      j.bus=67→j.send=true→j=write :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=67→j.send=true→j=write)
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
    write.msgVal tr t r pub=verticalWrite.msgVal (HorizontalTrace.project offset tr) t r pub := by
  simp only [write,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r offset pub e

theorem projected_mult (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    write.multNat tr t r pub=verticalWrite.multNat (HorizontalTrace.project offset tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression offset) _ tr (HorizontalTrace.project offset tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r offset pub e)

theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorCodecActualFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠67 := by
  have hall:((ProcPriorCodecActualFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 67)))=true := by decide +kernel
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


theorem write_flags {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:verticalWrite.multNat tr t r pub≠0) :
    cv tr t r (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t r ProcPriorRecordTable.writeGate=1 := by
  open ZkFormal.Chacha.Table.E in
  have hg:(Expr.mul (c (ProcPriorVertical4Linear.stage 3)) (c ProcPriorRecordTable.writeGate)).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c (ProcPriorVertical4Linear.stage 3)) (c ProcPriorRecordTable.writeGate)).eval tr t r pub=1
    · exact he
    · have heq:verticalWrite.mult=[Expr.mul (c (ProcPriorVertical4Linear.stage 3)) (c ProcPriorRecordTable.writeGate)] := rfl
      simp only [Interaction.multNat,heq,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hsbit:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 3)) (by simp [ProcPriorVertical4Linear.windows]))
  change tr.cell t r (ProcPriorVertical4Linear.stage 3)*tr.cell t r ProcPriorRecordTable.writeGate=1 at hg
  have hcell (x : Nat) :tr.cell t r x=Fp.ofNat (cv tr t r x) := (Fp.ofNat_toNat _).symm
  have hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hz|hz
    · rw [hcell _,hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by change (0:Fp)*_=1 at hg;grind only)).elim
    · exact hz
  rw [hcell (ProcPriorVertical4Linear.stage 3),hs] at hg
  have hw:tr.cell t r ProcPriorRecordTable.writeGate=1 := by change (1:Fp)*_=1 at hg;grind only
  exact ⟨hs,by unfold cv;rw [hw];rfl⟩

/-- Every physical prior-memory write receiver is supplied by the actual selected
Record component. Generated-trace inventories are not assumptions here. -/
theorem family_write_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorCodecActualFamily.tables)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=67) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv (HorizontalTrace.project offset tr) 0 q ProcPriorRecordTable.writeGate=1 ∧
      verticalWrite.msgVal (HorizontalTrace.project offset tr) 0 q pub=i.msgVal tr tc r pub ∧
      verticalWrite.multNat (HorizontalTrace.project offset tr) 0 q pub≠0 := by
  rcases recv_src hH ht hr hi hb hs hm with hp|hs'
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hs'
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
    have hp:=projected_local hL
    obtain ⟨hstage,hgate⟩:=write_flags hp hq hjm
    exact ⟨q,hq,hstage,hgate,hmsg,hjm⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyWrite

import ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyWrite
import ZkFormal.NearV3.Candidates.ProcPriorVerticalIdOrigin
import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead
import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyProjection
import ZkFormal.NearV3.Candidates.InteractionTriplesTransport
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyId
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32767
set_option maxHeartbeats 1000000

def offset : Nat:=((ProcPriorComparatorRoutedFamily.selected.take 19).map (·.width)).sum
def verticalResult : Interaction:=ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[2]!)
def result : Interaction:=HorizontalTables.interaction offset verticalResult

theorem raw_senders :ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==72 && i.send)=[result] := rfl

theorem overlay_location :HorizontalTables.shifted offset (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay)∈
    HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[19]?=
    some (HorizontalTables.shifted offset (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay)) := rfl
  exact List.mem_iff_getElem?.mpr ⟨19,he⟩

theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=72) (hs:i.send=true) :i=result := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=72→j.send=true→j=result := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==72 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=72→j.send=true→j=result :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=72→j.send=true→j=result)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs

theorem constraints_same :
    (ProcPriorComparatorRoutedFamily.tables[0]!).constraints=ProcPriorComparatorRoutedFamily.raw.constraints := rfl

theorem projected_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:Local (ProcPriorComparatorRoutedFamily.tables[0]!).constraints tr t pub) :
    ProcPriorVerticalMemorySound.LocalV (HorizontalTrace.project offset tr) t pub := by
  rw [constraints_same] at hL
  intro r hr e he
  rw [←HorizontalTrace.expression_eval]
  have hem:e∈(ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay).constraints := by
    change e∈ProcPriorCodecActualFamily.overlay.constraints
    rw [ProcPriorCodecFamilyProjection.overlay_constraints];exact he
  exact hL r hr _ (List.mem_flatMap.mpr ⟨HorizontalTables.shifted offset (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay),
    overlay_location,List.mem_map.mpr ⟨e,hem,rfl⟩⟩)

theorem projected_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    result.msgVal tr t r pub=verticalResult.msgVal (HorizontalTrace.project offset tr) t r pub := by
  simp only [result,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r offset pub e

theorem projected_mult (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    result.multNat tr t r pub=verticalResult.multNat (HorizontalTrace.project offset tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression offset) _ tr (HorizontalTrace.project offset tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r offset pub e)

theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠72 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 72)))=true := by decide +kernel
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

theorem result_flags {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:verticalResult.multNat tr t r pub≠0) :
    cv tr t r (ProcPriorVertical4Linear.stage 1)=1 ∧ cv tr t r ProcPriorIdTable.act=1 := by
  open ZkFormal.Chacha.Table.E in
  have hg:(Expr.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (ProcPriorIdTable.notE (c ProcPriorIdTable.isPublic)))).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (ProcPriorIdTable.notE (c ProcPriorIdTable.isPublic)))).eval tr t r pub=1
    · exact he
    · have heq:verticalResult.mult=[Expr.mul (c (ProcPriorVertical4Linear.stage 1))
          (.mul (c ProcPriorIdTable.act) (ProcPriorIdTable.notE (c ProcPriorIdTable.isPublic)))] := rfl
      simp only [Interaction.multNat,heq,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hsbit:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 1)) (by simp [ProcPriorVertical4Linear.windows]))
  change tr.cell t r (ProcPriorVertical4Linear.stage 1)*(tr.cell t r ProcPriorIdTable.act*(1 + -tr.cell t r ProcPriorIdTable.isPublic))=1 at hg
  have hc (x : Nat) :tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  have hs:cv tr t r (ProcPriorVertical4Linear.stage 1)=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hz|hz
    · rw [hc _,hz] at hg
      have hn:(0:Fp)≠1:=by decide +kernel
      exact (hn (by change (0:Fp)*_=1 at hg;grind only)).elim
    · exact hz
  have he:=ProcPriorVerticalIdRows.component_value hL hr hs (Table.boolC ProcPriorIdTable.act)
    (by simp [ProcPriorIdTable.constraints])
  have hb:cv tr t r ProcPriorIdTable.act≤1:=Codec.bool_of_eval (pub:=pub) he
  have ha:cv tr t r ProcPriorIdTable.act=1:=by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
    · rw [hc ProcPriorIdTable.act,hz] at hg
      have hn:(0:Fp)≠1:=by decide +kernel
      exact (hn (by change _*((0:Fp)*_)=1 at hg;grind only)).elim
    · exact hz
  exact ⟨hs,ha⟩

/-- Actual selected-family ID72 supplier classification, including horizontal
projection and stage1 gating. No standalone-ID ownership premise remains. -/
theorem family_result_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 72 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=72) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 1)=1 ∧
      cv (HorizontalTrace.project offset tr) 0 q ProcPriorIdTable.act=1 ∧
      verticalResult.msgVal (HorizontalTrace.project offset tr) 0 q pub=i.msgVal tr tc r pub := by
  rcases recv_src hH ht hr hi hb hs hm with hp|hsrc
  · exact (hp (hpub _)).elim
  · obtain ⟨ts,hts,q,hq,j,hj,hbus,hdir,hmsg,hmj⟩:=hsrc
    have he:ts=0:=Classical.byContradiction (fun hn=>other_tables htables ts hts hn j hj hdir hbus)
    subst ts
    rw [htables] at hj
    have hej:=sender_eq hj hbus hdir
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hmj
    have ht0:0<AP.tables.length:=by rw [htables];decide +kernel
    have hL:=local_of_holdsP hH ht0
    rw [htables] at hL
    obtain ⟨hstage,hact⟩:=result_flags (projected_local hL) hq hmj
    exact ⟨q,hq,hstage,hact,hmsg⟩

end ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyId

import ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead
import ZkFormal.NearV3.Candidates.ProcComparatorSound
namespace ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedSound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def comparatorOffset :Nat:=((ProcPriorCodecActualFamily.selected.take 12).map (·.width)).sum

def receiver :Interaction :=HorizontalTables.interaction comparatorOffset (Cmp.interactions 40)[0]!
def comparator (tr : Trace Fp) :Trace Fp :=HorizontalTrace.project comparatorOffset tr

theorem raw_receivers :ProcPriorProcessRepairedFamily.raw.interactions.filter (fun i=>i.bus==40 && !i.send)=[receiver] := rfl

theorem comparator_location :HorizontalTables.shifted comparatorOffset (Cmp.table 40)∈
    HorizontalTables.layout 0 ProcPriorProcessRepairedFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorProcessRepairedFamily.selected)[12]?=
    some (HorizontalTables.shifted comparatorOffset (Cmp.table 40)) := rfl
  exact List.mem_iff_getElem?.mpr ⟨_,he⟩

theorem receiver_eq {i : Interaction} (hi:i∈ProcPriorProcessRepairedFamily.fused.interactions)
    (hb:i.bus=40) (hs:i.send=false) :i=receiver := by
  have hp:∀j∈ProcPriorProcessRepairedFamily.paired.interactions,j.bus=40→j.send=false→j=receiver := by
    intro j hj hb hs
    have hj':j∈ProcPriorProcessRepairedFamily.raw.interactions := (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorProcessRepairedFamily.raw.interactions.filter (fun i=>i.bus==40 && !i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_receivers] at hm
    exact List.mem_singleton.mp hm
  exact ((InteractionTriples.forall_iff _ (fun j=>j.bus=40→j.send=false→j=receiver)
    (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp) i hi hb hs

theorem other_tables {AP : AirP} (htables:AP.tables=ProcPriorProcessRepairedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=40→i.send=true := by
  have hall:((ProcPriorProcessRepairedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.bus != 40 || i.send)))=true := by decide +kernel
  intro t ht hn i hi hb
  rw [htables] at ht hi
  have hm:ProcPriorProcessRepairedFamily.tables[t]!∈ProcPriorProcessRepairedFamily.tables.drop 1 := by
    have he:(ProcPriorProcessRepairedFamily.tables.drop 1)[t-1]?=some (ProcPriorProcessRepairedFamily.tables[t]!) := by
      rw [List.getElem?_drop,show 1+(t-1)=t by omega,List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorProcessRepairedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have he:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hb] using he

theorem comparator_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:Local ProcPriorProcessRepairedFamily.fused.constraints tr t pub) :Cmp.CLocal (comparator tr) t pub := by
  change Local ProcPriorProcessRepairedFamily.raw.constraints tr t pub at hL
  intro r hr e he
  unfold comparator
  rw [←HorizontalTrace.expression_eval]
  exact hL r hr _ (List.mem_flatMap.mpr ⟨HorizontalTables.shifted comparatorOffset (Cmp.table 40),
    comparator_location,List.mem_map.mpr ⟨e,he,rfl⟩⟩)

theorem receiver_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    receiver.msgVal tr t r pub=((Cmp.interactions 40)[0]!).msgVal (comparator tr) t r pub := by
  simp only [receiver,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r comparatorOffset pub e

/-- Actual shared/fused comparator40 soundness for both original scheduler and
routed prior-memory/ID traffic. Ownership, receiver identity
and projected Local follow from the concrete family; only real public-bus
exclusion and natural operand bounds remain. -/
theorem sound {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorProcessRepairedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {t r : Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i : Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=40) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) {x y b : Fp} (hmsg:i.msgVal tr t r pub=[x,y,b])
    (hx:x.toNat<2^29) (hy:y.toNat<2^29) :
    (b=1 ∧ y.toNat≤x.toNat) ∨ (b=0 ∧ x.toNat<y.toNat) := by
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorProcessRepairedFamily.fused := by rw [htables];rfl
  obtain ⟨q,hq,j,hj,hjb,hjs,hmatch,_⟩:=send_matched hH ht0 (other_tables htables) hpub ht hr hi hb hs hm
  rw [htab] at hj
  have hej:=receiver_eq hj hjb hjs
  subst j
  rw [receiver_message,hmsg] at hmatch
  simp only [Cmp.interactions,List.getElem!_cons_zero,Interaction.msgVal,Cmp.msg,List.map_cons,List.map_nil,List.cons.injEq] at hmatch
  obtain ⟨ex,ey,eb,_⟩:=hmatch
  have hL:=local_of_holdsP hH ht0
  rw [htab] at hL
  have hc:=comparator_local hL
  have cx:cv (comparator tr) 0 q Cmp.colX=x.toNat := by rw [←ex];rfl
  have cy:cv (comparator tr) 0 q Cmp.colY=y.toNat := by rw [←ey];rfl
  have cb:(comparator tr).cell 0 q Cmp.colB=b := eb
  rcases Cmp.cmp_row hc hq (by rw [cx];exact hx) (by rw [cy];exact hy) with ⟨hb,ho⟩|⟨hb,ho⟩
  · left
    refine ⟨?_,by rw [←cx,←cy];exact ho⟩
    rw [←cb]
    rw [←Fp.ofNat_toNat ((comparator tr).cell 0 q Cmp.colB)]
    change Fp.ofNat (cv (comparator tr) 0 q Cmp.colB)=1
    rw [hb];rfl
  · right
    refine ⟨?_,by rw [←cx,←cy];exact ho⟩
    rw [←cb]
    rw [←Fp.ofNat_toNat ((comparator tr).cell 0 q Cmp.colB)]
    change Fp.ofNat (cv (comparator tr) 0 q Cmp.colB)=0
    rw [hb];rfl

theorem prior_ge {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorProcessRepairedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {t r : Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i : Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=40) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) {x y : Fp} (hmsg:i.msgVal tr t r pub=[x,y,1])
    (hx:x.toNat<2^29) (hy:y.toNat<2^29) :y.toNat≤x.toNat := by
  rcases sound hH htables hpub ht hr hi hb hs hm hmsg hx hy with h|h
  · exact h.2
  · have hn:(1:Fp)≠0 := by decide +kernel
    exact (hn h.1).elim
end ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedSound

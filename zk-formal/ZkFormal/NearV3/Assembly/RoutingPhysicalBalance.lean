import ZkFormal.NearV3.Assembly.RoutingPhysicalProviders
import ZkFormal.NearV3.Assembly.QueuePartition

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

private theorem filterMap_bool {α β : Type} (xs : List α) (p : α→Bool) (f : α→β) :
    xs.filterMap (fun x=>if p x then some (f x) else none)=(xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h,ih]

theorem physical_messages_active (tr : Trace Fp) (t : Nat) (sd : Bool) :
    physicalCounterMessages tr t sd=(physicalActiveRows tr t).map (fun r=>
      physicalBoundaryKey tr t r++[if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r]) := by
  unfold physicalCounterMessages physicalActiveRows
  simpa only [decide_eq_true_eq] using filterMap_bool (List.range (tr.height t))
    (fun r=>decide (tr.cell t r gBd=1))
    (fun r=>physicalBoundaryKey tr t r++[if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r])

theorem physical_ranks_active (tr : Trace Fp) (t : Nat) (key : Msg) :
    physicalRanksFor tr t key=
      ((physicalActiveRows tr t).filter (fun r=>physicalBoundaryKey tr t r==key)).map (physicalBoundaryRank tr t) := by
  unfold physicalRanksFor
  rw [filterMap_bool]
  simp only [physicalActiveRows,List.filter_filter]
  congr 2
  funext r
  simp [selectedBoundary,Bool.and_comm]

def providerCounterMessages (tr : Trace Fp) (t : Nat) (e : BndE) (sd : Bool) : List Msg :=
  (physicalRanksFor tr t e.rec4).map (fun u=>e.rec4++[if sd then u+1 else u])

theorem physical_group_messages (tr : Trace Fp) (t : Nat) (e : BndE) (sd : Bool) :
    ((physicalActiveRows tr t).filter (fun r=>physicalBoundaryKey tr t r==e.rec4)).map (fun r=>
      physicalBoundaryKey tr t r++[if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r])=
      providerCounterMessages tr t e sd := by
  rw [providerCounterMessages,physical_ranks_active,List.map_map]
  apply List.map_congr_left
  intro r hr
  have he : physicalBoundaryKey tr t r=e.rec4 := by simpa using (List.mem_filter.mp hr).2
  simp only [Function.comp_def,he]

theorem physical_provider_partition (tr : Trace Fp) (t : Nat) (es : List BndE)
    (hn : (es.map BndE.rec4).Nodup)
    (hc : ∀r∈physicalActiveRows tr t,physicalBoundaryKey tr t r∈es.map BndE.rec4)
    (sd : Bool) :
    (physicalCounterMessages tr t sd).Perm (es.flatMap (fun e=>providerCounterMessages tr t e sd)) := by
  have hp := provider_partition (physicalActiveRows tr t) es (physicalBoundaryKey tr t) BndE.rec4 hn hc
  have hm := hp.map (fun r=>physicalBoundaryKey tr t r++
    [if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r])
  rw [←physical_messages_active,List.map_flatMap] at hm
  have he : es.flatMap (fun e=>
      ((physicalActiveRows tr t).filter (fun r=>physicalBoundaryKey tr t r==e.rec4)).map (fun r=>
        physicalBoundaryKey tr t r++[if sd then physicalBoundaryRank tr t r+1 else physicalBoundaryRank tr t r]))=
      es.flatMap (fun e=>providerCounterMessages tr t e sd) := by
    unfold List.flatMap
    congr 1
    apply List.map_congr_left
    intro e _
    exact physical_group_messages tr t e sd
  simp only [Lean.Grind.beq_eq_decide_eq] at hm he
  exact hm.trans (List.Perm.of_eq he)

/-- Complete natural BND multiset balance, preserving all repeated requests.
Coverage is the explicit public-key ownership obligation; it is not inferred
from counter cancellation or hash injectivity. -/
theorem physical_counter_balance (tr : Trace Fp) (t : Nat) (es : List BndE)
    (hn : (es.map BndE.rec4).Nodup)
    (hc : ∀r∈physicalActiveRows tr t,physicalBoundaryKey tr t r∈es.map BndE.rec4)
    (hu : ∀e∈es,e.U=physicalBoundaryUsers tr t e.rec4) :
    (es.map (fun e=>e.rec4++[0])++physicalCounterMessages tr t true).Perm
      (physicalCounterMessages tr t false++es.map (fun e=>e.rec4++[e.U])) := by
  have hs := physical_provider_partition tr t es hn hc true
  have hr := physical_provider_partition tr t es hn hc false
  have he : es.flatMap (fun e=>[e.rec4++[0]]++providerCounterMessages tr t e true)=
      es.flatMap (fun e=>providerCounterMessages tr t e false++[e.rec4++[e.U]]) := by
    unfold List.flatMap
    congr 1
    apply List.map_congr_left
    intro e hem
    simpa only [providerCounterMessages,Bool.false_eq_true,ite_true,ite_false,List.singleton_append,hu e hem] using
      physical_counter_chain tr t e.rec4
  have hp := (Near.Render.perm_flatMap_append es (fun e=>[e.rec4++[0]])
    (fun e=>providerCounterMessages tr t e true)).symm.trans (List.Perm.of_eq he)
  have hp' := hp.trans (Near.Render.perm_flatMap_append es
    (fun e=>providerCounterMessages tr t e false) (fun e=>[e.rec4++[e.U]]))
  simp only [←List.map_eq_flatMap] at hp'
  exact (hs.append_left _).trans (hp'.trans (hr.symm.append_right _))

end ZkFormal.NearV3.Assembly.RoutingQCandidate

import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowMessages
import ZkFormal.NearV3.Assembly.QueuePartition
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly

private theorem filterMap_bool {α β : Type} (xs : List α) (p : α→Bool) (f : α→β) :
    xs.filterMap (fun x=>if p x then some (f x) else none)=(xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h,ih]

theorem window_messages_active (tr : Trace Fp) (t : Nat) (sd : Bool) :
    physicalWindowMessages tr t sd=(physicalWindowRows tr t).map (fun r=>
      physicalWindowKey tr t r++[if sd then physicalWindowRank tr t r+1 else physicalWindowRank tr t r]) := by
  unfold physicalWindowMessages physicalWindowRows
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rows ih => by_cases h : tr.cell t r UpsV3.rd=1 <;> simp [h,ih]

theorem window_ranks_active (tr : Trace Fp) (t : Nat) (key : Msg) :
    windowRanksFor tr t key=
      ((physicalWindowRows tr t).filter (fun r=>physicalWindowKey tr t r==key)).map (physicalWindowRank tr t) := by
  unfold windowRanksFor
  rw [filterMap_bool]
  simp only [physicalWindowRows,List.filter_filter]
  congr 2
  funext r
  simp [selectedWindow,Bool.and_comm]

def providerWindowMessages (tr : Trace Fp) (t : Nat) (e : Msg) (sd : Bool) : List Msg :=
  (windowRanksFor tr t e).map (fun u=>e++[if sd then u+1 else u])

theorem window_group_messages (tr : Trace Fp) (t : Nat) (e : Msg) (sd : Bool) :
    ((physicalWindowRows tr t).filter (fun r=>physicalWindowKey tr t r==e)).map (fun r=>
      physicalWindowKey tr t r++[if sd then physicalWindowRank tr t r+1 else physicalWindowRank tr t r])=
      providerWindowMessages tr t e sd := by
  rw [providerWindowMessages,window_ranks_active,List.map_map]
  apply List.map_congr_left
  intro r hr
  have he : physicalWindowKey tr t r=e := by simpa using (List.mem_filter.mp hr).2
  simp only [Function.comp_def,he]

theorem window_provider_partition (tr : Trace Fp) (t : Nat) (es : List Msg)
    (hn : (es).Nodup)
    (hc : ∀r∈physicalWindowRows tr t,physicalWindowKey tr t r∈es)
    (sd : Bool) :
    (physicalWindowMessages tr t sd).Perm (es.flatMap (fun e=>providerWindowMessages tr t e sd)) := by
  have hp := provider_partition (physicalWindowRows tr t) es (physicalWindowKey tr t) id (by simpa using hn) (by simpa using hc)
  have hm := hp.map (fun r=>physicalWindowKey tr t r++
    [if sd then physicalWindowRank tr t r+1 else physicalWindowRank tr t r])
  rw [←window_messages_active,List.map_flatMap] at hm
  have he : es.flatMap (fun e=>
      ((physicalWindowRows tr t).filter (fun r=>physicalWindowKey tr t r==e)).map (fun r=>
        physicalWindowKey tr t r++[if sd then physicalWindowRank tr t r+1 else physicalWindowRank tr t r]))=
      es.flatMap (fun e=>providerWindowMessages tr t e sd) := by
    unfold List.flatMap
    congr 1
    apply List.map_congr_left
    intro e _
    exact window_group_messages tr t e sd
  simp only [Lean.Grind.beq_eq_decide_eq] at hm he
  exact hm.trans (List.Perm.of_eq he)

/-- Complete natural UPB multiset balance, preserving all repeated requests.
Coverage is the explicit provider-key ownership obligation; it is not inferred
from counter cancellation or hash injectivity. -/
theorem window_counter_balance (tr : Trace Fp) (t : Nat) (es : List Msg)
    (hn : (es).Nodup)
    (hc : ∀r∈physicalWindowRows tr t,physicalWindowKey tr t r∈es)
    :
    (es.map (fun e=>e++[0])++physicalWindowMessages tr t true).Perm
      (physicalWindowMessages tr t false++es.map (fun e=>e++[physicalWindowUsers tr t e])) := by
  have hs := window_provider_partition tr t es hn hc true
  have hr := window_provider_partition tr t es hn hc false
  have he : es.flatMap (fun e=>[e++[0]]++providerWindowMessages tr t e true)=
      es.flatMap (fun e=>providerWindowMessages tr t e false++[e++[physicalWindowUsers tr t e]]) := by
    unfold List.flatMap
    congr 1
    apply List.map_congr_left
    intro e hem
    simpa only [providerWindowMessages,Bool.false_eq_true,ite_true,ite_false,List.singleton_append] using
      window_counter_chain tr t e
  have hp := (Near.Render.perm_flatMap_append es (fun e=>[e++[0]])
    (fun e=>providerWindowMessages tr t e true)).symm.trans (List.Perm.of_eq he)
  have hp' := hp.trans (Near.Render.perm_flatMap_append es
    (fun e=>providerWindowMessages tr t e false) (fun e=>[e++[physicalWindowUsers tr t e]]))
  simp only [←List.map_eq_flatMap] at hp'
  exact (hs.append_left _).trans (hp'.trans (hr.symm.append_right _))


/-- Field-level UPB conservation for the actual patched trace, with provider
zero/terminal counters computed from the exact physical read inventory. -/
theorem window_counter_field_balance (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (es : List Msg) (hn : es.Nodup)
    (hc : ∀r∈physicalWindowRows tr t,physicalWindowKey tr t r∈es) (msg : List Fp) :
    ((es.map (fun e=>e++[0])).map Msg.toFp).count msg+
      tableBusCount Render.UpsRelay.compactTable.interactions
        (patchWindowCounters tr t (physicalWindowRank tr t)) t pub B_UPB true msg=
    tableBusCount Render.UpsRelay.compactTable.interactions
        (patchWindowCounters tr t (physicalWindowRank tr t)) t pub B_UPB false msg+
      ((es.map (fun e=>e++[physicalWindowUsers tr t e])).map Msg.toFp).count msg := by
  rw [patched_window_count,patched_window_count]
  have h:=((window_counter_balance tr t es hn hc).map Msg.toFp).count_eq msg
  simpa only [List.map_append,List.count_append] using h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

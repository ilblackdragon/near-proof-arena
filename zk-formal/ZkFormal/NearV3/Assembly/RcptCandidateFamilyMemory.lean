import ZkFormal.NearV3.Assembly.RcptCandidateMemoryProviders
import ZkFormal.NearV3.Candidates.GatedMemoryAdmission
import ZkFormal.NearV3.Candidates.HorizontalProjection

namespace ZkFormal.NearV3.Assembly.ReceiptFamilyMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates Candidates.HorizontalTables Candidates.HorizontalTraffic

/-- Only this bus and direction contribute to account-memory providers. -/
def memSend (i : Interaction) : Bool := decide (i.bus=B_MEM ∧ i.send=true)

theorem count_filter (is : List Interaction) (tr : Trace Fp) (t : Nat)
    (pub : List Fp) (m : List Fp) :
    tableBusCount (is.filter memSend) tr t pub B_MEM true m =
      tableBusCount is tr t pub B_MEM true m := by
  rw [table_sum,table_sum]
  congr 1
  apply List.map_congr_left
  intro r _
  unfold rowCount
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases hi : i.bus=B_MEM ∧ i.send=true
    · simp [memSend,hi,ih]
    · have hn : ¬(i.bus=B_MEM ∧ i.send=true ∧ i.msgVal tr t r pub=m) := fun h=>hi ⟨h.1,h.2.1⟩
      simp [memSend,hi,hn,ih]

def receiptOffset : Nat := ((GatedMemoryFusion.selected.take 13).map (·.width)).sum

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
/-- Concrete fusion inventory: no other fused component sends on MEM. -/
theorem fused_inventory :
    (fuse GatedMemoryFusion.selected).interactions.filter memSend =
      (shifted receiptOffset ReceiptCandidateRouting.candidateTable).interactions.filter memSend := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
/-- The remaining physical tables have one provider: account opens at table 6. -/
theorem rest_inventory :
    HorizontalAccounts.rest.map (fun T=>T.interactions.filter memSend) =
      [[],[],[],[],[],AcctV3.interactions.filter memSend,[],[],[],[],[]] := by
  decide +kernel

def counts (tr : Trace Fp) (pub : List Fp) (m : List Fp) : List (List Interaction) → Nat → Nat
  | [], _ => 0
  | is::iss,t => tableBusCount is tr t pub B_MEM true m + counts tr pub m iss (t+1)

theorem count_nil (tr : Trace Fp) (t : Nat) (pub m : List Fp) :
    tableBusCount [] tr t pub B_MEM true m=0 := by
  rw [table_sum]
  simp only [rowCount,List.map_nil,List.sum_nil]
  have hz : ∀ xs : List Nat,(xs.map (fun _=>0)).sum=0 := by
    intro xs; induction xs <;> simp_all
  exact hz _

theorem go_counts (ts : List Air.Table) (tr : Trace Fp) (t : Nat) (pub m : List Fp) :
    busCount.go tr pub B_MEM true m ts t =
      counts tr pub m (ts.map (fun T=>T.interactions.filter memSend)) t := by
  induction ts generalizing t with
  | nil => rfl
  | cons T ts ih => simp only [busCount.go,counts,List.map_cons,count_filter,ih]

/-- Exact global sender inventory on the actual fused candidate family. -/
theorem global_senders (tr : Trace Fp) (pub m : List Fp) :
    busCount GatedMemoryAdmission.air tr pub B_MEM true m =
      tableBusCount ReceiptCandidateRouting.candidateTable.interactions
        (HorizontalTrace.project receiptOffset tr) 0 pub B_MEM true m +
      tableBusCount AcctV3.interactions tr 6 pub B_MEM true m := by
  change tableBusCount (fuse GatedMemoryFusion.selected).interactions tr 0 pub B_MEM true m +
    busCount.go tr pub B_MEM true m HorizontalAccounts.rest 1 = _
  rw [←count_filter (fuse GatedMemoryFusion.selected).interactions, fused_inventory,
    count_filter, HorizontalProjection.shifted_count, go_counts, rest_inventory]
  simp only [counts,count_nil,count_filter,Nat.zero_add,Nat.add_zero]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem receipt_location :
    shifted receiptOffset ReceiptCandidateRouting.candidateTable∈layout 0 GatedMemoryFusion.selected := by
  exact List.mem_of_getElem? (show (layout 0 GatedMemoryFusion.selected)[13]?=
    some (shifted receiptOffset ReceiptCandidateRouting.candidateTable) from rfl)

theorem count_zero_of_no_message (is : List Interaction) (tr : Trace Fp) (t : Nat)
    (pub m : List Fp) (hn : ∀ r i, i∈is → i.msgVal tr t r pub≠m) :
    tableBusCount is tr t pub B_MEM true m=0 := by
  rw [table_sum]
  have hr : ∀ r, rowCount is tr t r pub B_MEM true m=0 := by
    intro r
    unfold rowCount
    induction is with
    | nil => rfl
    | cons i is ih =>
      have hi := hn r i (by simp)
      have ht := ih (by intro r i hi; exact hn r i (by simp [hi]))
      simp [hi,ht]
  simp only [hr]
  have hz : ∀ xs : List Nat,(xs.map (fun _=>0)).sum=0 := by
    intro xs; induction xs <;> simp_all
  exact hz _

theorem positive_count_message (is : List Interaction) (tr : Trace Fp) (t : Nat)
    (pub m : List Fp) (hp : 0<tableBusCount is tr t pub B_MEM true m) :
    ∃ r i, i∈is ∧ i.msgVal tr t r pub=m := by
  classical
  apply Classical.byContradiction
  intro hn
  have hz := count_zero_of_no_message is tr t pub m (by
    intro r i hi hm; exact hn ⟨r,i,hi,hm⟩)
  omega

/-- Every positively counted physical account opening has version zero. -/
theorem account_provider_version (tr : Trace Fp) (t : Nat) (pub m : List Fp)
    (hp : 0<tableBusCount AcctV3.interactions tr t pub B_MEM true m) :
    (m.getD 1 0).toNat=0 := by
  rw [←count_filter] at hp
  obtain ⟨r,i,hi,hm⟩ := positive_count_message _ _ _ _ _ hp
  have hh : AcctV3.interactions.filter memSend=
    [Dsl.send B_MEM (Dsl.c Acct.act)
      [Dsl.c Acct.kk,Dsl.k 0,Dsl.c Acct.i,Dsl.c Acct.amt,Dsl.c Acct.lk,Dsl.c Acct.st]] := rfl
  rw [hh,List.mem_singleton] at hi
  have hv : (i.msgVal tr t r pub).getD 1 0=0 := by rw [hi]; rfl
  rw [hm] at hv
  rw [hv]; rfl

/-- The actual family holds predicate supplies local legality of its fused head. -/
theorem fused_local {tr : Trace Fp} {pub : List Fp}
    (h : Holds GatedMemoryAdmission.air pub tr) :
    TableLocal (fuse GatedMemoryFusion.selected) tr 0 pub := by
  have hb := h.logBound 0 (by decide)
  exact ⟨hb.1,hb.2,h.constr 0 (by decide),h.bits 0 (by decide)⟩

/-- Global balance and the concrete provider inventory bound all positive fused
MEM receives. No age arithmetic or pre-assumed memory ownership is used. -/
theorem fused_receive_version {tr : Trace Fp} {pub : List Fp}
    (h : Holds GatedMemoryAdmission.air pub tr) (m : List Fp)
    (hp : 0<tableBusCount (fuse GatedMemoryFusion.selected).interactions tr 0 pub B_MEM false m) :
    (m.getD 1 0).toNat≤2^22 := by
  have hglobal : 0<busCount GatedMemoryAdmission.air tr pub B_MEM false m := by
    change 0<tableBusCount (fuse GatedMemoryFusion.selected).interactions tr 0 pub B_MEM false m + _
    omega
  rw [←h.balance B_MEM m,global_senders] at hglobal
  by_cases ha : 0<tableBusCount AcctV3.interactions tr 6 pub B_MEM true m
  · rw [account_provider_version tr 6 pub m ha];omega
  have hr : 0<tableBusCount ReceiptCandidateRouting.candidateTable.interactions
      (HorizontalTrace.project receiptOffset tr) 0 pub B_MEM true m := by omega
  have hl := HorizontalTrace.project_local receipt_location
    (show ReceiptCandidateRouting.candidateTable.maxLog=22 from rfl) (fused_local h)
  obtain ⟨bs,e,hc,ht⟩ := ReceiptCandidateProof.repaired_extract_traffic hl
  rw [(ht B_MEM m).1] at hr
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (List.count_pos_iff.mp hr)
  have hb := ReceiptCandidateProof.receipt_memory_provider_bound
    (ReceiptCandidateProof.repaired_local_base hl) hc hv
  rw [←he]
  have heq : (v.toFp.getD 1 0).toNat=(v.getD 1 0)%P := by
    cases v with
    | nil => rfl
    | cons a vs => cases vs with
      | nil => rfl
      | cons b tail => exact Fp.toNat_ofNat b
  rw [heq,Nat.mod_eq_of_lt (by unfold P;omega)]
  exact hb

end ZkFormal.NearV3.Assembly.ReceiptFamilyMemory

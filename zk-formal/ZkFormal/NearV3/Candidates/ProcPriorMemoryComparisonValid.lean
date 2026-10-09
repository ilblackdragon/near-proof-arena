import ZkFormal.NearV3.Candidates.ProcPriorMemoryStrictOrder
import ZkFormal.NearV3.Candidates.ProcPriorComparisonBudget
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonValid
open ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched.Complete
open ProcPriorNativeMemory ProcPriorComparisonRequests ProcPriorMemoryStrictOrder

theorem bounds (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (a : Tagged) (ha:a∈allRows bs) : address a<2^29 ∧ a.row.event.stamp+1<2^29 := by
  obtain ⟨b,hb,hab⟩:=List.mem_flatMap.mp ha
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
  have hir:i<bs.length:=(List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ht,hr⟩:=tagged_member b a hab
  have hlink:=ProcPriorIndexed.row_bound _ _ (hn b hb) a.row hr
  have hτ:=ho i b hi
  have hem:a.row.event∈ProcPriorEvents.events b.pub.ids b.old.links:=by
    have hm:=ProcPriorRows.rowsFrom_events ⟨none,ProcPriorCarry.zero⟩
      (ProcPriorEvents.events b.pub.ids b.old.links)
    change (ProcPriorRows.rows b.pub.ids b.old.links).map (·.event)=_ at hm
    rw [←hm]
    exact List.mem_map.mpr ⟨a.row,hr,rfl⟩
  have hstamp:=(ProcPriorEvents.event_bounds _ _ _ hem).2.1
  have hcharge:=ProcRawNativeLocal.length_le bs b hb
  unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length at hcharge
  unfold address
  omega

theorem pair_ok (a b : Tagged) (ha:address a<2^29 ∧ a.row.event.stamp+1<2^29)
    (hb:address b<2^29 ∧ b.row.event.stamp+1<2^29) (ho:Ordered a b)
    (q : Request) (hq:q∈memoryPair a b) : CmpOk q := by
  simp only [memoryPair,List.mem_append,List.mem_singleton] at hq
  rcases hq with rfl|hq
  · unfold CmpOk Ordered at *
    dsimp only
    exact ⟨hb.1,ha.1,by rw [ite_eq_left (by omega)]⟩
  · split at hq
    next he=>
      simp only [List.mem_singleton] at hq
      subst q
      unfold CmpOk Ordered at *
      dsimp only
      exact ⟨by omega,ha.2,by rw [ite_eq_left (by omega)]⟩
    next=>simp at hq

theorem adjacent_ok {α : Type} (R : α→α→Prop) (B : α→Prop)
    (f : α→α→List Request) (xs : List α) (hr:xs.Pairwise R) (hb:∀a∈xs,B a)
    (hf:∀a b,B a→B b→R a b→∀q∈f a b,CmpOk q) : ∀q∈adjacent f xs,CmpOk q := by
  intro q hq
  obtain ⟨p,hp,hqp⟩:=List.mem_flatMap.mp hq
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hp
  obtain ⟨hil,he⟩:=List.getElem?_eq_some_iff.mp hi
  have h1:i<xs.length:=by
    rw [List.length_zip] at hil
    exact (Nat.lt_min.mp hil).1
  have h2:i+1<xs.length:=by simp only [List.length_zip,List.length_drop] at hil;omega
  rw [List.getElem_zip,List.getElem_drop] at he
  subst p
  have ho:=List.pairwise_iff_getElem.mp hr i (1+i) h1 (by omega) (by omega)
  exact hf _ _ (hb _ (List.getElem_mem h1)) (hb _ (List.getElem_mem (by omega))) ho q hqp

theorem native (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    ∀q∈memory bs,CmpOk q := by
  exact adjacent_ok Ordered (fun a=>address a<2^29 ∧ a.row.event.stamp+1<2^29) memoryPair
    (allRows bs) (ProcPriorMemoryStrictOrder.native bs hn ho) (bounds bs hn hlen ho hraw) pair_ok
end ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonValid

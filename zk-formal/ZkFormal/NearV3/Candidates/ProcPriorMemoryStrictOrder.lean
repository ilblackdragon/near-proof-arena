import ZkFormal.NearV3.Candidates.ProcPriorEventStrictOrder
import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryComplete
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryStrictOrder
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorNativeMemory

def Ordered (a b : Tagged) :=address a<address b ∨ address a=address b ∧ a.row.event.stamp<b.row.event.stamp

theorem block (b : NativeBlock) : (tagged b).Pairwise Ordered := by
  have hm:=ProcPriorRows.rowsFrom_events ⟨none,ProcPriorCarry.zero⟩
    (ProcPriorEvents.events b.pub.ids b.old.links)
  change (ProcPriorRows.rows b.pub.ids b.old.links).map (·.event)=_ at hm
  have hs:=ProcPriorEventStrictOrder.sorted_strict b.pub.ids b.old.links
  rw [←hm,List.pairwise_map] at hs
  apply List.Pairwise.map _ ?_ hs
  intro a c hac
  simp only [Ordered,address]
  omega

theorem blocks (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (ho:bs.Pairwise (fun a b=>a.run.tau<b.run.tau)) : (allRows bs).Pairwise Ordered := by
  induction bs with
  | nil=>simp [allRows]
  | cons b bs ih=>
    obtain ⟨hh,ht⟩:=List.pairwise_cons.mp ho
    change (tagged b++allRows bs).Pairwise Ordered
    apply List.pairwise_append.mpr
    refine ⟨block b,ih (fun b hb=>hn b (by simp [hb])) ht,?_⟩
    intro a ha c hc
    obtain ⟨d,hd,hcd⟩:=List.mem_flatMap.mp hc
    obtain ⟨hat,har⟩:=tagged_member b a ha
    obtain ⟨hct,hcr⟩:=tagged_member d c hcd
    have hal:=ProcPriorIndexed.row_bound _ _ (hn b (by simp)) a.row har
    have hcl:=ProcPriorIndexed.row_bound _ _ (hn d (by simp [hd])) c.row hcr
    have htd:=hh d hd
    left
    unfold address
    omega

theorem native (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i) :
    (allRows bs).Pairwise Ordered := by
  apply blocks bs hn
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  rw [ho i _ (List.getElem?_eq_getElem hi),ho j _ (List.getElem?_eq_getElem hj)]
  exact hij
end ZkFormal.NearV3.Candidates.ProcPriorMemoryStrictOrder

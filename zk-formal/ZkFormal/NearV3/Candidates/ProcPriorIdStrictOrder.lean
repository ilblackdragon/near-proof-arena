import ZkFormal.NearV3.Candidates.ProcPriorIdEventOrder
import ZkFormal.NearV3.Candidates.ProcIdNativeLocal
namespace ZkFormal.NearV3.Candidates.ProcPriorIdStrictOrder
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcIdTaggedCells

def EventOrdered (a b : ProcPriorIds.Event) := a.key≤b.key ∧
  (a.key=b.key→a.isPublic=true→b.isPublic=true→a.ordinal<b.ordinal)
def Ordered (a b : Tagged) :=a.1<b.1 ∨ a.1=b.1 ∧ EventOrdered a.2.event b.2.event

theorem event_order (ids : List Nat) (rs : List NearSpec.Bandwidth.LinkAllowance) :
    (ProcPriorIds.events ids rs).Pairwise EventOrdered := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hs:=List.pairwise_iff_getElem.mp (ProcPriorIds.events_sorted ids rs) i j hi hj hij
  simp only [ProcPriorIds.precedes,decide_eq_true_eq] at hs
  refine ⟨by omega,?_⟩
  exact ProcPriorIdEventOrder.public_strict ids rs i j hi hj hij

theorem block (b : NativeBlock) : (ProcIdTaggedRows.block b.pub.ids b).Pairwise Ordered := by
  have hm:=ProcPriorIdRows.rowsFrom_events ⟨none,ProcPriorIdCarry.zero⟩
    (ProcPriorIds.events b.pub.ids b.old.links)
  change (ProcPriorIdRows.rows b.pub.ids b.old.links).map (·.event)=_ at hm
  have hs:=event_order b.pub.ids b.old.links
  rw [←hm,List.pairwise_map] at hs
  apply List.Pairwise.map _ ?_ hs
  intro a c hac
  exact Or.inr ⟨rfl,hac⟩

theorem blocks (bs : List NativeBlock)
    (ho:bs.Pairwise (fun a b=>a.run.tau<b.run.tau)) :
    (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs).Pairwise Ordered := by
  induction bs with
  | nil=>simp [ProcIdTaggedRows.rows]
  | cons b bs ih=>
    obtain ⟨hh,ht⟩:=List.pairwise_cons.mp ho
    change (ProcIdTaggedRows.block b.pub.ids b++ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs).Pairwise Ordered
    apply List.pairwise_append.mpr
    refine ⟨block b,ih ht,?_⟩
    intro a ha c hc
    obtain ⟨ar,har,rfl⟩:=List.mem_map.mp ha
    obtain ⟨d,hd,cr,hcr,rfl⟩:=ProcIdTaggedRows.mem_origin _ bs c hc
    exact Or.inl (hh d hd)

theorem native (bs : List NativeBlock)
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i) :
    (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs).Pairwise Ordered := by
  apply blocks bs
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  rw [ho i _ (List.getElem?_eq_getElem hi),ho j _ (List.getElem?_eq_getElem hj)]
  exact hij
end ZkFormal.NearV3.Candidates.ProcPriorIdStrictOrder

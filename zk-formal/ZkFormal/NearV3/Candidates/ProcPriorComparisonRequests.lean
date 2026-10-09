import ZkFormal.NearV3.Candidates.ProcIdNativeLocal
import ZkFormal.NearV3.Candidates.ProcPriorOverlayBudget
import ZkFormal.NearV3.Candidates.CmpHeight
namespace ZkFormal.NearV3.Candidates.ProcPriorComparisonRequests
open ZkFormal.NearV3.Assembly.CodecDigest
abbrev Request := Nat×Nat×Nat

def memoryPair (a b : ProcPriorNativeMemory.Tagged) : List Request :=
  [(ProcPriorNativeMemory.address b,ProcPriorNativeMemory.address a,1)]++
    if ProcPriorNativeMemory.address a=ProcPriorNativeMemory.address b ∧ !b.row.event.query then
      [(b.row.event.stamp,a.row.event.stamp+1,1)] else []

def idPair (a b : ProcIdTaggedCells.Tagged) : List Request :=
  [(ProcIdTaggedCells.top b,ProcIdTaggedCells.top a,1)]++
  if a.1=b.1 then
    (if ProcPriorIdCells.sameTop a.2 (some b.2) then
      [(ProcPriorIdLimbs.mid b.2.event.key,ProcPriorIdLimbs.mid a.2.event.key,1)] else [])++
    (if ProcPriorIdCells.gateMid a.2 (some b.2) then
      [(ProcPriorIdLimbs.lo b.2.event.key,ProcPriorIdLimbs.lo a.2.event.key,1)] else [])++
    (if ProcPriorIdCells.gateAll a.2 (some b.2) && a.2.event.isPublic && b.2.event.isPublic then
      [(b.2.event.ordinal,a.2.event.ordinal+1,1)] else [])
  else []

def adjacent {α : Type} (f : α→α→List Request) (xs : List α) : List Request :=
  (xs.zip (xs.drop 1)).flatMap (fun (a,b)=>f a b)

def memory (bs : List NativeBlock) :=adjacent memoryPair (ProcPriorNativeMemory.allRows bs)
def ids (bs : List NativeBlock) :=adjacent idPair (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)
def requests (bs : List NativeBlock) :=memory bs++ids bs

theorem memory_pair_length (a b : ProcPriorNativeMemory.Tagged) : (memoryPair a b).length≤2 := by
  unfold memoryPair
  split <;> simp

theorem id_pair_length (a b : ProcIdTaggedCells.Tagged) : (idPair a b).length≤4 := by
  unfold idPair
  split
  · repeat' split <;> simp
  · simp

theorem flat_bound {α : Type} (xs : List α) (f : α→List Request) (n : Nat)
    (h:∀x∈xs,(f x).length≤n) : (xs.flatMap f).length≤n*xs.length := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem adjacent_length {α : Type} (xs : List α) (f : α→α→List Request) (n : Nat)
    (h:∀a b,(f a b).length≤n) : (adjacent f xs).length≤n*xs.length := by
  have hh:=flat_bound (xs.zip (xs.drop 1)) (fun (a,b)=>f a b) n (fun p _=>h p.1 p.2)
  have hl:(xs.zip (xs.drop 1)).length≤xs.length:=by simp [List.length_zip]
  exact Nat.le_trans hh (Nat.mul_le_mul_left n hl)

theorem length_bound (bs : List NativeBlock) :
    (requests bs).length≤2*(ProcPriorNativeMemory.allRows bs).length+
      4*(ProcPriorOverlayBudget.idRows bs).length := by
  have hm:=adjacent_length (ProcPriorNativeMemory.allRows bs) memoryPair 2 memory_pair_length
  have hi:=adjacent_length (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs) idPair 4 id_pair_length
  have he:(ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs).length=(ProcPriorOverlayBudget.idRows bs).length:=by
    simp [ProcIdTaggedRows.rows,ProcIdTaggedRows.block,ProcPriorOverlayBudget.idRows,List.length_flatMap]
  rw [he] at hi
  simp only [requests,List.length_append]
  exact Nat.add_le_add hm hi
end ZkFormal.NearV3.Candidates.ProcPriorComparisonRequests

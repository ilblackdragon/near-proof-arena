import ZkFormal.NearV3.Candidates.ProcPriorRecordSemantics
import ZkFormal.NearV3.Candidates.ProcPriorIdLocal
import ZkFormal.NearV3.Candidates.ProcPriorRawLocal
import ZkFormal.NearV3.Candidates.ProcPriorDecodedLocal
namespace ZkFormal.NearV3.Candidates.ProcPriorFourStageBudget
open NearSpec NearSpec.Bandwidth ProcPriorBudget

def joinRows (xs : List Input) : Nat:=
  (xs.map fun x=>1+(ProcPriorRecordRows.rows x.state.links).length).sum

theorem joinRows_exact (xs : List Input) : joinRows xs=xs.length+9*records xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [joinRows,List.map_cons,List.sum_cons,ProcPriorRecordRows.rows_length] at ih ⊢
    simp only [records,List.map_cons,List.sum_cons,List.length_cons]
    change (xs.map fun x=>1+9*x.state.links.length).sum=xs.length+9*records xs at ih
    unfold records at ih
    omega

/-- Includes one trailing padding row for each of the four vertical stages.
The source-byte premise is still explicit until the accepted-witness allocator
binds exactly this input inventory, including virtual absent-state headers. -/
theorem capacity (xs : List Input) (h:∀x∈xs,Valid x)
    (hk:xs.length≤33) (hb:byteRows xs≤2000000) :
    byteRows xs+writeRows xs+idRows xs+joinRows xs+4≤3137313 ∧
    byteRows xs+writeRows xs+idRows xs+joinRows xs+4<2^22 := by
  have hc:=original_charge xs h
  have hw:=write_bound xs h
  have hi:=id_bound xs h
  rw [joinRows_exact]
  omega

end ZkFormal.NearV3.Candidates.ProcPriorFourStageBudget

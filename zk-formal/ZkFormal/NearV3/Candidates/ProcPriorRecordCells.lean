import ZkFormal.NearV3.Candidates.ProcPriorRecordLimbs
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordCells
open ZkFormal.Algebra NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler
open ProcPriorRecordRows ProcPriorCells

def cell (ids : List Nat) (tau : Nat) (r : Row) : Nat→Fp:=
  let sf:=indexOf ids r.source.sender
  let rf:=indexOf ids r.source.receiver
  let v:=value r
  let h:=ProcPriorIdLimbs.mid v+ProcPriorIdLimbs.hi v
  fun c=>match c with
  | 0=>1
  | 1=>Fp.ofNat tau
  | 2=>Fp.ofNat r.index
  | 3=>Fp.ofNat ids.length
  | 4=>bit (decide (r.word=0))
  | 5=>bit (decide (r.word=1))
  | 6=>bit (decide (r.word=2))
  | 7=>bit (decide (r.limb=0))
  | 8=>bit (decide (r.limb=1))
  | 9=>bit (decide (r.limb=2))
  | 10=>Fp.ofNat (ProcPriorRecordLimbs.digit v (3*r.limb))
  | 11=>Fp.ofNat (ProcPriorRecordLimbs.digit v (3*r.limb+1))
  | 12=>if r.limb=2 then 0 else Fp.ofNat (ProcPriorRecordLimbs.digit v (3*r.limb+2))
  | 13=>Fp.ofNat (ProcPriorIdLimbs.lo v)
  | 14=>Fp.ofNat (ProcPriorIdLimbs.mid v)
  | 15=>Fp.ofNat (ProcPriorIdLimbs.hi v)
  | 16=>bit sf.isSome
  | 17=>Fp.ofNat (sf.getD 0)
  | 18=>bit rf.isSome
  | 19=>Fp.ofNat (rf.getD 0)
  | 20=>bit (decide (h≠0))
  | 21=>(Fp.ofNat h)⁻¹
  | 22=>bit (decide (r.word=2) && decide (r.limb=2) && sf.isSome && rf.isSome)
  | _=>0

def header (ids : List Nat) (tau : Nat) : Nat→Fp
  | 0=>1
  | 1=>Fp.ofNat tau
  | 3=>Fp.ofNat ids.length
  | _=>0

def block (ids : List Nat) (tau : Nat) (rs : List LinkAllowance) : List (Nat→Fp):=
  header ids tau::(rows rs).map (cell ids tau)

theorem block_length (ids : List Nat) (tau : Nat) (rs : List LinkAllowance) :
    (block ids tau rs).length=1+9*rs.length := by
  simp [block,rows_length,Nat.add_comm]

theorem boolean_cells (ids : List Nat) (tau : Nat) (r : Row) (c : Nat)
    (hc:c∈[0,4,5,6,7,8,9,16,18,20,22]) : cell ids tau r c=0 ∨ cell ids tau r c=1 := by
  have bit_cases (b : Bool) : bit b=0 ∨ bit b=1 := by cases b <;> simp [bit]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inr rfl
  all_goals exact bit_cases _

theorem allowance_summary (ids : List Nat) (tau j : Nat) (r : LinkAllowance) :
    cell ids tau ⟨j,2,2,r⟩ 13=Fp.ofNat (ProcPriorSummary.low r.allowance) ∧
    cell ids tau ⟨j,2,2,r⟩ 20=bit (ProcPriorSummary.big r.allowance) := by
  simp only [cell,value,ProcPriorSummary.low,ProcPriorIdLimbs.lo,
    ProcPriorRecordLimbs.big_exact]
  exact ⟨rfl,rfl⟩

end ZkFormal.NearV3.Candidates.ProcPriorRecordCells

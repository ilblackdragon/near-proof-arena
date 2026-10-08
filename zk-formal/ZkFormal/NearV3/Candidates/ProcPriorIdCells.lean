import ZkFormal.NearV3.Candidates.ProcPriorIdNext
import ZkFormal.NearV3.Candidates.ProcPriorIdLimbs
import ZkFormal.NearV3.Candidates.ProcPriorIdTable
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorIdCells
open ZkFormal.Algebra ProcPriorIdRows ProcPriorCells

def eqLimb (f : Nat→Nat) (a : Row) (b : Option Row) : Bool :=
  match b with | none=>false | some b=>decide (f a.event.key=f b.event.key)
def invLimb (f : Nat→Nat) (a : Row) (b : Option Row) : Fp :=
  match b with | none=>0 | some b=>(Fp.ofNat (f b.event.key)-Fp.ofNat (f a.event.key))⁻¹

def sameTop (a : Row) (b : Option Row) : Bool:=eqLimb ProcPriorIdLimbs.hi a b
def sameMid (a : Row) (b : Option Row) : Bool:=eqLimb ProcPriorIdLimbs.mid a b
def sameLo (a : Row) (b : Option Row) : Bool:=eqLimb ProcPriorIdLimbs.lo a b
def gateMid (a : Row) (b : Option Row) : Bool:=sameTop a b && sameMid a b
def gateAll (a : Row) (b : Option Row) : Bool:=gateMid a b && sameLo a b
def nextPublic (b : Option Row) : Bool:=b.any (·.event.isPublic)
def take (a : Row) : Bool:=a.event.isPublic && !a.before.isSome

def cells (a : Row) (b : Option Row) (tau : Nat) : Nat→Fp
  | 0=>1
  | 1=>Fp.ofNat tau
  | 2=>Fp.ofNat (ProcPriorIdLimbs.lo a.event.key)
  | 3=>Fp.ofNat (ProcPriorIdLimbs.mid a.event.key)
  | 4=>Fp.ofNat (ProcPriorIdLimbs.hi a.event.key)
  | 5=>Fp.ofNat a.event.ordinal
  | 6=>bit a.event.isPublic
  | 7=>bit a.before.isSome
  | 8=>Fp.ofNat (a.before.getD 0)
  | 9=>bit (take a)
  | 10=>bit (sameTop a b)
  | 11=>bit (sameMid a b)
  | 12=>bit (sameLo a b)
  | 13=>invLimb ProcPriorIdLimbs.hi a b
  | 14=>invLimb ProcPriorIdLimbs.mid a b
  | 15=>invLimb ProcPriorIdLimbs.lo a b
  | 16=>bit (sameTop a b)
  | 17=>bit (gateMid a b)
  | 18=>bit (gateAll a b)
  | 19=>bit (gateAll a b && a.event.isPublic && nextPublic b)
  | _=>0

theorem bit_bool (b : Bool) : bit b=0 ∨ bit b=1 := by cases b <;> simp [bit]

theorem boolean_cells (a : Row) (b : Option Row) (tau c : Nat)
    (hc:c∈[0,6,7,9,10,11,12,16,17,18,19]) :
    cells a b tau c=0 ∨ cells a b tau c=1 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inr rfl
  all_goals exact bit_bool _

theorem gateAll_key (a b : Row) : gateAll a (some b)=decide (a.event.key=b.event.key) := by
  simp only [gateAll,gateMid,sameTop,sameMid,sameLo,eqLimb]
  by_cases h:a.event.key=b.event.key
  · simp [h]
  · have hn:¬(ProcPriorIdLimbs.hi a.event.key=ProcPriorIdLimbs.hi b.event.key ∧
        ProcPriorIdLimbs.mid a.event.key=ProcPriorIdLimbs.mid b.event.key ∧
        ProcPriorIdLimbs.lo a.event.key=ProcPriorIdLimbs.lo b.event.key) := by
      intro hh
      exact h (ProcPriorIdLimbs.injective _ _ hh.2.2 hh.2.1 hh.1)
    simp only [h,decide_false,Bool.and_eq_false_imp]
    grind

end ZkFormal.NearV3.Candidates.ProcPriorIdCells

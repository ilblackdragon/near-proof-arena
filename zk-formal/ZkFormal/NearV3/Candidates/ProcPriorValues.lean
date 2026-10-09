import ZkFormal.NearV3.Candidates.ProcPriorEventOrder
namespace ZkFormal.NearV3.Candidates.ProcPriorValues
open NearSpec NearSpec.Bandwidth ProcPriorLookup ProcPriorWinner ProcPriorSummary ProcPriorEvents

def pair (r : LinkAllowance) : Nat×Bool := (low r.allowance,big r.allowance)
def value (e : Event) : Nat×Bool := (e.lo,e.hi)

def writesFrom (ids : List Nat) (rs : List LinkAllowance) (start : Nat) : List Event :=
  (rs.zipIdx start).filterMap fun (r,j)=>(target ids r).map fun l=>⟨l,j,false,low r.allowance,big r.allowance⟩

theorem values_from (ids : List Nat) (rs : List LinkAllowance) (start l : Nat) :
    ((writesFrom ids rs start).filter fun e=>e.link==l).map value =
    (rs.filter fun r=>target ids r==some l).map pair := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
    simp only [writesFrom,List.zipIdx_cons,List.filterMap_cons]
    cases ht:target ids r with
    | none => simpa [ht,writesFrom] using ih (start+1)
    | some k =>
      by_cases hk:k=l
      · subst k
        simpa [ht,value,pair,writesFrom] using congrArg (List.cons (pair r)) (ih (start+1))
      · simpa [ht,hk,writesFrom] using ih (start+1)

theorem last_write_value (ids : List Nat) (rs : List LinkAllowance) (l : Nat) :
    (((writeEvents ids rs).filter fun e=>e.link==l).map value).getLast? =
      (winner ids rs l).map pair := by
  change (((writesFrom ids rs 0).filter fun e=>e.link==l).map value).getLast? = _
  rw [values_from,List.getLast?_map]
  rfl

/-- Exact initialized memory value read by the canonical query, including the
no-write default. This uses original decoded records, not a proposed AIR row. -/
theorem query_last_write (ids : List Nat) (rs : List LinkAllowance) (e : Event)
    (h:e∈queryEvents ids rs) :
    value e=((((writeEvents ids rs).filter fun w=>w.link==e.link).map value).getLast?).getD (0,false) := by
  obtain ⟨_,_,_,hl,hb⟩:=query_source ids rs e h
  rw [last_write_value]
  unfold value
  rw [hl,hb]
  cases winner ids rs e.link <;> rfl

end ZkFormal.NearV3.Candidates.ProcPriorValues

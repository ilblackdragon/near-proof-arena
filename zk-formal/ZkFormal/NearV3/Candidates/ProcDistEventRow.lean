import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Sched.Spec.Dist
namespace ZkFormal.NearV3.Candidates.ProcDistEventRow
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler

abbrev Acc := Array Endpoint × Array Nat × Endpoint

/-- Exactly the receiver body used by distributeEv. -/
def step (n : Nat) (allowed : Array Bool) (s r : Nat) (acc : Acc) :
    Except String (ForInStep Acc) := do
  let (ri,g,se) := acc
  let l := s*n+r
  if allowed[l]! then
    let re := ri[r]!
    if se.1=0 || re.1=0 then throw "distribute break"
    let gb := Nat.min (se.2/se.1) (re.2/re.1)
    return .yield (ri.set! r (re.1-1,re.2-gb),g.set! l gb,(se.1-1,se.2-gb))
  else return .yield acc

def row (n : Nat) (allowed : Array Bool) (s : Nat) (rs : List Nat) (acc : Acc) :
    Except String Acc := forIn rs acc (step n allowed s)

/-- Total grid recurrence with the same numerical grants representation. -/
def grid (n : Nat) (allowed : Array Bool) (s : Nat) : List Nat → Acc → Acc
  | [],acc => acc
  | r::rs,(ri,g,se) =>
    if allowed[s*n+r]! then
      let re := ri[r]!
      let gb := Nat.min (se.2/se.1) (re.2/re.1)
      grid n allowed s rs (ri.set! r (re.1-1,re.2-gb),g.set! (s*n+r) gb,(se.1-1,se.2-gb))
    else grid n allowed s rs (ri,g,se)

/-- Definitional connection to the actual event generator, not a replacement algorithm. -/
theorem distribute_refactor (n : Nat) (allowed : Array Bool) (sb rb cs cr : Array Nat) :
    distributeEv n allowed sb rb cs cr = (do
      let sord := sortedBy (fun s => avgOf cs[s]! sb[s]!) n
      let rord := sortedBy (fun r => avgOf cr[r]! rb[r]!) n
      let acc ← forIn sord ((List.range n).toArray.map (fun r => (cr[r]!,rb[r]!)),
          Array.replicate (n*n) 0) (fun s acc => do
        let out ← row n allowed s rord (acc.1,acc.2,(cs[s]!,sb[s]!))
        return .yield (out.1,out.2.1))
      return (acc.2,sord,rord)) := rfl

/-- The actual receiver loop cannot throw while counts describe unvisited links. -/
theorem row_eq_grid (n : Nat) (allowed : Array Bool) (s : Nat) :
    ∀ (rs : List Nat) (ri : Array Endpoint) (g : Array Nat) (se : Endpoint),
      rs.Nodup → se.1=(rs.filter fun r => allowed[s*n+r]!).length →
      (∀ r ∈ rs, allowed[s*n+r]! = true → 1≤(ri[r]!).1) →
      row n allowed s rs (ri,g,se)=.ok (grid n allowed s rs (ri,g,se))
  | [],ri,g,se,_,_,_ => rfl
  | r::rs,ri,g,se,hnd,hse,hri => by
    rw [List.nodup_cons] at hnd
    by_cases ha : allowed[s*n+r]! = true
    · have h1 := hri r (by simp) ha
      have h2 : se.1=(rs.filter fun r => allowed[s*n+r]!).length+1 := by
        simpa [List.filter_cons,ha] using hse
      have hs : se.1≠0 := by omega
      have hr : (ri[r]!).1≠0 := by omega
      simp only [row,List.forIn_cons,step,ha,hs,hr,decide_false,Bool.or_self,
        Bool.false_eq_true,ite_false,ite_true,pure,Except.pure,bind,Except.bind,
        grid] 
      apply row_eq_grid n allowed s rs _ _ _ hnd.2
      · simp only; omega
      · intro r' hr' ha'
        rw [getElem!_set!_ne _ _ (fun e => by subst e; exact hnd.1 hr')]
        exact hri r' (by simp [hr']) ha'
    · simp only [row,List.forIn_cons,step,ha,pure,Except.pure,
        bind,Except.bind,grid]
      apply row_eq_grid n allowed s rs ri g se hnd.2
      · simpa [List.filter_cons,ha] using hse
      · intro r' hr' ha'
        exact hri r' (by simp [hr']) ha'
theorem grid_receiver_count (n : Nat) (allowed : Array Bool) (s : Nat) :
    ∀ (rs : List Nat) (se : Endpoint) (ri : Array Endpoint) (g : Array Nat),
      rs.Nodup → ∀ r,
      ((grid n allowed s rs (ri,g,se)).1[r]!).1 =
        (ri[r]!).1 - (if r ∈ rs ∧ allowed[s * n + r]! = true then 1 else 0)
  | [], se, ri, g, _, r => by simp [grid]
  | r' :: rs, se, ri, g, hnd, r => by
    rw [List.nodup_cons] at hnd
    by_cases ha : allowed[s * n + r']! = true
    · simp only [grid, ha, ite_true]
      rw [grid_receiver_count n allowed s rs _ _ _ hnd.2 r]
      by_cases hr : r = r'
      · subst hr
        rw [getElem!_set!_self]
        split
        · simp [ha, hnd.1]
        · rename_i hsz
          rw [getElem!_oob ri (Nat.le_of_not_lt hsz)]
          simp [ha, hnd.1]
          rfl
      · rw [getElem!_set!_ne _ _ (fun e => hr e.symm)]
        simp [hr]
    · have ha' : allowed[s * n + r']! = false := by simpa using ha
      simp only [grid, ha', Bool.false_eq_true, ite_false]
      rw [grid_receiver_count n allowed s rs _ _ _ hnd.2 r]
      by_cases hr : r = r'
      · subst hr; simp [ha', hnd.1]
      · simp [hr]

end ZkFormal.NearV3.Candidates.ProcDistEventRow

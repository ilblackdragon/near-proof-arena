import ZkFormal.NearV3.Candidates.ProcActualInitialPush
namespace ZkFormal.NearV3.Candidates.ProcPushSortContract
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev Record := Nat×Nat×Nat×Nat

/-- The generator compares only timestamp and entry ID, not the full record. -/
def less (a b : Record) : Bool := a.1<b.1 || (a.1==b.1 && a.2.2.2<b.2.2.2)

theorem comparator_ties :
    less (0,1,0,0) (0,2,0,0)=false ∧ less (0,2,0,0) (0,1,0,0)=false := by decide

def stampTime (R t : Nat) := if t<R then t else T0+(t-R)

theorem stamp_strict (R : Nat) (hR : R≤T0) (a b : Nat) (hab : a<b) :
    stampTime R a<stampTime R b := by
  unfold stampTime
  split <;> split <;> omega

theorem stamp_injective (R : Nat) (hR : R≤T0) (a b : Nat)
    (h : stampTime R a=stampTime R b) : a=b := by
  by_cases hab : a<b
  · have := stamp_strict R hR a b hab; omega
  by_cases hba : b<a
  · have := stamp_strict R hR b a hba; omega
  omega

theorem stamped_order (R : Nat) (hR : R≤T0) (ps : List Push)
    (h : ps.Pairwise (fun a b=>a.ts<b.ts)) :
    (ps.map (ProcPushConservation.stamp R)).Pairwise (fun a b=>a.1<b.1) := by
  apply List.pairwise_map.mpr
  exact h.imp (fun {a b} hab=>stamp_strict R hR a.ts b.ts hab)

/-- Strict timestamp ordering plus the already-proved permutation suffices for
canonical equality. Establishing these sorting postconditions remains required. -/
theorem sorted_unique (xs ys : List Record)
    (hx : xs.Pairwise (fun a b=>a.1<b.1)) (hy : ys.Pairwise (fun a b=>a.1<b.1))
    (hp : xs.Perm ys) : xs=ys := by
  apply hp.eq_of_pairwise (fun a b _ _ hab hba=>by omega) hx hy
end ZkFormal.NearV3.Candidates.ProcPushSortContract

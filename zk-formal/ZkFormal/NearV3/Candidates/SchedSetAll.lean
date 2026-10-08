import ZkFormal.NearV3.Sched.Gen.Dist
namespace ZkFormal.NearV3.Candidates.SchedSetAll
open ZkFormal.NearV3.Sched.Gen

/-- Sparse native row assignments retain the final assignment to a column. -/
def lookup (kv : List (Nat×Nat)) (c initial : Nat) : Nat :=
  kv.foldl (fun v p => if p.1=c then p.2 else v) initial

theorem fold_size (kv : List (Nat×Nat)) (a : Array Nat) :
    (kv.foldl (fun r p => r.set! p.1 p.2) a).size=a.size := by
  induction kv generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons,ih]
    simp

theorem fold_cell (kv : List (Nat×Nat)) (a : Array Nat) (c : Nat) (hc:c<a.size) :
    (kv.foldl (fun r p => r.set! p.1 p.2) a)[c]! = lookup kv c a[c]! := by
  induction kv generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons]
    have hc' : c<(a.set! p.1 p.2).size := by simpa using hc
    rw [ih _ hc']
    unfold lookup
    rw [List.foldl_cons]
    by_cases he:p.1=c
    · rw [if_pos he,he,Array.getElem!_set!_self _ _ _ hc]
    · rw [if_neg he,Array.getElem!_set!_ne _ _ _ _ he]

theorem width (w : Nat) (kv : List (Nat×Nat)) : (setAll w kv).size=w := by
  unfold setAll
  rw [fold_size]
  simp [zrow]

theorem cell (w : Nat) (kv : List (Nat×Nat)) (c : Nat) (hc:c<w) :
    (setAll w kv)[c]! = lookup kv c 0 := by
  have hz : c<(zrow w).size := by simpa [zrow] using hc
  simpa [setAll,zrow,hc] using fold_cell kv (zrow w) c hz

theorem append (xs ys : List (Nat×Nat)) (c v : Nat) :
    lookup (xs++ys) c v = lookup ys c (lookup xs c v) := by
  simp [lookup,List.foldl_append]

theorem lookup_miss (xs : List (Nat×Nat)) (c v : Nat)
    (h:∀p∈xs,p.1≠c) : lookup xs c v=v := by
  induction xs generalizing v with
  | nil => rfl
  | cons p ps ih =>
    have hp:=h p (by simp)
    have ht:∀q∈ps,q.1≠c := fun q hq=>h q (by simp [hq])
    simpa only [lookup,List.foldl_cons,if_neg hp] using ih v ht

theorem last_assignment (w c v : Nat) (xs ys : List (Nat×Nat)) (hc:c<w)
    (hy:∀p∈ys,p.1≠c) :
    (setAll w (xs++(c,v)::ys))[c]! = v := by
  rw [cell w _ c hc,append]
  change lookup ys c (if c=c then v else lookup xs c 0)=v
  rw [if_pos rfl]
  exact lookup_miss ys c v hy

end ZkFormal.NearV3.Candidates.SchedSetAll

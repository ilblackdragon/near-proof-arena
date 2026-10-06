import NearSpecV3.PrepD0

/-!
# ZkFormal.NearV3.Sched.Spec.DistDefs — distribute-remaining as the AIR's grid (definitions)

`NearSpecV3.Scheduler.distribute` visits, for each sender in sorted order, the receivers in
sorted order and `break`s when an endpoint has `links_num = 0`. The AIR (`sdsV3`) computes the
same grants on the `n × n` grid of (sorted sender position `i`, sorted receiver position `j`):

* `SE i j` — the sender endpoint `(links, left)` of `sord[i]` before receiver position `j`;
* `RE i j` — the receiver endpoint of `rord[j]` before sender position `i`;
* `gb i j = min(SE.left / SE.links, RE.left / RE.links)` on an allowed cell; the endpoints step
  only on allowed cells.

Proved in `Sched/Spec/Dist.lean`:
* the `break` never fires (`links_num` counts exactly the allowed links still to visit);
* `distribute` = the grid grants (`distribute_eq_grid`);
* the sorted orders are the unique permutations of `[0, n)` with strictly increasing key
  `avg·64 + idx` (`sortByKey_eq_of_sorted`).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- Links count of sender `s` / receiver `r` (as `distribute` computes them). -/
def cntS (n : Nat) (allowed : Array Bool) (s : Nat) : Nat :=
  ((List.range n).filter fun r => allowed[s * n + r]!).length

def cntR (n : Nat) (allowed : Array Bool) (r : Nat) : Nat :=
  ((List.range n).filter fun s => allowed[s * n + r]!).length

/-- Sort key used by the AIR: strictly increasing along a stable sort by `avg` (for `idx < 64`). -/
def sortKey (avg idx : Nat) : Nat := avg * 64 + idx

/-- The grid state after the first `i` sender rows: receiver endpoints by receiver *index*, and
the grants so far by link. Row `i` walks `rord` with the sender endpoint of `sord[i]`. -/
def gridRow (n : Nat) (allowed : Array Bool) (s : Nat) :
    List Nat → Endpoint → Array Endpoint → Array (Option Nat) →
      Endpoint × Array Endpoint × Array (Option Nat)
  | [], se, ri, g => (se, ri, g)
  | r :: rs, se, ri, g =>
    if !allowed[s * n + r]! then gridRow n allowed s rs se ri g else
    let re := ri[r]!
    let gb := Nat.min (se.2 / se.1) (re.2 / re.1)
    gridRow n allowed s rs (se.1 - 1, se.2 - gb) (ri.set! r (re.1 - 1, re.2 - gb))
      (g.set! (s * n + r) (some gb))

/-- The whole grid (no `break`): grants by link. -/
def gridGrants (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat) :
    Array (Option Nat) :=
  let si : Array Endpoint := ((List.range n).map fun s => (cntS n allowed s, sb[s]!)).toArray
  let ri : Array Endpoint := ((List.range n).map fun r => (cntR n allowed r, rb[r]!)).toArray
  (sord.foldl (fun (acc : Array Endpoint × Array (Option Nat)) s =>
      let (_, ri', g') := gridRow n allowed s rord si[s]! acc.1 acc.2
      (ri', g')) (ri, Array.replicate (n * n) none)).2

/-- Grants applied to the state (as `distribute` does with `grantMore`). -/
def applyGrants (n : Nat) (st : St) (g : Array (Option Nat)) : St :=
  (List.range (n * n)).foldl (fun st l =>
    match g[l]! with
    | some b => grantMore st l b
    | none => st) st

/-- The spec's sorted orders. -/
def sordOf (n : Nat) (allowed : Array Bool) (sb : Array Nat) : List Nat :=
  sortByKey (fun s => avgLink (cntS n allowed s, sb[s]!)) (List.range n)

def rordOf (n : Nat) (allowed : Array Bool) (rb : Array Nat) : List Nat :=
  sortByKey (fun r => avgLink (cntR n allowed r, rb[r]!)) (List.range n)

end ZkFormal.NearV3.Sched

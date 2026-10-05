import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Walk

/-!
# ZkFormal.Near.Render.Walk — honest rows of the `walk` table

One segment per receipt (batch order): the `START` row, then one row per key
symbol of `nibbles (0 ‖ receiver) ++ [END]`.  The chained edge counter `u` of a
step is the number of earlier steps (in table order) using the same edge.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Near

/-- Steps of walks `r, r+1, …` with their receipt index. -/
def stepsFrom : List (List WStep) → Nat → List (Nat × WStep)
  | [], _ => []
  | w :: ws, r => w.map (r, ·) ++ stepsFrom ws (r + 1)

/-- All steps in table order, with their receipt index. -/
def walkSteps (ws : List (List WStep)) : List (Nat × WStep) := stepsFrom ws 0

/-- The chained edge counter of step `j` of `st`: earlier steps with the same edge. -/
def useAtL (st : List (Nat × WStep)) (j : Nat) : Nat :=
  ((st.take j).filter fun p => p.2.edge == (st.getD j default).2.edge).length

def useAt (ws : List (List WStep)) (j : Nat) : Nat := useAtL (walkSteps ws) j

/-- All counters (computed once). -/
def usesL (st : List (Nat × WStep)) : List Nat := (List.range st.length).map (useAtL st)

/-- Cells of the row of step `(r, s)` with counter `u`. -/
def walkCell (p : Nat × WStep) (u : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if p.2.t.isNone then 1 else 0
  | 2 => if p.2.last then 1 else 0
  | 3 => p.1
  | 4 => p.2.t.getD 0
  | 5 => p.2.sym
  | 6 => p.2.edge.getD 0 0
  | 7 => p.2.edge.getD 1 0
  | 8 => p.2.edge.getD 3 0
  | 9 => p.2.edge.getD 4 0
  | 10 => u
  | 11 => if p.2.t.isNone then 0 else 1
  | _ => 0

def walkRowsAll (ws : List (List WStep)) : Array Row :=
  let st := walkSteps ws
  let us := usesL st
  mkTab (2 ^ logOf st.length) WalkTab.width fun q col =>
    if q < st.length then walkCell (st.getD q default) (us.getD q 0) col else 0

end ZkFormal.Near.Render

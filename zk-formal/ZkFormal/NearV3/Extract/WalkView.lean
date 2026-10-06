import ZkFormal.Near.Extract.SmallViews
import ZkFormal.NearV3.Tables.Walk

/-!
# ZkFormal.NearV3.Extract.WalkView — the `walkV3` view statement

One `WalkR` per walk segment.  Each row is a `WStep3`:
* `mode` — `0` step (edge), `1` absent by key (edge), `2` absent at a branch (`BMAP`),
  `3` drain;
* `sym` — the key symbol (`START` on the first row);
* `e = [N, I, nib, N2, I2, ek]` — the edge message (for mode 2 only `N`, `I` matter);
* `u` — the edge use count; `bm`, `hv`, `ub` — the `BMAP` message and use count.

`WalkWf3` collects what the constraints give, as naturals (canonical representatives).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure WStep3 where
  mode : Nat
  sym : Nat
  e : Msg
  u : Nat
  bm : Nat
  hv : Nat
  ub : Nat
  deriving Repr, Inhabited

structure WalkR where
  w : Nat
  tau : Nat
  steps : List WStep3
  deriving Repr, Inhabited

def WalkR.step (wv : WalkR) (i : Nat) : WStep3 := wv.steps.getD i default
def WalkR.last (wv : WalkR) : WStep3 := wv.step (wv.steps.length - 1)

/-- `FINAL` kind and target of a walk. -/
def WalkR.fk (wv : WalkR) : Nat := if wv.last.mode = 0 then FK_VAL else FK_ABS
def WalkR.k (wv : WalkR) : Nat := if wv.last.mode = 0 then wv.last.e.getD 3 0 else 0

/-- Facts about one row. -/
structure StepOk (st : WStep3) (isLast : Bool) : Prop where
  mode : st.mode ≤ 3
  elen : st.e.length = 6
  /-- step: the edge carries the symbol; kind `DOWN`/`KEY`, or `VAL` on the last row -/
  stepE : st.mode = 0 → st.e.getD 2 0 = st.sym ∧
    (isLast = false → st.e.getD 5 0 = EK_DOWN ∨ st.e.getD 5 0 = EK_KEY) ∧
    (isLast = true → st.e.getD 5 0 = EK_VAL)
  /-- absent by key: a `KEY`/`LEND` edge with a different symbol -/
  absK : st.mode = 1 → (st.e.getD 5 0 = EK_KEY ∨ st.e.getD 5 0 = EK_LEND) ∧ st.e.getD 2 0 ≠ st.sym
  /-- absent at a branch (position 0) -/
  absB : st.mode = 2 → st.e.getD 1 0 = 0 ∧ st.bm < 2 ^ 16 ∧ st.hv ≤ 1 ∧
    (isLast = true → st.hv = 0) ∧
    (isLast = false → st.sym < 16 ∧ st.bm / 2 ^ st.sym % 2 = 0)
  /-- the last symbol is `END` -/
  lastEnd : isLast = true → st.sym = SYM_END

structure WalkWf3 (ws : List WalkR) : Prop where
  len : ∀ wv ∈ ws, 2 ≤ wv.steps.length
  canon : ∀ wv ∈ ws, wv.w < P ∧ wv.tau < P ∧ ∀ st ∈ wv.steps,
    st.sym < P ∧ st.u < P ∧ st.ub < P ∧ ∀ x ∈ st.e, x < P
  rows : ∀ wv ∈ ws, ∀ i (hi : i < wv.steps.length), StepOk wv.steps[i] (i + 1 == wv.steps.length)
  /-- the first row is the `START` step from `(head, τ)` -/
  start : ∀ wv ∈ ws, (wv.step 0).mode = 0 ∧ (wv.step 0).sym = SYM_START ∧ (wv.step 0).e.getD 1 0 = wv.tau
  /-- consecutive rows -/
  chain : ∀ wv ∈ ws, ∀ i, i + 1 < wv.steps.length →
    ((wv.step i).mode = 0 → (wv.step (i + 1)).e.take 2 = ((wv.step i).e.drop 3).take 2 ∧
      (wv.step (i + 1)).mode ≠ 3) ∧
    ((wv.step i).mode ≠ 0 → (wv.step (i + 1)).mode = 3)

/-- Edge message of a row with use count `x`. -/
def WStep3.edgeMsg (st : WStep3) (x : Nat) : Msg := st.e ++ [x]
def WStep3.bmapMsg (st : WStep3) (x : Nat) : Msg := [st.e.getD 0 0, st.bm, st.hv, x]

def walkSends3 (ws : List WalkR) (b : Nat) : List Msg :=
  if b = B_EDGE then ws.flatMap fun wv => (wv.steps.filter fun st => st.mode ≤ 1).map fun st => st.edgeMsg (st.u + 1)
  else if b = B_BMAP then ws.flatMap fun wv => (wv.steps.filter fun st => st.mode = 2).map fun st => st.bmapMsg (st.ub + 1)
  else if b = B_FINAL then ws.map fun wv => [wv.w, wv.tau, wv.fk, wv.k]
  else []

def walkRecvs3 (ws : List WalkR) (b : Nat) : List Msg :=
  if b = B_EDGE then ws.flatMap fun wv => (wv.steps.filter fun st => st.mode ≤ 1).map fun st => st.edgeMsg st.u
  else if b = B_BMAP then ws.flatMap fun wv => (wv.steps.filter fun st => st.mode = 2).map fun st => st.bmapMsg st.ub
  else if b = B_KEYNIB then
    ws.flatMap fun wv => (List.range (wv.steps.length - 1)).map fun t =>
      [wv.w, t, (wv.step (t + 1)).sym, if t + 2 = wv.steps.length then 1 else 0]
  else []

def walkTraffic3 (ws : List WalkR) : Traffic := ⟨walkSends3 ws, walkRecvs3 ws⟩

/-- **The `walkV3` view statement** (any table index `t`). -/
def WalkV3ViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal WalkV3.table tr t pub →
    ∃ ws, WalkWf3 ws ∧ TableTraffic WalkV3.interactions tr t pub (walkTraffic3 ws)

end ZkFormal.NearV3

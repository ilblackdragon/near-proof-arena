import ZkFormal.Size.Sched

/-!
# ZkFormal.Size.Model — the parametric accounting model of `sizeMaxDedup`

`sizeMaxDedup A prm` depends on the AIR only through each table's static counts
(`TShape`: base width, aux and quotient K-columns, running-product finals at `auxGroup`,
`maxLog`).  `sizeOfWeq prm ts` is the same closed formula over a list of shapes, and

* `sizeMaxDedup_eq_model : sizeMaxDedup A prm = sizeOfWeq prm (A.tables.map (shapeOf prm.auxGroup))`
* `sizeMaxSched_eq_model : sizeMaxSched A prm = sizeOfSchedS prm (A.tables.map (shapeOf prm.auxGroup))`

so any AIR whose tables have the shapes `ts` has exactly the bound `sizeOfWeq prm ts`
(evaluated by `decide +kernel` on synthetic shape lists in `Size/V3Synth.lean`).

Per table `t` (`nq = 216`, `N = maxLogLde`, `r_t = min nq 2^(maxLog_t + logBlowup)`):
* rows: `4·r_t·W_eq(t)` with `W_eq = w + 8·aux + 8·quot` (`= 864·W_eq` when `r_t = nq`);
* prefix: `32·fin_t` (finals) + `32·(2w + 2aux + quot)` (OOD) + 1 header byte;
and globally `3·64·dsum nq N` (main/aux/quotient digests), `64·N + 64 + 200 + 64·N` prefix
constants, and the FRI DP `phiMaxG … (costD nq B) (N - B)` whose roll-in cap
`capS` counts the tables by `maxLog`.
-/

namespace ZkFormal.Size

open ZkFormal.Stark ZkFormal.Air ZkFormal.Prover ZkFormal.Prover.SizeBound ZkFormal.V2.SizeSched

/-- Static counts of one table at a fixed `auxGroup`. -/
structure TShape where
  w : Nat
  aux : Nat
  quot : Nat
  fin : Nat
  maxLog : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The shape of a table at `auxGroup = g`. -/
def shapeOf (g : Nat) (T : Air.Table) : TShape :=
  ⟨T.width, T.auxCount g, T.quotCount g,
    numGroups (T.numSide true) g + numGroups (T.numSide false) g, T.maxLog⟩

/-- `W_eq` of a shape (`Near.Budget.weqTable`). -/
def TShape.weq (t : TShape) : Nat := t.w + 8 * t.aux + 8 * t.quot

/-- Roll-in cap over shapes (`capE`). -/
def capS (prm : Params) (ts : List TShape) (e : Nat) : Nat :=
  (ts.map fun t => if e ≤ t.maxLog - prm.finalLog then 1 else 0).sum - 1

/-- Header-free prefix over shapes (`prefixMax`). -/
def prefixS (prm : Params) (ts : List TShape) : Nat :=
  (8 + ts.length) + 64 + (64 + 32 * (ts.map (·.fin)).sum) + 64 +
    32 * (ts.map fun t => 2 * t.w + 2 * t.aux + t.quot).sum + (64 * prm.maxLogLde + 64)

/-- Deduplicated rows over shapes (`rowsMax`). -/
def rowsS (prm : Params) (ts : List TShape) (f : TShape → Nat) : Nat :=
  (ts.map fun t => min (prm.numChunks * prm.posPerChunk) (2 ^ (t.maxLog + prm.logBlowup)) * f t).sum

/-- Deduplicated FRI over shapes (`friDedupMax`). -/
def friS (prm : Params) (ts : List TShape) : Nat :=
  phiMaxG (max prm.maxArityLog 1) ts.length (capS prm ts)
    (costD (prm.numChunks * prm.posPerChunk) (prm.logBlowup + prm.finalLog))
    (prm.maxLogLde - prm.logBlowup - prm.finalLog)

/-- **The accounting model**: `sizeMaxDedup` as a function of the table shapes. -/
def sizeOfWeq (prm : Params) (ts : List TShape) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixS prm ts +
    (4 * rowsS prm ts (·.w) + 64 * dsum nq N) +
    (4 * rowsS prm ts (fun t => 8 * t.aux) + 64 * dsum nq N) +
    (4 * rowsS prm ts (fun t => 8 * t.quot) + 64 * dsum nq N) +
    friS prm ts

/-- The P1 bound (`sizeMaxSched`) over shapes, for comparison. -/
def sizeOfSchedS (prm : Params) (ts : List TShape) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixS prm ts +
    nq * (4 * (ts.map (·.w)).sum + 64 * N) +
    nq * (4 * (ts.map fun t => 8 * t.aux).sum + 64 * N) +
    nq * (4 * (ts.map fun t => 8 * t.quot).sum + 64 * N) +
    nq * phiMaxG (max prm.maxArityLog 1) ts.length (capS prm ts) (stepCost (prm.logBlowup + prm.finalLog))
      (prm.maxLogLde - prm.logBlowup - prm.finalLog)

theorem capE_eq (A : Air) (prm : Params) :
    capE A prm = capS prm (A.tables.map (shapeOf prm.auxGroup)) := by
  funext e
  simp only [capE, capS, List.map_map]
  rfl

theorem prefixMax_eq (A : Air) (prm : Params) :
    prefixMax A prm = prefixS prm (A.tables.map (shapeOf prm.auxGroup)) := by
  simp only [prefixMax, prefixS, finalsMax, totalCols, List.map_map, List.length_map]
  rfl

/-- **`sizeMaxDedup` is the model evaluated at the AIR's shapes.** -/
theorem sizeMaxDedup_eq_model (A : Air) (prm : Params) :
    sizeMaxDedup A prm = sizeOfWeq prm (A.tables.map (shapeOf prm.auxGroup)) := by
  unfold sizeMaxDedup sizeOfWeq friDedupMax friS rowsS rowsMax
  rw [prefixMax_eq, capE_eq]
  simp only [List.map_map, List.length_map]
  rfl

theorem sizeMaxSched_eq_model (A : Air) (prm : Params) :
    sizeMaxSched A prm = sizeOfSchedS prm (A.tables.map (shapeOf prm.auxGroup)) := by
  unfold sizeMaxSched sizeOfSchedS friSchedMax
  rw [prefixMax_eq, phiMax_eq, capE_eq]
  simp only [List.map_map, List.length_map]
  rfl

/-! ## Breakdown (for reporting) -/

/-- `(prefix, main, aux, quotient, FRI)` parts of `sizeOfWeq`. -/
def partsS (prm : Params) (ts : List TShape) : Nat × Nat × Nat × Nat × Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  (prefixS prm ts, 4 * rowsS prm ts (·.w) + 64 * dsum nq N,
    4 * rowsS prm ts (fun t => 8 * t.aux) + 64 * dsum nq N,
    4 * rowsS prm ts (fun t => 8 * t.quot) + 64 * dsum nq N, friS prm ts)

theorem sizeOfWeq_parts (prm : Params) (ts : List TShape) :
    sizeOfWeq prm ts = (partsS prm ts).1 + (partsS prm ts).2.1 + (partsS prm ts).2.2.1 +
      (partsS prm ts).2.2.2.1 + (partsS prm ts).2.2.2.2 := rfl

end ZkFormal.Size

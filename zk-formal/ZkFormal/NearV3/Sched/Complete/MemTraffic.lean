import ZkFormal.NearV3.Sched.Complete.Mem

/-!
# ZkFormal.NearV3.Sched.Complete.MemTraffic — the memory table's traffic as op-log lists (M4)

* `sopList segs`: per segment its INIT message `(addr, 0, OP_INIT, vin₀, v₀, w₀, 0, isL)`, then
  the op log `(addr, t, op, vin, v, inc, ok, c)` in order — exactly what `smmV3` receives on `SOP`;
* `finList segs`: `(addr, vfin, wfin)` per segment — what it sends on `SFIN`;
* `cmpList segs`: per op `(t, tp + 1, 1)` (`tp` = previous op time, `0` first), then
  `(vin, inc, sf)` for a GRANT — what it sends on `SCMP`;
* nothing else on any bus / direction.

**`mem_complete`** collects heights, constraints, bits and traffic.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def sopInit (g : Seg) : List Nat := [g.addr, 0, OP_INIT, g.vin0, g.v0, g.w0, 0, b2n g.isL]
def sopOp (g : Seg) (o : MOp) : List Nat := [g.addr, o.t, o.op, o.vin, o.v, o.inc, b2n o.ok, b2n o.c]

/-- The `SOP` messages received by the memory: INITs and the op log. -/
def sopList (segs : List Seg) : List (List Nat) := segs.flatMap fun g => sopInit g :: g.ops.map (sopOp g)

/-- The `SFIN` messages sent by the memory: final values. -/
def finList (segs : List Seg) : List (List Nat) := segs.map fun g => [g.addr, g.vfin, g.wfin]

def opsCmp : Nat → List MOp → List (List Nat)
  | _, [] => []
  | tp, o :: os => [o.t, tp + 1, 1] :: ((if o.op = OP_GRANT then [[o.vin, o.inc, b2n o.sf]] else []) ++
      opsCmp o.t os)

/-- The `SCMP` messages sent by the memory: time order and GRANT budget checks. -/
def cmpList (segs : List Seg) : List (List Nat) := segs.flatMap fun g => opsCmp 0 g.ops

/-! ## Row messages per bus -/

theorem rowMsgs_sop (X : MV) : rowMsgs B_SOP false X = if X.act = 1 then [sopMsg X] else [] := by
  simp [rowMsgs, B_SOP, B_SFIN, B_SCMP]

theorem rowMsgs_fin (X : MV) : rowMsgs B_SFIN true X = if X.lst = 1 then [finMsg X] else [] := by
  simp [rowMsgs, B_SOP, B_SFIN, B_SCMP]

theorem rowMsgs_cmp (X : MV) : rowMsgs B_SCMP true X =
    (if X.isRd + X.isGr = 1 then [cmpTMsg X] else []) ++ (if X.isGr = 1 then [cmpVMsg X] else []) := by
  simp [rowMsgs, B_SOP, B_SFIN, B_SCMP]

theorem rowMsgs_other {b : Nat} {send : Bool} (h1 : ¬ (b = B_SOP ∧ send = false))
    (h2 : ¬ (b = B_SFIN ∧ send = true)) (h3 : ¬ (b = B_SCMP ∧ send = true)) (X : MV) :
    rowMsgs b send X = [] := by
  unfold rowMsgs
  rw [if_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg (fun h => h2 ⟨h.1, h.2.1⟩),
    if_neg (fun h => h3 ⟨h.1, h.2.1⟩), if_neg (fun h => h3 ⟨h.1, h.2.1⟩)]
  rfl

/-! ## Per segment -/

theorem op_kind_cases {o : MOp} (h : o.op = OP_READ ∨ o.op = OP_GRANT) :
    b2n (o.op == OP_READ) + b2n (o.op == OP_GRANT) = 1 ∧
      b2n (o.op == OP_READ) + 2 * b2n (o.op == OP_GRANT) = o.op := by
  rcases h with h | h <;> rw [h] <;> decide

theorem ops_sop (g : Seg) : ∀ (os : List MOp) (k tp pv pw : Nat), OpsOk g pv pw os →
    (opsVs g k tp os).flatMap (rowMsgs B_SOP false) = os.map (sopOp g)
  | [], _, _, _, _, _ => rfl
  | o :: os, k, tp, pv, pw, ⟨ho, hos⟩ => by
    simp only [opsVs, List.flatMap_cons, List.map_cons, rowMsgs_sop]
    rw [ops_sop g os (k + 1) o.t o.v o.w hos]
    simp only [opV, if_true, List.singleton_append]
    congr 1
    simp only [sopMsg, sopOp, (op_kind_cases ho.kind).2]

theorem seg_sop (g : Seg) (hg : SegOk g) : (segVs g).flatMap (rowMsgs B_SOP false) = sopInit g :: g.ops.map (sopOp g) := by
  simp only [segVs, List.flatMap_cons, rowMsgs_sop]
  rw [ops_sop g g.ops 0 0 g.v0 g.w0 hg.ops]
  simp [initV, sopMsg, sopInit, OP_INIT]

theorem ops_fin (g : Seg) : ∀ (os : List MOp) (k tp : Nat), k + os.length = g.ops.length →
    (opsVs g k tp os).flatMap (rowMsgs B_SFIN true) =
      match os.getLast? with | some o => [[g.addr, o.v, o.w]] | none => []
  | [], _, _, _ => rfl
  | o :: os, k, tp, hk => by
    simp only [opsVs, List.flatMap_cons, rowMsgs_fin]
    have hk' : k + 1 + os.length = g.ops.length := by simp at hk; omega
    rw [ops_fin g os (k + 1) o.t hk']
    cases os with
    | nil =>
      have : (k + 1 == g.ops.length) = true := by simp at hk'; simp [hk']
      simp [opV, this, b2n, finMsg]
    | cons o' os =>
      have : (k + 1 == g.ops.length) = false := by simp at hk' ⊢; omega
      simp only [opV, this, b2n]
      simp [List.getLast?_cons_cons]

theorem seg_fin (g : Seg) : (segVs g).flatMap (rowMsgs B_SFIN true) = [[g.addr, g.vfin, g.wfin]] := by
  simp only [segVs, List.flatMap_cons, rowMsgs_fin]
  rw [ops_fin g g.ops 0 0 (by omega)]
  unfold Seg.vfin Seg.wfin
  cases h : g.ops.getLast? with
  | none =>
    have : g.ops = [] := List.getLast?_eq_none_iff.1 h
    simp [initV, this, b2n, finMsg]
  | some o =>
    have : g.ops ≠ [] := fun e => by rw [e] at h; simp at h
    have : (g.ops.length == 0) = false := by simpa using this
    simp [initV, this, b2n]

theorem ops_cmp (g : Seg) : ∀ (os : List MOp) (k tp pv pw : Nat), OpsOk g pv pw os →
    (opsVs g k tp os).flatMap (rowMsgs B_SCMP true) = opsCmp tp os
  | [], _, _, _, _, _ => rfl
  | o :: os, k, tp, pv, pw, ⟨ho, hos⟩ => by
    simp only [opsVs, List.flatMap_cons, rowMsgs_cmp, opsCmp]
    rw [ops_cmp g os (k + 1) o.t o.v o.w hos]
    simp only [opV, (op_kind_cases ho.kind).1, if_true, List.singleton_append, List.cons_append]
    congr 2
    rcases ho.kind with h | h
    · simp [h, OP_READ, OP_GRANT, b2n]
    · simp [h, OP_GRANT, b2n, cmpVMsg]

theorem seg_cmp (g : Seg) (hg : SegOk g) : (segVs g).flatMap (rowMsgs B_SCMP true) = opsCmp 0 g.ops := by
  simp only [segVs, List.flatMap_cons, rowMsgs_cmp]
  rw [ops_cmp g g.ops 0 0 g.v0 g.w0 hg.ops]
  simp [initV]

/-! ## All segments -/

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem memVs_flatMap (f : MV → List (List Nat)) (segs : List Seg) :
    (memVs segs).flatMap f = segs.flatMap fun g => (segVs g).flatMap f := by
  unfold memVs; rw [List.flatMap_assoc]

theorem sop_list (segs : List Seg) (hg : ∀ g ∈ segs, SegOk g) :
    (memVs segs).flatMap (rowMsgs B_SOP false) = sopList segs := by
  rw [memVs_flatMap]; unfold sopList
  exact flatMap_congr' (fun g h => seg_sop g (hg g h))

theorem fin_list (segs : List Seg) : (memVs segs).flatMap (rowMsgs B_SFIN true) = finList segs := by
  rw [memVs_flatMap]; unfold finList
  rw [flatMap_congr' (fun g _ => seg_fin g)]
  induction segs with
  | nil => rfl
  | cons g segs ih => simp [ih]

theorem cmp_list (segs : List Seg) (hg : ∀ g ∈ segs, SegOk g) :
    (memVs segs).flatMap (rowMsgs B_SCMP true) = cmpList segs := by
  rw [memVs_flatMap]; unfold cmpList
  exact flatMap_congr' (fun g h => seg_cmp g (hg g h))

/-! ## Completeness -/

/-- **Completeness of the memory `smmV3`.** For honest segments that fit the table, the honest
trace has a legal height, satisfies every constraint, has boolean multiplicity bits, receives on
`SOP` exactly the INITs and the op log (`sopList`), sends on `SFIN` exactly the final values
(`finList`), sends on `SCMP` exactly `cmpList`, and nothing else. -/
theorem mem_complete (R : Run) (hg : ∀ g ∈ R.segs, SegOk g)
    (hrows : (R.segs.map fun g => g.ops.length + 1).sum + 1 ≤ 2 ^ Mem.maxLog) :
    (∀ t, 1 ≤ (Gen.Mem.trace R).log t ∧ (Gen.Mem.trace R).log t ≤ Mem.maxLog) ∧
    (∀ t pub r, r < (Gen.Mem.trace R).height t → ∀ e ∈ Mem.constraints,
       e.eval (Gen.Mem.trace R) t r pub = 0) ∧
    (∀ t pub r, r < (Gen.Mem.trace R).height t → ∀ i ∈ Mem.interactions, ∀ b ∈ i.mult,
       b.eval (Gen.Mem.trace R) t r pub = 0 ∨ b.eval (Gen.Mem.trace R) t r pub = 1) ∧
    (∀ t pub m,
       tableBusCount Mem.interactions (Gen.Mem.trace R) t pub B_SOP false m = (fmsgs (sopList R.segs)).count m ∧
       tableBusCount Mem.interactions (Gen.Mem.trace R) t pub B_SFIN true m = (fmsgs (finList R.segs)).count m ∧
       tableBusCount Mem.interactions (Gen.Mem.trace R) t pub B_SCMP true m = (fmsgs (cmpList R.segs)).count m ∧
       ∀ b send, ¬ (b = B_SOP ∧ send = false) → ¬ (b = B_SFIN ∧ send = true) → ¬ (b = B_SCMP ∧ send = true) →
         tableBusCount Mem.interactions (Gen.Mem.trace R) t pub b send m = 0) := by
  refine ⟨fun t => mk_log_bounds _ 1 _ (by decide) ?_ t, fun t pub r hr => mem_constraints R hg t pub r hr,
    fun t pub r hr => mem_bits R hg t r pub hr, fun t pub m => ⟨?_, ?_, ?_, fun b send h1 h2 h3 => ?_⟩⟩
  · rw [memRows_size R (fun g h => (hg g h).small), memVs_length]; exact hrows
  · rw [mem_traffic R hg, sop_list R.segs hg]
  · rw [mem_traffic R hg, fin_list R.segs]
  · rw [mem_traffic R hg, cmp_list R.segs hg]
  · rw [mem_traffic R hg]
    rw [flatMap_congr' (g := fun _ => []) (fun X _ => rowMsgs_other h1 h2 h3 X)]
    induction (memVs R.segs) with
    | nil => rfl
    | cons x l ih => simpa using ih

end ZkFormal.NearV3.Sched.Complete

import ZkFormal.NearV3.Sched.Link.Cmp
import ZkFormal.NearV3.Sched.View.Mem

/-!
# ZkFormal.NearV3.Sched.Link.MemBus — the memory table's buses inside a v2 AIR

`MemOwn AP tm`: `smmV3` is table `tm`, the only receiver on `SOP` and the only sender on
`SFIN`, and no public segment uses either bus (STATUS-V3-SCHED §6.1).

* `busCount_single`: a bus side used by one table only counts that table;
* `opMsg_eq`: the `SOP` message of a memory row, `(addr, t, isRd + 2·isGr, vin, v, inc, ok, c)`;
* **`mem_recv_eq_sent`**: for every message `m`, the number of active memory rows receiving `m`
  equals the total send multiplicity of `m` on `SOP` over all tables;
* **`mem_ops_eq_sent`**: the same for the non-`INIT` rows and the messages with op ∈ {1, 2};
  `mem_init_eq_sent` for the `INIT` rows and op 0;
* `mem_sent_row`: every active `SOP` send of any table is the message of an active memory row;
* `sopSent`: all `SOP` sends as a list (`sopSent_count`); **`mem_recv_perm`**, **`mem_ops_perm`**:
  the multiset forms (`memOpRecv ~ (sopSent).filter isOpMsg`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha

/-! ## Generic counting -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem tableBusCount_zero {is : List Interaction} {tr : Trace F} {t : Nat} {pub : List F}
    {b : Nat} {s : Bool} {m : List F} (h : ∀ i ∈ is, i.bus = b → i.send ≠ s) :
    tableBusCount is tr t pub b s m = 0 := by
  rcases Nat.eq_zero_or_pos (tableBusCount is tr t pub b s m) with h0 | hp
  · exact h0
  · obtain ⟨_, _, i, hi, hb, hs, -⟩ := exists_of_tableBusCount (Nat.pos_iff_ne_zero.mp hp)
    exact absurd hs (h i hi hb)

theorem busCount_go_zero (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    ∀ (Ts : List ZkFormal.Air.Table) (k : Nat),
      (∀ t, t < Ts.length → tableBusCount Ts[t]!.interactions tr (k + t) pub b s m = 0) →
      busCount.go tr pub b s m Ts k = 0
  | [], _, _ => rfl
  | T :: Ts, k, h => by
    simp only [busCount.go]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    rw [h0, busCount_go_zero tr pub b s m Ts (k + 1) (fun t ht => by
      have := h (t + 1) (by simp; omega)
      rw [show k + (t + 1) = k + 1 + t by omega] at this; simpa using this)]

theorem busCount_go_single (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    ∀ (Ts : List ZkFormal.Air.Table) (k j : Nat), j < Ts.length →
      (∀ t, t < Ts.length → t ≠ j → tableBusCount Ts[t]!.interactions tr (k + t) pub b s m = 0) →
      busCount.go tr pub b s m Ts k = tableBusCount Ts[j]!.interactions tr (k + j) pub b s m
  | [], _, _, h, _ => by simp at h
  | T :: Ts, k, 0, _, h => by
    simp only [busCount.go, Nat.add_zero, List.getElem!_cons_zero]
    rw [busCount_go_zero tr pub b s m Ts (k + 1) (fun t ht => by
      have := h (t + 1) (by simp; omega) (by omega)
      rw [show k + (t + 1) = k + 1 + t by omega] at this; simpa using this), Nat.add_zero]
  | T :: Ts, k, j + 1, hj, h => by
    simp only [busCount.go]
    have h0 := h 0 (by simp) (by omega)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    rw [h0, busCount_go_single tr pub b s m Ts (k + 1) j (by simp at hj; omega) (fun t ht hne => by
      have := h (t + 1) (by simp; omega) (by omega)
      rw [show k + (t + 1) = k + 1 + t by omega] at this; simpa using this)]
    simp only [List.getElem!_cons_succ, Nat.zero_add, show k + 1 + j = k + (j + 1) by omega]

/-- A bus side used by one table only counts that table. -/
theorem busCount_single {A : Air} {tr : Trace F} {pub : List F} {b : Nat} {s : Bool} {m : List F}
    {tc : Nat} (htc : tc < A.tables.length)
    (h : ∀ t, t < A.tables.length → t ≠ tc → ∀ i ∈ A.tables[t]!.interactions, i.bus = b → i.send ≠ s) :
    busCount A tr pub b s m = tableBusCount A.tables[tc]!.interactions tr tc pub b s m := by
  unfold busCount
  have := busCount_go_single tr pub b s m A.tables 0 tc htc (fun t ht hne => by
    rw [Nat.zero_add]; exact tableBusCount_zero (h t ht hne))
  simpa using this

theorem count_filterMap_ite {α : Type} [BEq α] [LawfulBEq α] (l : List Nat) (p : Nat → Prop) [DecidablePred p]
    (g : Nat → α) (m : α) :
    (l.filterMap fun r => if p r then some (g r) else none).count m =
      (l.map fun r => if p r ∧ (g r == m) = true then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    by_cases hp : p r
    · by_cases hg : g r = m
      · simp [hp, hg, ih]; omega
      · simp [hp, hg, ih]
    · simp [hp, ih]

/-- All messages sent (`s = true`) or received on bus `b` by the tables `Ts` (numbered from `k`),
with multiplicity. -/
def busTraffic (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) :
    List ZkFormal.Air.Table → Nat → List (List F)
  | [], _ => []
  | T :: Ts, k => ((List.range (tr.height k)).flatMap fun r => rowTraffic T.interactions tr k r pub b s) ++
      busTraffic tr pub b s Ts (k + 1)

theorem count_busTraffic (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    ∀ (Ts : List ZkFormal.Air.Table) (k : Nat),
      (busTraffic tr pub b s Ts k).count m = busCount.go tr pub b s m Ts k
  | [], _ => rfl
  | T :: Ts, k => by
    simp only [busTraffic, busCount.go, List.count_append, tableBusCount_eq,
      count_busTraffic tr pub b s m Ts (k + 1)]

end

/-! ## Ownership and the `SOP` message -/

/-- `smmV3` is table `tm`, the only receiver on `SOP` and the only sender on `SFIN`; no public
segment uses either bus. -/
structure MemOwn (AP : AirP) (tm : Nat) : Prop where
  lt : tm < AP.tables.length
  tab : AP.tables[tm]! = Mem.table
  only : ∀ t, t < AP.tables.length → t ≠ tm → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SOP → i.send = true
  fin : ∀ t, t < AP.tables.length → t ≠ tm → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SFIN → i.send = false
  pubOp : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SOP
  pubFin : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SFIN

namespace Mem

open ZkFormal.Chacha.Table.E

/-- The `SOP` receive (`Mem.interactions[0]`). -/
def iOp : Interaction :=
  { bus := B_SOP, mult := [c act], send := false,
    msg := [c addr, c t, opE, c vin, c v, c inc, c ok, c cc] }

/-- The time-order comparison (`Mem.interactions[2]`). -/
def iTime : Interaction :=
  { bus := B_SCMP, mult := [.add (c isRd) (c isGr)], send := true, msg := [c t, .add (c tp) (k 1), k 1] }

/-- The final-value send (`Mem.interactions[1]`). -/
def iFin : Interaction := { bus := B_SFIN, mult := [c lst], send := true, msg := [c addr, c v, c w] }

/-- The budget comparison (`Mem.interactions[3]`). -/
def iSf : Interaction := { bus := B_SCMP, mult := [c isGr], send := true, msg := [c vin, c inc, c sf] }

theorem interactions_eq : interactions = [iOp, iFin, iTime, iSf] := rfl

theorem iOp_mem : iOp ∈ interactions := by rw [interactions_eq]; simp
theorem iTime_mem : iTime ∈ interactions := by rw [interactions_eq]; simp

theorem interactions_nodup : interactions.Nodup := by decide

/-- The `SOP` message of row `r`. -/
def opMsg (tr : Trace Fp) (tm : Nat) (pub : List Fp) (r : Nat) : List Fp := iOp.msgVal tr tm r pub

section
variable {tr : Trace Fp} {tm : Nat} {pub : List Fp}

theorem ev_of {e : Expr} {r v : Nat} (h : zev (tenv tr tm r pub) e = (v : Int)) :
    e.eval tr tm r pub = Fp.ofNat v := by
  rw [eval_eq, h, intCast_ofNat]

theorem opMsg_eq (r : Nat) :
    opMsg tr tm pub r = [tr.cell tm r addr, tr.cell tm r t, Fp.ofNat (cv tr tm r isRd + 2 * cv tr tm r isGr),
      tr.cell tm r vin, tr.cell tm r v, tr.cell tm r inc, tr.cell tm r ok, tr.cell tm r cc] := by
  have hop : opE.eval tr tm r pub = Fp.ofNat (cv tr tm r isRd + 2 * cv tr tm r isGr) :=
    ev_of (by simp only [opE, zev_add, zev_smul, zev_c, cur_cv]; omega)
  simp only [opMsg, iOp, Interaction.msgVal, List.map_cons, List.map_nil, hop]
  rfl

theorem multNat_c {i : Interaction} {x r : Nat} (hi : i.mult = [c x]) :
    i.multNat tr tm r pub = if cv tr tm r x = 1 then 1 else 0 := by
  unfold Interaction.multNat
  rw [hi]
  simp only [Interaction.multNat.go]
  have e : (c x).eval tr tm r pub = 1 ↔ cv tr tm r x = 1 := by
    show tr.cell tm r x = 1 ↔ (tr.cell tm r x).toNat = 1
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply Fp.ext; rw [h]; rfl
  by_cases h : cv tr tm r x = 1 <;> simp [e, h]

theorem multNat_ne_of {i : Interaction} {e : Expr} {r : Nat} (hi : i.mult = [e])
    (h : e.eval tr tm r pub = 1) : i.multNat tr tm r pub ≠ 0 := by
  unfold Interaction.multNat
  rw [hi]
  simp [Interaction.multNat.go, h]

theorem ofNat_ne {a b : Nat} (ha : a < 2013265921) (hb : b < 2013265921) (h : a ≠ b) :
    Fp.ofNat a ≠ Fp.ofNat b := fun e => by
  have := congrArg Fp.toNat e
  simp only [Fp.toNat_ofNat, P] at this
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

/-- On an `INIT` row the op is 0, the time 0 and the row active. -/
theorem init_row (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (hf : cv tr tm r fst = 1) :
    cv tr tm r act = 1 ∧ cv tr tm r isRd = 0 ∧ cv tr tm r isGr = 0 ∧
      (opMsg tr tm pub r).take 3 = [tr.cell tm r addr, 0, 0] := by
  obtain ⟨hA, -, -, hR, hG, -, -, -, -, -, hsum, -⟩ := row_flags hL hr
  have ht := (row_init hL hr hf).1
  have h1 : cv tr tm r act = 1 := by omega
  have h2 : cv tr tm r isRd = 0 := by omega
  have h3 : cv tr tm r isGr = 0 := by omega
  refine ⟨h1, h2, h3, ?_⟩
  rw [opMsg_eq, h2, h3]
  have : tr.cell tm r t = 0 := Fp.ext (by rw [Fp.toNat_zero]; exact ht)
  simp only [List.take, this]
  rfl

/-- On an active non-`INIT` row the op is 1 (READ) or 2 (GRANT). -/
theorem op_row (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (ha : cv tr tm r act = 1)
    (hf : cv tr tm r fst = 0) :
    cv tr tm r isRd + cv tr tm r isGr = 1 ∧
      ((opMsg tr tm pub r)[2]? = some 1 ∨ (opMsg tr tm pub r)[2]? = some 2) := by
  obtain ⟨-, -, -, hR, hG, -, -, -, -, -, hsum, -⟩ := row_flags hL hr
  refine ⟨by omega, ?_⟩
  rw [opMsg_eq]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hR with h | h
  · right; rw [h, show cv tr tm r isGr = 1 by omega]; rfl
  · left; rw [h, show cv tr tm r isGr = 0 by omega]; rfl

theorem op_init (hL : MLocal tr tm pub) {r : Nat} (hr : r < tr.height tm) (hf : cv tr tm r fst = 1) :
    (opMsg tr tm pub r)[2]? = some 0 := by
  have := (init_row hL hr hf).2.2.2
  have e : (opMsg tr tm pub r)[2]? = ((opMsg tr tm pub r).take 3)[2]? := by simp
  rw [e, this]; rfl

end

end Mem

/-! ## Received = sent -/

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

open Mem in
theorem mLocal_of (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) : MLocal tr tm pub := by
  have := local_of_holdsP hH hM.lt; rw [hM.tab] at this; exact this

/-- Messages received by the active memory rows. -/
def memRecv (tr : Trace Fp) (tm : Nat) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height tm)).filterMap fun r =>
    if cv tr tm r Mem.act = 1 then some (Mem.opMsg tr tm pub r) else none

/-- Messages received by the active non-`INIT` memory rows (the ops). -/
def memOpRecv (tr : Trace Fp) (tm : Nat) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height tm)).filterMap fun r =>
    if cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0 then some (Mem.opMsg tr tm pub r) else none

/-- Messages received by the `INIT` memory rows. -/
def memInitRecv (tr : Trace Fp) (tm : Nat) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height tm)).filterMap fun r =>
    if cv tr tm r Mem.fst = 1 then some (Mem.opMsg tr tm pub r) else none

theorem mem_recv_table (tm : Nat) (m : List Fp) :
    tableBusCount Mem.interactions tr tm pub B_SOP false m = (memRecv tr tm pub).count m := by
  rw [tableBusCount_eq, count_flatMap_rows, memRecv,
    count_filterMap_ite (p := fun r => cv tr tm r Mem.act = 1) (g := Mem.opMsg tr tm pub)]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [count_rowTraffic_eq]
  have hm := Mem.multNat_c (tr := tr) (tm := tm) (r := r) (pub := pub) (i := Mem.iOp) rfl
  simp only [Mem.interactions_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [Mem.iFin, Mem.iTime, Mem.iSf, B_SOP, B_SFIN, B_SCMP]
  simp only [show Mem.opMsg tr tm pub r = Mem.iOp.msgVal tr tm r pub from rfl,
    show Mem.iOp.bus = 41 from rfl, show Mem.iOp.send = false from rfl, hm]
  by_cases h1 : cv tr tm r Mem.act = 1 <;> by_cases h2 : Mem.iOp.msgVal tr tm r pub = m <;> simp [h1, h2]

/-- Everything received on `SOP` is received by the memory table. -/
theorem mem_recv_count {tm : Nat} (hM : MemOwn AP tm) (m : List Fp) :
    busCount AP.toAir tr pub B_SOP false m = (memRecv tr tm pub).count m := by
  rw [busCount_single (tc := tm) hM.lt (fun t ht hne i hi hb => by rw [hM.only t ht hne i hi hb]; simp)]
  show tableBusCount AP.tables[tm]!.interactions tr tm pub B_SOP false m = _
  rw [hM.tab]; exact mem_recv_table tm m

/-- **Received = sent** (all rows). -/
theorem mem_recv_eq_sent (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) (m : List Fp) :
    (memRecv tr tm pub).count m = busCount AP.toAir tr pub B_SOP true m := by
  have hbal := hH.balance B_SOP m
  rw [pubCount_zero (fun seg h1 h2 => absurd h2 (hM.pubOp seg h1)) _,
    pubCount_zero (fun seg h1 h2 => absurd h2 (hM.pubOp seg h1)) _, mem_recv_count hM] at hbal
  omega

/-- **Received = sent** for the ops: the multiset of `SOP` messages received on non-`INIT`
memory rows equals the multiset of `SOP` messages with op ∈ {1, 2} sent by all tables. -/
theorem mem_ops_eq_sent (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) (m : List Fp)
    (hop : m[2]? = some 1 ∨ m[2]? = some 2) :
    (memOpRecv tr tm pub).count m = busCount AP.toAir tr pub B_SOP true m := by
  rw [← mem_recv_eq_sent hH hM, memOpRecv, memRecv,
    count_filterMap_ite (p := fun r => cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0) (g := Mem.opMsg tr tm pub),
    count_filterMap_ite (p := fun r => cv tr tm r Mem.act = 1) (g := Mem.opMsg tr tm pub)]
  have hL := mLocal_of hH hM
  congr 1
  apply List.map_congr_left
  intro r hr
  have hr' := List.mem_range.mp hr
  by_cases ha : cv tr tm r Mem.act = 1
  · by_cases hm : Mem.opMsg tr tm pub r = m
    · have hf : cv tr tm r Mem.fst = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Mem.row_flags hL hr').2.1 with h | h
        · exact h
        · have := Mem.op_init hL hr' h
          rw [hm] at this
          rcases hop with e | e <;> rw [e] at this <;> simp at this <;>
            exact absurd this.symm (Mem.ofNat_ne (by decide) (by decide) (by decide))
      simp [ha, hm, hf]
    · simp [hm]
  · simp [ha]

/-- **Received = sent** for the `INIT` rows (op 0). -/
theorem mem_init_eq_sent (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) (m : List Fp)
    (hop : m[2]? = some 0) :
    (memInitRecv tr tm pub).count m = busCount AP.toAir tr pub B_SOP true m := by
  rw [← mem_recv_eq_sent hH hM, memInitRecv, memRecv,
    count_filterMap_ite (p := fun r => cv tr tm r Mem.fst = 1) (g := Mem.opMsg tr tm pub),
    count_filterMap_ite (p := fun r => cv tr tm r Mem.act = 1) (g := Mem.opMsg tr tm pub)]
  have hL := mLocal_of hH hM
  congr 1
  apply List.map_congr_left
  intro r hr
  have hr' := List.mem_range.mp hr
  by_cases hf : cv tr tm r Mem.fst = 1
  · simp [hf, (Mem.init_row hL hr' hf).1]
  · by_cases ha : cv tr tm r Mem.act = 1
    · by_cases hm : Mem.opMsg tr tm pub r = m
      · exfalso
        have hf0 : cv tr tm r Mem.fst = 0 := by
          have := (Mem.row_flags hL hr').2.1; omega
        rcases (Mem.op_row hL hr' ha hf0).2 with e | e <;> rw [hm, hop] at e <;> simp at e <;>
          exact Mem.ofNat_ne (by decide) (by decide) (by decide) e
      · simp [hf, hm]
    · simp [hf, ha]

/-- Every active `SOP` send of any table is the message of an active memory row. -/
theorem mem_sent_row (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = B_SOP) (hs : i.send = true)
    (hm : i.multNat tr t r pub ≠ 0) :
    ∃ r', r' < tr.height tm ∧ cv tr tm r' Mem.act = 1 ∧ Mem.opMsg tr tm pub r' = i.msgVal tr t r pub := by
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := send_matched hH hM.lt hM.only hM.pubOp ht hr hi hb hs hm
  rw [hM.tab] at hi'
  simp only [Mem.table, Mem.interactions_eq, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with e | e | e | e <;> subst e <;>
    simp [Mem.iFin, Mem.iTime, Mem.iSf, B_SOP, B_SFIN, B_SCMP] at hb' hs'
  refine ⟨r', hr', ?_, hmsg⟩
  rw [Mem.multNat_c (i := Mem.iOp) rfl] at hm'
  by_cases h : cv tr tm r' Mem.act = 1
  · exact h
  · simp [h] at hm'

/-! ## Multisets -/

/-- All `SOP` messages sent by the tables, with multiplicity. -/
def sopSent (AP : AirP) (tr : Trace Fp) (pub : List Fp) : List (List Fp) :=
  busTraffic tr pub B_SOP true AP.tables 0

theorem sopSent_count (m : List Fp) : (sopSent AP tr pub).count m = busCount AP.toAir tr pub B_SOP true m :=
  count_busTraffic tr pub B_SOP true m AP.tables 0

/-- The messages received by the active memory rows are, as a multiset, the messages sent on `SOP`. -/
theorem mem_recv_perm (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) :
    (memRecv tr tm pub).Perm (sopSent AP tr pub) :=
  List.perm_iff_count.2 fun m => by rw [mem_recv_eq_sent hH hM, sopSent_count]

/-- `op ∈ {1, 2}` (READ or GRANT). -/
def isOpMsg (m : List Fp) : Bool := decide (m[2]? = some 1 ∨ m[2]? = some 2)

/-- **`mem_ops_eq_sent`, multiset form**: the `SOP` messages received on the non-`INIT` memory rows
are, as a multiset, the `SOP` messages with op ∈ {1, 2} sent by all tables. -/
theorem mem_ops_perm (hH : HoldsP AP pub tr) {tm : Nat} (hM : MemOwn AP tm) :
    (memOpRecv tr tm pub).Perm ((sopSent AP tr pub).filter isOpMsg) := by
  refine List.perm_iff_count.2 fun m => ?_
  by_cases hop : isOpMsg m = true
  · rw [List.count_filter hop, sopSent_count]
    exact mem_ops_eq_sent hH hM m (by simpa [isOpMsg] using hop)
  · rw [List.count_eq_zero.2 (fun h => hop (List.mem_filter.1 h).2), List.count_eq_zero]
    intro h
    obtain ⟨r, hr, hm⟩ := List.mem_filterMap.1 h
    have hr' := List.mem_range.1 hr
    by_cases hc : cv tr tm r Mem.act = 1 ∧ cv tr tm r Mem.fst = 0
    · simp only [hc.1, hc.2, and_self, ↓reduceIte] at hm
      have := (Mem.op_row (mLocal_of hH hM) hr' hc.1 hc.2).2
      rw [Option.some.inj hm] at this
      exact hop (by simpa [isOpMsg] using this)
    · simp [hc] at hm

end ZkFormal.NearV3.Sched

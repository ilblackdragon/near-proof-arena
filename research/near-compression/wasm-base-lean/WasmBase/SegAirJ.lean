import WasmBase.SegAirMP
/-!
# WasmBase.SegAirJ — the joined segment AIR (`wasmBaseSegAirMPJ`, E2E A-T1 item 5, the M6 join)

In the joined segment lane B's state rows (`StateM5a.StwH` / `StbH`) sit on lane A's host buses
HOSTQ 208 / HOSTR 209 / HOSTB 210 and answer the storage calls `storage_write` (id 58) and
`storage_remove` (id 60).  `wasmBaseSegAirMPJ` is `wasmBaseSegAirMP` (whose `HOSTB` already carries
the linear-memory address on bus 210, `Seg.HostBK.msgM`) with two tables changed:

* **HOSTO (23) → `HostOJ`**: `HOSTO`'s columns plus `w` (last); one constraint
  `mult · (1 − w · (q1 − 58) · (q1 − 60)) = 0` (`q1` the request's `hid`).  An oracle row that
  answers (`mult ≠ 0`) has `(q1 − 58)(q1 − 60)` invertible, so the in-trace oracle cannot answer a
  storage call: lane B's `STWH` row must.  Interactions unchanged.
* **HOSTB (25) → `HostBJ`**: `HostBK`'s columns plus `stg`, `sw` (last, in that order);
  constraints `HostBK`'s plus `bool stg`, `stg·(hid − 58)·(hid − 60) = 0`,
  `(1 − stg)·(1 − sw·(hid − 58)·(hid − 60)) = 0`, so `stg = 1 ↔ hid ∈ {58, 60}` (`hid` the base id);
  the state-side receive of request bytes (interaction 1) gets count `act·(1−dir)·(1−reg)·(1−stg)`:
  a storage call's request bytes are consumed by lane B's `STBH` rows, not by `HOSTB` itself.

Everything else is `wasmBaseSegAirMP`'s.  Proved here: the table-level difference
(`segMPJ_same`, `segMPJ_t23`, `segMPJ_t25`, `HostBJ.inters_eq_set`, `HostBJ.inters_filter`),
`hostOJ_no_storage`, `hostBJ_stg_iff`, and non-vacuity of the new constraints (`decide`).
The join obligation on lane B is `Main/HostJoin.lean` (`StorageJoinObl`).
-/
namespace WasmBase
namespace Chips
namespace Seg

/-! ## HOSTO in the joined segment: no answers to storage calls -/

namespace HostOJ
/-- The inverse witness of `(q1 − 58)(q1 − 60)` (the oracle's `hid` column is `HostO.q 1`). -/
def w : Nat := 33
def cols : List String := HostO.cols ++ ["w"]
theorem cols_len : cols.length = 34 := by decide
theorem w_name : cols[w]? = some "w" := by decide
/-- The storage selector polynomial of the request's `hid`: zero exactly at 58 and 60. -/
def stgPoly : Expr := (v (HostO.q 1) - 58) * (v (HostO.q 1) - 60)
/-- **An answering oracle row is not a storage call**: `mult · (1 − w·(q1−58)(q1−60)) = 0`
(degree 4). -/
def cNoStg : Expr := v HostO.mult * (1 - v w * stgPoly)
def constraints : List Expr := [cNoStg]
def inters : List Inter := HostO.inters
def table : Table := ⟨"HOSTO", cols, constraints, inters⟩
theorem inters_eq : table.inters = HostO.table.inters := rfl
theorem cols_prefix : HostO.cols <+: cols := List.prefix_append _ _
/-- `HOSTO` had no constraints, so the only one is the new one. -/
theorem constraints_eq : table.constraints = HostO.table.constraints ++ [cNoStg] := rfl
end HostOJ

/-! ## HOSTB in the joined segment: storage request bytes go to lane B -/

namespace HostBJ
/-- `stg = 1` iff the byte belongs to a storage call (`hid ∈ {58, 60}`). -/
def stg : Nat := 17
/-- The inverse witness of `(hid − 58)(hid − 60)` on a non-storage row. -/
def sw : Nat := 18
def cols : List String := HostBK.cols ++ ["stg", "sw"]
theorem cols_len : cols.length = 19 := by decide
theorem stg_name : cols[stg]? = some "stg" := by decide
theorem sw_name : cols[sw]? = some "sw" := by decide
def stgPoly : Expr := (v HostB.hid - 58) * (v HostB.hid - 60)
def cStgB : Expr := bool (v stg)
/-- `stg = 1 → hid ∈ {58, 60}` (degree 3). -/
def cStg : Expr := v stg * stgPoly
/-- `stg = 0 → hid ∉ {58, 60}` (degree 4). -/
def cStgN : Expr := (1 - v stg) * (1 - v sw * stgPoly)
def newConstraints : List Expr := [cStgB, cStg, cStgN]
def constraints : List Expr := HostBK.constraints ++ newConstraints
/-- The state-side receive of a request byte, off for storage calls (degree 4). -/
def reqRecvCnt : Expr := v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg) * (1 - v stg)
def reqRecv : Inter := ⟨busHostB, false, reqRecvCnt, HostBK.msgM⟩
/-- `HostBK.wireInters` with interaction 1 (the state-side receive of a request byte) gated by
`1 − stg`. -/
def wireInters : List Inter :=
  [⟨busHostB, true, v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg), HostBK.msgM⟩,
   reqRecv,
   ⟨busHostB, true, v HostB.act * v HostB.dir * (1 - v HostB.reg), HostBK.msgM⟩,
   ⟨busHostB, false, v HostB.act * v HostB.dir * (1 - v HostB.reg), HostBK.msgM⟩,
   ⟨busHostB, true, v HostB.act * v HostB.reg, HostBK.msgW⟩] ++ HostB.inters.drop 5
def inters : List Inter := wireInters ++ [HostBK.keySend] ++ HostBK.writeInters
def table : Table := ⟨"HOSTB", cols, constraints, inters⟩

theorem cols_prefix : HostBK.cols <+: cols := List.prefix_append _ _
theorem constraints_prefix : HostBK.constraints <+: constraints := List.prefix_append _ _
theorem inters_len : inters.length = HostBK.inters.length := by decide
theorem inters_len20 : inters.length = 20 := by decide

/-- **`HostBJ`'s interactions are `HostBK`'s with interaction 1 replaced** by the gated receive. -/
theorem inters_eq_set : inters = HostBK.inters.set 1 reqRecv := by decide

/-- Interaction 1 of `HostBK` is the ungated state-side receive of a request byte. -/
theorem hostBK_inter1 : HostBK.inters[1]? =
    some ⟨busHostB, false, v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg), HostBK.msgM⟩ := by
  decide

/-- Every interaction but index 1 is `HostBK`'s. -/
theorem inters_same (i : Nat) (hi : i ≠ 1) : inters[i]? = HostBK.inters[i]? := by
  rw [inters_eq_set, List.getElem?_set_ne (Ne.symm hi)]

/-- **Only the receives on bus 210 differ**: every other (bus, direction) sees `HostBK`'s
interactions. -/
theorem inters_filter (b : Nat) (s : Bool) (h : ¬ (b = busHostB ∧ s = false)) :
    inters.filter (fun i => i.bus = b ∧ i.send = s) = HostBK.inters.filter (fun i => i.bus = b ∧ i.send = s) := by
  have e1 : inters = wireInters.take 1 ++ [reqRecv] ++ (wireInters.drop 2 ++ [HostBK.keySend] ++ HostBK.writeInters) := by
    decide
  have e2 : HostBK.inters = wireInters.take 1 ++
      [⟨busHostB, false, v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg), HostBK.msgM⟩] ++
      (wireInters.drop 2 ++ [HostBK.keySend] ++ HostBK.writeInters) := by decide
  rw [e1, e2]
  simp only [List.filter_append]
  congr 1; congr 1
  by_cases hb : b = busHostB
  · subst hb
    have hs : s = true := by cases s <;> simp_all
    subst hs; simp [reqRecv]
  · simp [reqRecv, Ne.symm hb]

/-- On bus 210, direction receive, the two tables differ in interaction 1's count only. -/
theorem inters_filter_recv :
    inters.filter (fun i => i.bus = busHostB ∧ i.send = false) =
      [reqRecv, ⟨busHostB, false, v HostB.act * v HostB.dir * (1 - v HostB.reg), HostBK.msgM⟩] := by
  decide
theorem hostBK_filter_recv :
    HostBK.inters.filter (fun i => i.bus = busHostB ∧ i.send = false) =
      [⟨busHostB, false, v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg), HostBK.msgM⟩,
       ⟨busHostB, false, v HostB.act * v HostB.dir * (1 - v HostB.reg), HostBK.msgM⟩] := by
  decide
end HostBJ

end Seg
end Chips

open Chips in
/-- **The joined E2E segment AIR**: `wasmBaseSegAirMP` with `HOSTO` (23) → `Seg.HostOJ.table` and
`HOSTB` (25) → `Seg.HostBJ.table`.  The standalone `wasmBaseSegAirMP` is unchanged. -/
def wasmBaseSegAirMPJ (nloc ngl : Nat) : Air where
  tables := ((wasmBaseSegAirMP nloc ngl).tables.set 23 Seg.HostOJ.table).set 25 Seg.HostBJ.table
  numPub := Seg.numPub

theorem segMPJ_len (nloc ngl : Nat) : (wasmBaseSegAirMPJ nloc ngl).tables.length = 32 := by
  simp [wasmBaseSegAirMPJ, segMP_len]

theorem segMPJ_numPub (nloc ngl : Nat) :
    (wasmBaseSegAirMPJ nloc ngl).numPub = (wasmBaseSegAirMP nloc ngl).numPub := rfl

/-- **Every table but HOSTO (23) and HOSTB (25) is `wasmBaseSegAirMP`'s**, at the same index. -/
theorem segMPJ_same (nloc ngl t : Nat) (h23 : t ≠ 23) (h25 : t ≠ 25) :
    (wasmBaseSegAirMPJ nloc ngl).tables[t]? = (wasmBaseSegAirMP nloc ngl).tables[t]? := by
  simp [wasmBaseSegAirMPJ, Ne.symm h23, Ne.symm h25]

theorem segMPJ_t23 (nloc ngl : Nat) :
    (wasmBaseSegAirMPJ nloc ngl).tables[23]? = some Chips.Seg.HostOJ.table := by
  simp [wasmBaseSegAirMPJ, segMP_len]

theorem segMPJ_t25 (nloc ngl : Nat) :
    (wasmBaseSegAirMPJ nloc ngl).tables[25]? = some Chips.Seg.HostBJ.table := by
  simp [wasmBaseSegAirMPJ, segMP_len]

theorem segMP_t23 (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables[23]? = some Chips.HostO.table := by
  rw [segMP_same nloc ngl 23 (by decide)]; simp [wasmBaseSegAir]

theorem segMP_t25 (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables[25]? = some Chips.Seg.HostBK.table := by
  rw [segMP_same nloc ngl 25 (by decide)]; simp [wasmBaseSegAir]

theorem segMPJ_t23' (nloc ngl : Nat) :
    (wasmBaseSegAirMPJ nloc ngl).tables[23]'(by rw [segMPJ_len]; decide) = Chips.Seg.HostOJ.table := by
  have := segMPJ_t23 nloc ngl
  rw [List.getElem?_eq_getElem (by rw [segMPJ_len]; decide)] at this
  exact Option.some.inj this

theorem segMPJ_t25' (nloc ngl : Nat) :
    (wasmBaseSegAirMPJ nloc ngl).tables[25]'(by rw [segMPJ_len]; decide) = Chips.Seg.HostBJ.table := by
  have := segMPJ_t25 nloc ngl
  rw [List.getElem?_eq_getElem (by rw [segMPJ_len]; decide)] at this
  exact Option.some.inj this

/-- **The interactions of the joined AIR, table by table**: the same as `wasmBaseSegAirMP`'s on
every table except HOSTB, where only the receives on bus 210 differ (`HostBJ.inters_filter`). -/
theorem segMPJ_inters_filter (nloc ngl t b : Nat) (s : Bool) (h : ¬ (t = 25 ∧ b = Chips.busHostB ∧ s = false)) :
    ((wasmBaseSegAirMPJ nloc ngl).tables[t]?.map fun T => T.inters.filter fun i => i.bus = b ∧ i.send = s) =
      ((wasmBaseSegAirMP nloc ngl).tables[t]?.map fun T => T.inters.filter fun i => i.bus = b ∧ i.send = s) := by
  by_cases h25 : t = 25
  · subst h25
    rw [segMPJ_t25, segMP_t25]
    simp only [Option.map_some]
    rw [Chips.Seg.HostBJ.table, Chips.Seg.HostBK.table]
    simp only
    rw [Chips.Seg.HostBJ.inters_filter b s (by intro hh; exact h ⟨rfl, hh⟩)]
  by_cases h23 : t = 23
  · subst h23
    rw [segMPJ_t23, segMP_t23]; rfl
  rw [segMPJ_same nloc ngl t h23 h25]

/-! ## The new constraints: what they force -/

section Facts
open Chips Seg
variable {nloc ngl : Nat} {pub : List F} {tr : Trace}

/-- Row-level: an answering oracle row's `hid` is not 58 or 60. -/
theorem hostOJ_row_no_storage (rw : Row) (h : HostOJ.cNoStg.eval rw = 0) (hm : rw.cur HostO.mult ≠ 0) :
    rw.cur (HostO.q 1) ≠ 58 ∧ rw.cur (HostO.q 1) ≠ 60 := by
  simp only [HostOJ.cNoStg, HostOJ.stgPoly, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat'] at h
  rcases mul_eq_zero' h with h | h
  · exact absurd h hm
  · constructor <;> intro he <;> rw [he] at h <;> grind

/-- **`hostOJ_no_storage`**: in a trace of the joined AIR, an active `HOSTO` row (`mult ≠ 0`) is not
a storage call: its request `hid` is neither 58 (`storage_write`) nor 60 (`storage_remove`). -/
theorem hostOJ_no_storage (H : Holds (wasmBaseSegAirMPJ nloc ngl) pub tr) {r : Nat}
    (hr : r < tr.height 23) (hm : tr.cell 23 r HostO.mult ≠ 0) :
    tr.cell 23 r (HostO.q 1) ≠ 58 ∧ tr.cell 23 r (HostO.q 1) ≠ 60 := by
  have h := H.constr 23 (by rw [segMPJ_len]; decide) r hr HostOJ.cNoStg (by
    rw [segMPJ_t23']; simp [HostOJ.table, HostOJ.constraints])
  exact hostOJ_row_no_storage _ h hm

/-- The same, on naturals. -/
theorem hostOJ_no_storage_nat (H : Holds (wasmBaseSegAirMPJ nloc ngl) pub tr) {r : Nat}
    (hr : r < tr.height 23) (hm : tr.cell 23 r HostO.mult ≠ 0) :
    (tr.cell 23 r (HostO.q 1)).toNat ≠ 58 ∧ (tr.cell 23 r (HostO.q 1)).toNat ≠ 60 := by
  obtain ⟨h1, h2⟩ := hostOJ_no_storage H hr hm
  refine ⟨fun e => h1 ?_, fun e => h2 ?_⟩
  · rw [eq_of_toNat e]; rfl
  · rw [eq_of_toNat e]; rfl

/-- Row-level: the three new `HOSTB` constraints make `stg` the indicator of `hid ∈ {58, 60}`. -/
theorem hostBJ_row_stg_iff (rw : Row) (h1 : HostBJ.cStg.eval rw = 0) (h2 : HostBJ.cStgN.eval rw = 0) :
    rw.cur HostBJ.stg = 1 ↔ (rw.cur HostB.hid = 58 ∨ rw.cur HostB.hid = 60) := by
  simp only [HostBJ.cStg, HostBJ.cStgN, HostBJ.stgPoly, Chips.v, Expr.eval_mul', Expr.eval_sub',
    Expr.eval_col, Expr.eval_ofNat'] at h1 h2
  constructor
  · intro hs
    rw [hs] at h1
    rcases mul_eq_zero' h1 with h | h
    · grind
    · rcases mul_eq_zero' h with h | h
      · left; grind
      · right; grind
  · intro hh
    have hz : (rw.cur HostB.hid - ((58 : Nat) : F)) * (rw.cur HostB.hid - ((60 : Nat) : F)) = 0 := by
      rcases hh with hh | hh <;> rw [hh] <;> decide
    rw [hz] at h2
    grind

/-- **`hostBJ_stg_iff`**: on every row of `HOSTB` in the joined AIR, `stg = 1 ↔ hid ∈ {58, 60}`. -/
theorem hostBJ_stg_iff (H : Holds (wasmBaseSegAirMPJ nloc ngl) pub tr) {r : Nat}
    (hr : r < tr.height 25) :
    tr.cell 25 r HostBJ.stg = 1 ↔ (tr.cell 25 r HostB.hid = 58 ∨ tr.cell 25 r HostB.hid = 60) := by
  have mem : ∀ e ∈ HostBJ.newConstraints,
      e ∈ ((wasmBaseSegAirMPJ nloc ngl).tables[25]'(by rw [segMPJ_len]; decide)).constraints := by
    intro e he; rw [segMPJ_t25']; exact List.mem_append_right _ he
  have h1 := H.constr 25 (by rw [segMPJ_len]; decide) r hr HostBJ.cStg (mem _ (by simp [HostBJ.newConstraints]))
  have h2 := H.constr 25 (by rw [segMPJ_len]; decide) r hr HostBJ.cStgN (mem _ (by simp [HostBJ.newConstraints]))
  exact hostBJ_row_stg_iff _ h1 h2

/-- `stg` is a bit on every `HOSTB` row of the joined AIR. -/
theorem hostBJ_stg_bit (H : Holds (wasmBaseSegAirMPJ nloc ngl) pub tr) {r : Nat}
    (hr : r < tr.height 25) : tr.cell 25 r HostBJ.stg = 0 ∨ tr.cell 25 r HostBJ.stg = 1 := by
  have h := H.constr 25 (by rw [segMPJ_len]; decide) r hr HostBJ.cStgB (by
    rw [segMPJ_t25']; exact List.mem_append_right _ (by simp [HostBJ.newConstraints]))
  simp only [HostBJ.cStgB, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat'] at h
  exact bool_cases h

/-- On a non-storage `HOSTB` row (`hid ∉ {58, 60}`) the gated receive count is `HostBK`'s. -/
theorem hostBJ_reqRecv_nonstg (H : Holds (wasmBaseSegAirMPJ nloc ngl) pub tr) {r : Nat}
    (hr : r < tr.height 25) (h58 : tr.cell 25 r HostB.hid ≠ 58) (h60 : tr.cell 25 r HostB.hid ≠ 60) :
    HostBJ.reqRecvCnt.eval (tr.row pub 25 r) =
      (v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg)).eval (tr.row pub 25 r) := by
  have hs : tr.cell 25 r HostBJ.stg = 0 := by
    rcases hostBJ_stg_bit H hr with h | h
    · exact h
    · rcases (hostBJ_stg_iff H hr).1 h with e | e <;> contradiction
  simp only [HostBJ.reqRecvCnt, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row, hs]
  grind

/-- On a storage `HOSTB` row the gated receive count is `0`: `HOSTB` does not consume its own
request bytes. -/
theorem hostBJ_reqRecv_stg (H : Holds (wasmBaseSegAirMPJ nloc ngl) pub tr) {r : Nat}
    (hr : r < tr.height 25) (hh : tr.cell 25 r HostB.hid = 58 ∨ tr.cell 25 r HostB.hid = 60) :
    HostBJ.reqRecvCnt.eval (tr.row pub 25 r) = 0 := by
  have hs := (hostBJ_stg_iff H hr).2 hh
  simp only [HostBJ.reqRecvCnt, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row, hs]
  grind

end Facts

/-! ## Non-vacuity: honest rows satisfy the new constraints -/

namespace JoinCheck
open Chips Seg

/-- A row from an explicit column assignment (next row all zero, no publics). -/
def rowOf (f : Nat → F) : Row := ⟨f, fun _ => 0, fun _ => 0, false, false⟩

/-- `(48 − 58)(48 − 60) = 120`, and `120⁻¹ = 1996488705` in the BabyBear field. -/
def inv120 : Nat := 1996488705
theorem inv120_ok : ((120 : Nat) : F) * ((inv120 : Nat) : F) = 1 := by decide

/-- An honest `HOSTO` row of an `input` call (`hid = 48`, answered: `mult = 1`, `w = 120⁻¹`). -/
def hostoInput : Row := rowOf fun c =>
  if c = HostO.q 1 then 48 else if c = HostO.mult then 1 else if c = HostOJ.w then ((inv120 : Nat) : F) else 0
/-- An honest `HOSTO` row in a joined trace at a `storage_write` call: the oracle does not answer
(`mult = 0`; `w` arbitrary). -/
def hostoWrite : Row := rowOf fun c => if c = HostO.q 1 then 58 else 0
/-- The mutant: the oracle answers a `storage_write` (`mult = 1`), for any `w`. -/
def hostoWriteAns (w : F) : Row := rowOf fun c =>
  if c = HostO.q 1 then 58 else if c = HostO.mult then 1 else if c = HostOJ.w then w else 0

theorem hostoInput_ok : ∀ e ∈ HostOJ.table.constraints, e.eval hostoInput = 0 := by decide +kernel
theorem hostoWrite_ok : ∀ e ∈ HostOJ.table.constraints, e.eval hostoWrite = 0 := by decide +kernel
/-- **The oracle cannot answer a storage call**, whatever `w` it picks. -/
theorem hostoWriteAns_rejected (w : F) : HostOJ.cNoStg.eval (hostoWriteAns w) ≠ 0 := by
  intro h
  have hm : (hostoWriteAns w).cur HostO.mult = 1 := rfl
  have hq : (hostoWriteAns w).cur (HostO.q 1) = 58 := rfl
  have := hostOJ_row_no_storage _ h (by rw [hm]; decide)
  exact this.1 hq

/-- An honest `HOSTB` request byte of a `storage_write` call (key byte 0x61 at `ptr = 100`,
`pos = 2`, `stg = 1`, `sw = 0`). -/
def hostbWrite : Row := rowOf fun c =>
  if c = HostB.ts then 10 else if c = HostB.pos then 2 else if c = HostB.bv then 0x61
  else if c = HostB.blen then 4 else if c = HostB.hid then 58 else if c = HostB.gap then 1
  else if c = HostB.act then 1 else if c = HostB.ptrLo then 100 else if c = HostB.mtp then 5
  else if c = HostBJ.stg then 1 else 0
/-- An honest `HOSTB` register-fill byte of an `input` call (`hid = 48`, `dir = 1`, `reg = 1`,
`stg = 0`, `sw = 120⁻¹`). -/
def hostbInput : Row := rowOf fun c =>
  if c = HostB.ts then 12 else if c = HostB.dir then 1 else if c = HostB.bv then 7
  else if c = HostB.blen then 3 else if c = HostB.hid then 48 else if c = HostB.gap then 2
  else if c = HostB.act then 1 else if c = HostB.reg then 1
  else if c = HostBJ.sw then ((inv120 : Nat) : F) else 0

theorem hostbWrite_ok : ∀ e ∈ HostBJ.newConstraints, e.eval hostbWrite = 0 := by decide +kernel
theorem hostbInput_ok : ∀ e ∈ HostBJ.newConstraints, e.eval hostbInput = 0 := by decide +kernel
/-- At the honest storage byte the state-side receive is off (`0`) and the send is on (`1`), with the
absolute address `ptr + pos = 102` on the bus. -/
theorem hostbWrite_bus : HostBJ.reqRecvCnt.eval hostbWrite = 0 ∧
    (v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg)).eval hostbWrite = 1 ∧
    HostBK.msgM.map (·.eval hostbWrite) = [10, 58, 0, 102, 0x61] := by decide +kernel
/-- At the honest `input` byte the gated receive equals the standalone one (`0` here: a register
byte) and `stg = 0`. -/
theorem hostbInput_bus : HostBJ.reqRecvCnt.eval hostbInput = 0 ∧ hostbInput.cur HostBJ.stg = 0 := by
  decide +kernel
/-- A storage byte (`hid = 58`) claiming `stg = 0`, with any `sw`. -/
def hostbStg0 (sw : F) : Row := rowOf fun c => if c = HostB.hid then 58 else if c = HostBJ.sw then sw else 0
/-- The mutant: a storage byte claiming `stg = 0` violates `cStgN` for every `sw`. -/
theorem hostbWrite_stg0_rejected (sw : F) : HostBJ.cStgN.eval (hostbStg0 sw) ≠ 0 := by
  intro h
  have h0 : (hostbStg0 sw).cur HostBJ.stg = 0 := rfl
  have hq : (hostbStg0 sw).cur HostB.hid = 58 := rfl
  have h1 : HostBJ.cStg.eval (hostbStg0 sw) = 0 := by
    simp only [HostBJ.cStg, Chips.v, Expr.eval_mul', Expr.eval_col, h0]; grind
  have := (hostBJ_row_stg_iff _ h1 h).2 (Or.inl hq)
  rw [h0] at this
  exact absurd this (by decide)

end JoinCheck

end WasmBase

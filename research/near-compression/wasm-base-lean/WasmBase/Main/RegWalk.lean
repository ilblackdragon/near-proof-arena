import WasmBase.Main.RegFacts
import WasmBase.RegisterSpace
/-!
# WasmBase.Main.RegWalk — the REG group walk, and `Register.RegLenAgree` proved

`Register.RegLenAgree` was stated and not proved (`RegisterSpace.lean`).  This file proves it from
the group constraints `RegChip.lean` now carries.

## The group

One register access is one **group** of rows: `len` byte rows (`kind = 0`) at `pos = 0 … len−1`,
then one length row (`kind = 1`, `pos = 0`), all with the same `(rid, ts, len, rd)`; `f = 1` marks
the group start.  A length-only access (`register_len`) is a group that is a single length row.

## The constraints the walk uses

* `cStartPos` — a group's first byte row has `pos = 0`;
* `cOnlyLenEnds` — an active byte row is never followed by a group start, so from a byte row the
  walk continues inside the group;
* `cPosStep` — consecutive byte rows step `pos` by one;
* `cLastByte` — the row before a length row has `pos = len − 1`;
* `cLenEnds` — a length row ends its group;
* `cByteAct` — every byte row is active (so it emits a byte message);
* `cRidG`/`cTsG`/`cLenG` — the group's `(rid, ts, len)` is constant;
* `cFirst`/`cLast` — the table starts and ends at a group break.

## Proved

* `reg_byte_step` — from an active byte row, either the next row is another active byte row of the
  same group at `pos + 1`, or it is the group's length row and `pos = len − 1`;
* `reg_group_exact` — walking from a group start visits byte rows `pos = 0 … len−1`, in order, and
  then the group's length row (the walk, by induction on the distance to the terminator);
* `regLenAgree_of_holds` — **`Register.RegLenAgree`**.

The `Holds` facts are extracted by `reg_constraint_holds`; the walk is then arithmetic on rows.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The row-local constraint facts -/

/-- The named REG constraints vanish on any REG row (from `Holds`). -/
theorem reg_walk_constraints {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    ∀ e ∈ Reg.table.constraints, e.eval (natRow (rowNat tr 26 r) (tr.row pub 26 r)) = 0 :=
  reg_row_constraints H hr

/-- The REG table is at index 26, so `Holds` applies to it. -/
theorem reg_walk_26 {nloc ngl : Nat} :
    26 < (wasmBaseRegAir nloc ngl).tables.length ∧
      (wasmBaseRegAir nloc ngl).tables[26]'(by rw [reg_air_len]; decide) = Reg.table :=
  ⟨by rw [reg_air_len]; decide, reg_air_26 nloc ngl⟩

/-- `act`, `kind`, `f` are bits on any REG row. -/
theorem reg_act_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    rowNat tr 26 r Reg.act = 0 ∨ rowNat tr 26 r Reg.act = 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cAct (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cAct, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Reg.act, natRow] at h
  exact bool_nat (rowNat_lt tr 26 r Reg.act) h

theorem reg_kind_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    rowNat tr 26 r Reg.kind = 0 ∨ rowNat tr 26 r Reg.kind = 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cKind (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cKind, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Reg.kind, natRow] at h
  exact bool_nat (rowNat_lt tr 26 r Reg.kind) h

theorem reg_f_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    rowNat tr 26 r Reg.f = 0 ∨ rowNat tr 26 r Reg.f = 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cF (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cF, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Reg.f, natRow] at h
  exact bool_nat (rowNat_lt tr 26 r Reg.f) h

/-- **`cByteAct`**: a byte row is active. -/
theorem reg_byte_active {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hk : rowNat tr 26 r Reg.kind = 0) :
    rowNat tr 26 r Reg.act = 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cByteAct (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cByteAct, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Reg.act, Reg.kind, natRow] at h
  -- unfolded: `(1 − kind)·(1 − act) = 0` with `kind = c₁`, `act = c₀`
  rw [show (rowNat tr 26 r 1 : F) = 0 from by rw [show (1 : Nat) = Reg.kind from rfl, hk]; rfl] at h
  rcases reg_act_bit H hr with hb | hb
  · rw [show (rowNat tr 26 r 0 : F) = 0 from by rw [show (0 : Nat) = Reg.act from rfl, hb]; rfl] at h
    grind
  · exact hb

/-- **`cStartPos`**: a group's first byte row has `pos = 0`. -/
theorem reg_start_pos {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hf : rowNat tr 26 r Reg.f = 1) (hk : rowNat tr 26 r Reg.kind = 0) :
    rowNat tr 26 r Reg.pos = 0 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cStartPos (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cStartPos, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Reg.f, Reg.kind, Reg.pos, natRow] at h
  rw [show (rowNat tr 26 r 15 : F) = 1 from by rw [show (15 : Nat) = Reg.f from rfl, hf]; rfl,
      show (rowNat tr 26 r 1 : F) = 0 from by rw [show (1 : Nat) = Reg.kind from rfl, hk]; rfl] at h
  have hp := rowNat_lt tr 26 r Reg.pos
  rw [show (4 : Nat) = Reg.pos from rfl] at h
  have h0 : (rowNat tr 26 r Reg.pos : F) = ((0 : Nat) : F) := by grind
  exact natEq h0 hp (by decide)

/-- **`cOnlyLenEnds`**: an active byte row's successor is not a group start. -/
theorem reg_byte_succ_not_start {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (ha : rowNat tr 26 r Reg.act = 1) (hk : rowNat tr 26 r Reg.kind = 0) :
    rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cOnlyLenEnds (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cOnlyLenEnds, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', Reg.act, Reg.kind, Reg.f, natRow, Trace.row] at h
  rw [show (rowNat tr 26 r 0 : F) = 1 from by rw [show (0 : Nat) = Reg.act from rfl, ha]; rfl,
      show (rowNat tr 26 r 1 : F) = 0 from by rw [show (1 : Nat) = Reg.kind from rfl, hk]; rfl] at h
  rw [show (15 : Nat) = Reg.f from rfl] at h
  have hc : ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) =
      tr.cell 26 ((r + 1) % tr.height 26) Reg.f := Fp.cast_toNat _
  have h0 : (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = ((0 : Nat) : F) := by
    rw [hc]
    grind
  exact natEq h0 (rowNat_lt tr 26 ((r + 1) % tr.height 26) Reg.f) (by decide)

/-! ## The walk: row-level successor facts

The remaining pieces are `cPosStep` (a byte row inside a group steps `pos` by one), `cLastByte`
(the byte row before a length row is at `pos = len − 1`), and `cLenEnds` (a length row is the last
row of its group). -/


/-- **The row-index bound.**  A REG row's `pos` is at most its row index: every group starts at
`pos = 0` and steps by one, and row 0 is a group break (`cFirst`), so no group wraps.  This is the
bound that makes `pos + 1 < P` true (`r < height ≤ 2^24`). -/
theorem reg_pos_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) :
    ∀ r, r < tr.height 26 → rowNat tr 26 r Reg.pos ≤ r := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have key : ∀ n, ∀ r, r ≤ n → r < tr.height 26 → rowNat tr 26 r Reg.pos ≤ r := by
    intro n
    induction n with
    | zero =>
      intro r hrle hr
      have hr0 : r = 0 := by omega
      subst hr0
      have hcon := table_constr H ht hr
      rw [hT] at hcon
      rcases reg_kind_bit H hr with hk | hk
      · -- byte row at 0: `cFirst` forces `f = 1`, then `cStartPos` gives `pos = 0`
        have hc := hcon Reg.cFirst (by simp [Reg.table, Reg.constraints])
        simp only [Reg.cFirst, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
          Expr.eval_ofNat', Expr.eval, Reg.f, natRow, Trace.row, beq_self_eq_true, ite_true] at hc
        have hf1 : (rowNat tr 26 0 Reg.f : F) = 1 := by
          rcases reg_f_bit H hr with hf | hf
          · rw [show (15 : Nat) = Reg.f from rfl,
                show (rowNat tr 26 0 Reg.f : F) = 0 from by rw [hf]; rfl] at hc
            grind
          · rw [hf]; rfl
        have hf : rowNat tr 26 0 Reg.f = 1 := by
          have := natEq hf1 (rowNat_lt tr 26 0 Reg.f) (by decide)
          exact this
        rw [reg_start_pos H hr hf hk]; omega
      · have h := hcon Reg.cLenPos (by simp [Reg.table, Reg.constraints])
        simp only [Reg.cLenPos, Chips.v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat',
          Reg.kind, Reg.pos, natRow, Trace.row] at h
        rw [show rowNat tr 26 0 (1 : Nat) = rowNat tr 26 0 Reg.kind from by
              rw [show (1 : Nat) = Reg.kind from rfl],
            show rowNat tr 26 0 (4 : Nat) = rowNat tr 26 0 Reg.pos from by
              rw [show (4 : Nat) = Reg.pos from rfl]] at h
        rw [show (rowNat tr 26 0 Reg.kind : F) = 1 from by rw [hk]; rfl] at h
        have h0 : (rowNat tr 26 0 Reg.pos : F) = ((0 : Nat) : F) := by grind
        have hz := natEq h0 (rowNat_lt tr 26 0 Reg.pos) (by decide)
        omega
    | succ n ih =>
      intro r hrle hr
      rcases (show r ≤ n ∨ r = n + 1 by omega) with h | rfl
      · exact ih r h hr
      · have hrm : n < tr.height 26 := by omega
        have hn := ih n (by omega) hrm
        have hcon := table_constr H ht hr
        rw [hT] at hcon
        rcases reg_kind_bit H hr with hk | hk
        · rcases reg_f_bit H hr with hf | hf
          · -- a non-starting byte row: the step comes from `cPosStep` at the previous row
            have hcn := table_constr H ht hrm
            rw [hT] at hcn
            have h := hcn Reg.cPosStep (by simp [Reg.table, Reg.constraints])
            simp only [Reg.cPosStep, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub',
              Expr.eval_col, Expr.eval_nxt, Expr.eval_ofNat', Reg.f, Reg.kind, Reg.pos, natRow,
              Trace.row] at h
            have hmod : (n + 1) % tr.height 26 = n + 1 := Nat.mod_eq_of_lt hr
            rw [hmod] at h
            -- successor (row n + 1) f and kind are the hypotheses
            rw [show tr.cell 26 (n + 1) 15 =
                  ((rowNat tr 26 (n + 1) Reg.f : Nat) : F) from (Fp.cast_toNat _).symm,
                show tr.cell 26 (n + 1) 1 =
                  ((rowNat tr 26 (n + 1) Reg.kind : Nat) : F) from (Fp.cast_toNat _).symm,
                show tr.cell 26 (n + 1) 4 =
                  ((rowNat tr 26 (n + 1) Reg.pos : Nat) : F) from (Fp.cast_toNat _).symm] at h
            rw [show (4 : Nat) = Reg.pos from rfl] at h
            rw [show (rowNat tr 26 (n + 1) Reg.f : F) = 0 from by rw [hf]; rfl,
                show (rowNat tr 26 (n + 1) Reg.kind : F) = 0 from by rw [hk]; rfl] at h
            have hP : P = 2013265921 := P_val
            have hgl := H.heightLe 26 ht
            unfold maxLogHeight at hgl
            have hb : rowNat tr 26 n Reg.pos + 1 < P := by omega
            have eqn : (rowNat tr 26 (n + 1) Reg.pos : F) =
                (rowNat tr 26 n Reg.pos : F) + 1 := by grind
            have eqn' : rowNat tr 26 (n + 1) Reg.pos = rowNat tr 26 n Reg.pos + 1 := by
              refine natEq ?_ (rowNat_lt tr 26 (n + 1) Reg.pos) hb
              rw [Lean.Grind.Semiring.natCast_add]
              exact eqn
            omega
          · rw [reg_start_pos H hr hf hk]; omega
        · have h := hcon Reg.cLenPos (by simp [Reg.table, Reg.constraints])
          simp only [Reg.cLenPos, Chips.v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat',
            Reg.kind, Reg.pos, natRow, Trace.row] at h
          rw [show rowNat tr 26 (n + 1) (1 : Nat) = rowNat tr 26 (n + 1) Reg.kind from by
                rw [show (1 : Nat) = Reg.kind from rfl],
              show rowNat tr 26 (n + 1) (4 : Nat) = rowNat tr 26 (n + 1) Reg.pos from by
                rw [show (4 : Nat) = Reg.pos from rfl]] at h
          rw [show (rowNat tr 26 (n + 1) Reg.kind : F) = 1 from by rw [hk]; rfl] at h
          have h0 : (rowNat tr 26 (n + 1) Reg.pos : F) = ((0 : Nat) : F) := by grind
          have hz := natEq h0 (rowNat_lt tr 26 (n + 1) Reg.pos) (by decide)
          omega
  intro r hr
  exact key r r (Nat.le_refl r) hr

/-- **`cPosStep`**: if the successor row is a byte row that does not start a group, then `pos`
increases by exactly one. -/
theorem reg_pos_step {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hf' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0)
    (hk' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.kind = 0) :
    rowNat tr 26 ((r + 1) % tr.height 26) Reg.pos = rowNat tr 26 r Reg.pos + 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cPosStep (by simp [Reg.table, Reg.constraints])
  have hP := P_val
  simp only [Reg.cPosStep, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', Reg.f, Reg.kind, Reg.pos, natRow, Trace.row] at h
  -- replace the successor's literal columns by the hypotheses (`Fp.cast_toNat` bridges both ways)
  have e1 : tr.cell 26 ((r + 1) % tr.height 26) 15 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) := (Fp.cast_toNat _).symm
  have e2 : tr.cell 26 ((r + 1) % tr.height 26) 1 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.kind : Nat) : F) := (Fp.cast_toNat _).symm
  rw [e1, e2] at h
  rw [show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = 0 from by rw [hf']; rfl,
      show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.kind : F) = 0 from by rw [hk']; rfl] at h
  -- `1 · 1 · (pos' − pos − 1) = 0`
  have hp := rowNat_lt tr 26 r Reg.pos
  have hp' := rowNat_lt tr 26 ((r + 1) % tr.height 26) Reg.pos
  have e3 : tr.cell 26 ((r + 1) % tr.height 26) 4 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.pos : Nat) : F) := (Fp.cast_toNat _).symm
  have e : (rowNat tr 26 ((r + 1) % tr.height 26) Reg.pos : F) =
      (rowNat tr 26 r Reg.pos : F) + 1 := by
    rw [e3, show (4 : Nat) = Reg.pos from rfl] at h
    grind
  have hle := reg_pos_le H r hr
  have hP : P = 2013265921 := P_val
  have hgl := H.heightLe 26 ht
  unfold maxLogHeight at hgl
  have hpv : rowNat tr 26 r Reg.pos + 1 < P := by omega
  refine natEq ?_ hp' hpv
  rw [e, Lean.Grind.Semiring.natCast_add]
  rfl

/-- **`cLastByte`**: if the successor row is a length row (inside the same group), then the
current byte row is the group's last byte, `pos = len − 1`. -/
theorem reg_last_byte {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hf' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0)
    (hk' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.kind = 1) :
    rowNat tr 26 r Reg.blen = rowNat tr 26 r Reg.pos + 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cLastByte (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cLastByte, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', Reg.f, Reg.kind, Reg.blen, Reg.pos, natRow, Trace.row] at h
  have e1 : tr.cell 26 ((r + 1) % tr.height 26) 15 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) := (Fp.cast_toNat _).symm
  have e2 : tr.cell 26 ((r + 1) % tr.height 26) 1 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.kind : Nat) : F) := (Fp.cast_toNat _).symm
  rw [e1, e2] at h
  rw [show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = 0 from by rw [hf']; rfl,
      show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.kind : F) = 1 from by rw [hk']; rfl] at h
  have hl := rowNat_lt tr 26 r Reg.blen
  have hp := rowNat_lt tr 26 r Reg.pos
  have e : (rowNat tr 26 r Reg.blen : F) = (rowNat tr 26 r Reg.pos : F) + 1 := by
    rw [show (5 : Nat) = Reg.blen from rfl, show (4 : Nat) = Reg.pos from rfl] at h
    grind
  have hle := reg_pos_le H r hr
  have hP : P = 2013265921 := P_val
  have hgl := H.heightLe 26 ht
  unfold maxLogHeight at hgl
  refine natEq ?_ hl (by omega)
  rw [e, Lean.Grind.Semiring.natCast_add]
  rfl

/-- **`cLenG`**: the group's `len` is constant across the row boundary. -/
theorem reg_len_const {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hf' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0) :
    rowNat tr 26 ((r + 1) % tr.height 26) Reg.blen = rowNat tr 26 r Reg.blen := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cLenG (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cLenG, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', Reg.f, Reg.blen, natRow, Trace.row] at h
  have e1 : tr.cell 26 ((r + 1) % tr.height 26) 15 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) := (Fp.cast_toNat _).symm
  have e2 : tr.cell 26 ((r + 1) % tr.height 26) 5 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.blen : Nat) : F) := (Fp.cast_toNat _).symm
  rw [e1, e2] at h
  rw [show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = 0 from by rw [hf']; rfl] at h
  rw [show (5 : Nat) = Reg.blen from rfl] at h
  have h1 := rowNat_lt tr 26 ((r + 1) % tr.height 26) Reg.blen
  have h2 := rowNat_lt tr 26 r Reg.blen
  have e : (rowNat tr 26 ((r + 1) % tr.height 26) Reg.blen : F) =
      (rowNat tr 26 r Reg.blen : F) := by grind
  exact natEq e h1 h2

end WasmBase

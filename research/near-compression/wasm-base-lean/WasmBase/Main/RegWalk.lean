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

/-- The RANGE16-answer characterisation for a `wasmBaseRegAir` trace: an R16 **receive** is a
single value `< 2^16`.  This is the `hrecv` premise of `reg_r16_query_16bit`, mirroring
`Main/HostLinks.host_r16_sound`. -/
theorem reg_r16_recv {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) :
    ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 := by
  intro o ho hb hs hc
  obtain ⟨t, ht', r', hr', i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs hc
  -- every table other than RANGE16 *sends* R16, so a receive must be RANGE16
  have hT : (wasmBaseRegAir nloc ngl).tables[t]'ht' = Range16.table := by
    rcases Classical.em ((wasmBaseRegAir nloc ngl).tables[t]'ht' = Range16.table) with he | hne
    · exact he
    · exact absurd (reg_recv_only_range16 nloc ngl _ (List.getElem_mem _) hne i hi hb) (by simp [hs])
  obtain ⟨hh, hv⟩ := range16_values H ht' hT
  -- RANGE16's single interaction answers `[val]`, and `val` is the row index
  rw [hT] at hi
  simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
  subst hi
  refine ⟨((r' : Nat) : F), ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [row_eq_natRow]
    simp only [v, Expr.eval_col, natRow, Range16.val]
    have e : rowNat tr t r' Range16.val = r' := hv r' hr'
    simp only [Range16.val] at e ⊢
    simpa using congrArg (fun n => ((n : Nat) : F)) e
  · rw [Fp.toNat_cast_of_lt (by rw [P_val]; omega)]; omega

/-- **`gap < 2^16` from the R16 lookup.**  REG queries `gap` with count `act·(1−kind) = 1` on a
byte row, so `reg_r16_query_16bit` turns the answer into a 16-bit bound.  This is what makes
`cPosLtLen` exact and hence `pos < len` (`reg_pos_lt_len`). -/
theorem reg_gap_lt {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 26) (hk : rowNat tr 26 r Reg.kind = 0) :
    rowNat tr 26 r Reg.gap < 65536 := by
  have ha := reg_byte_active H hr hk
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hc : (((v Reg.act * Reg.isB).eval (tr.row pub 26 r)).toNat) = 1 := by
    simp only [Reg.isB, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Expr.eval_ofNat', Trace.row]
    rw [show Reg.act = 0 from rfl, show Reg.kind = 1 from rfl]
    rw [cell_cast tr 26 r 0, cell_cast tr 26 r 1]
    rw [show ((rowNat tr 26 r 0 : Nat) : F) = 1 from
          by rw [show (0:Nat) = Reg.act from rfl]; rw [ha]; rfl,
        show ((rowNat tr 26 r 1 : Nat) : F) = 0 from
          by rw [show (1:Nat) = Reg.kind from rfl]; rw [hk]; rfl]
    decide
  have hocc : (busR16, true, [((rowNat tr 26 r Reg.gap : Nat) : F)], 1) ∈
      occs (wasmBaseRegAir nloc ngl) tr pub := by
    have hmem : r16 (v Reg.gap) (v Reg.act * Reg.isB) ∈ Reg.table.inters :=
      List.mem_of_getElem? (i := 8) (by decide)
    refine (mem_occs).mpr ⟨26, (reg_walk_26 (nloc := nloc) (ngl := ngl)).1, r, hr,
      r16 (v Reg.gap) (v Reg.act * Reg.isB), ?_, ?_⟩
    · rw [hT]; exact hmem
    · simp only [r16, List.map_cons, List.map_nil]
      rw [show Expr.eval (tr.row pub 26 r) (v Reg.gap) = ((rowNat tr 26 r Reg.gap : Nat) : F) from by
        simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]]
      rw [hc]
  obtain ⟨x, hx, hxl⟩ := reg_r16_query_16bit H hsend (reg_r16_recv H) hocc (by rfl) (by rfl) (by rfl)
  simp only [List.cons.injEq, and_true] at hx
  subst hx
  rw [Fp.toNat_cast_of_lt (rowNat_lt tr 26 r Reg.gap)] at hxl
  exact hxl

/-- **`pos < len` on an active byte row.**  `cPosLtLen` is `len − pos − 1 − gap = 0`, i.e.
`pos + gap + 1 = len` in the field.  With `pos ≤ r < 2^24` (`reg_pos_le`) and `gap < 2^16` (its R16
lookup) all three terms are `< 2^24 + 2^16 < P`, so the field equation is an exact natural one and
`pos < len`.  This is the bound the walk needs to exclude a byte row at offset `len`. -/
theorem reg_pos_lt_len {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hk : rowNat tr 26 r Reg.kind = 0) (hgap : rowNat tr 26 r Reg.gap < 65536) :
    rowNat tr 26 r Reg.pos < rowNat tr 26 r Reg.blen := by
  have ha := reg_byte_active H hr hk
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cPosLtLen (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cPosLtLen, Reg.isB, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Reg.act, Reg.kind, Reg.pos, Reg.blen, Reg.gap, natRow] at h
  rw [show (rowNat tr 26 r 0 : F) = 1 from by rw [show (0:Nat) = Reg.act from rfl]; rw [ha]; rfl,
      show (rowNat tr 26 r 1 : F) = 0 from by rw [show (1:Nat) = Reg.kind from rfl]; rw [hk]; rfl] at h
  rw [show (4 : Nat) = Reg.pos from rfl, show (5 : Nat) = Reg.blen from rfl,
      show (10 : Nat) = Reg.gap from rfl] at h
  have hle := reg_pos_le H r hr
  have hP := P_val
  have hgl := H.heightLe 26 ht
  unfold maxLogHeight at hgl
  have hb : rowNat tr 26 r Reg.pos + rowNat tr 26 r Reg.gap + 1 < P := by omega
  have e : ((rowNat tr 26 r Reg.blen : F)) =
      (rowNat tr 26 r Reg.pos : F) + (rowNat tr 26 r Reg.gap : F) + 1 := by grind
  have e' : rowNat tr 26 r Reg.blen = rowNat tr 26 r Reg.pos + rowNat tr 26 r Reg.gap + 1 := by
    refine natEq ?_ (rowNat_lt tr 26 r Reg.blen) hb
    rw [e, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add]
    simp only [Lean.Grind.Semiring.natCast_add, cast_one]
  omega

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

/-! ## The group walk

The row lemmas above are successor-shaped: `reg_pos_step` and `reg_len_const` say what the *next* row
is, given that it is a byte row with `f = 0`.  The walk turns them into a statement about a whole
group: from a group-start byte row `r0`, bytes occupy `pos = 0, 1, …` consecutively and the group
ends at a length row carrying that count.

Two things make the induction go through, and both are worth stating because the naive attempt
fails:

* **Row existence must be carried.**  `reg_byte_succ_not_start` is about the next row, so the
  induction carries `r0 + n < tr.height 26` alongside the byte facts.  Deriving existence from the
  walk itself is circular.
* **Termination is `cFirst`/`cLast`, not `pos < len`.**  A byte row's successor has `f = 0`
  (`cOnlyLenEnds`) while the last row starts a group (`cLast`), so a byte row is never the last row
  (`reg_byte_not_last`).  The walk therefore cannot fall off the table: the group's length row is
  reached first. -/

/-- **Row 0 starts a group** (`cFirst` forces `f = 1`). -/
theorem reg_row0_f {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) (htr : 0 < tr.height 26) :
    rowNat tr 26 0 Reg.f = 1 := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht htr
  rw [hT] at hcon
  have hc := hcon Reg.cFirst (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cFirst, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval,
    Reg.f, natRow, Trace.row, beq_self_eq_true, ite_true] at hc
  have hf1 : (rowNat tr 26 0 Reg.f : F) = 1 := by
    rcases reg_f_bit H htr with hf | hf
    · rw [show (rowNat tr 26 0 15 : F) = 0 from by rw [show (15 : Nat) = Reg.f from rfl, hf]; rfl] at hc
      grind
    · rw [hf]; rfl
  exact natEq hf1 (rowNat_lt tr 26 0 Reg.f) (by decide)

theorem reg_byte_not_last {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hk : rowNat tr 26 r Reg.kind = 0) :
    r + 1 < tr.height 26 := by
  rcases Nat.lt_or_ge (r + 1) (tr.height 26) with h | h
  · exact h
  · exfalso
    have hlast : r + 1 = tr.height 26 := by omega
    have ha : rowNat tr 26 r Reg.act = 1 := reg_byte_active H hr hk
    have hf0 : rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0 := reg_byte_succ_not_start H hr ha hk
    rw [hlast, Nat.mod_self] at hf0
    have hf1 := reg_row0_f H (by omega)
    omega

/-- **`cRidG`**: the group's `rid` is constant across the row boundary. -/
theorem reg_rid_const {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hf' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0) :
    rowNat tr 26 ((r + 1) % tr.height 26) Reg.rid = rowNat tr 26 r Reg.rid := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cRidG (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cRidG, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', Reg.f, Reg.rid, natRow, Trace.row] at h
  have e1 : tr.cell 26 ((r + 1) % tr.height 26) 15 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) := (Fp.cast_toNat _).symm
  have e2 : tr.cell 26 ((r + 1) % tr.height 26) 3 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.rid : Nat) : F) := (Fp.cast_toNat _).symm
  rw [e1, e2] at h
  rw [show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = 0 from by rw [hf']; rfl] at h
  rw [show (3 : Nat) = Reg.rid from rfl] at h
  have h1 := rowNat_lt tr 26 ((r + 1) % tr.height 26) Reg.rid
  have h2 := rowNat_lt tr 26 r Reg.rid
  have e : (rowNat tr 26 ((r + 1) % tr.height 26) Reg.rid : F) = (rowNat tr 26 r Reg.rid : F) := by
    grind
  exact natEq e h1 h2

/-- **`cTsG`**: the group's `ts` is constant across the row boundary. -/
theorem reg_ts_const {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hf' : rowNat tr 26 ((r + 1) % tr.height 26) Reg.f = 0) :
    rowNat tr 26 ((r + 1) % tr.height 26) Reg.ts = rowNat tr 26 r Reg.ts := by
  have ht := (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
  have hT := (reg_walk_26 (nloc := nloc) (ngl := ngl)).2
  have hcon := table_constr H ht hr
  rw [hT] at hcon
  have h := hcon Reg.cTsG (by simp [Reg.table, Reg.constraints])
  simp only [Reg.cTsG, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_nxt, Expr.eval_ofNat', Reg.f, Reg.ts, natRow, Trace.row] at h
  have e1 : tr.cell 26 ((r + 1) % tr.height 26) 15 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) := (Fp.cast_toNat _).symm
  have e2 : tr.cell 26 ((r + 1) % tr.height 26) 8 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.ts : Nat) : F) := (Fp.cast_toNat _).symm
  rw [e1, e2] at h
  rw [show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = 0 from by rw [hf']; rfl] at h
  rw [show (8 : Nat) = Reg.ts from rfl] at h
  have h1 := rowNat_lt tr 26 ((r + 1) % tr.height 26) Reg.ts
  have h2 := rowNat_lt tr 26 r Reg.ts
  have e : (rowNat tr 26 ((r + 1) % tr.height 26) Reg.ts : F) = (rowNat tr 26 r Reg.ts : F) := by
    grind
  exact natEq e h1 h2

/-- One step of the walk: from a byte row at `r0 + n` (with `f = 0` unless `n = 0`, `pos = n`,
`len = L`), the successor is inside the table and still carries `len = L`. -/
theorem reg_step {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hk : rowNat tr 26 r Reg.kind = 0) :
    r + 1 < tr.height 26 ∧
      rowNat tr 26 (r + 1) Reg.f = 0 ∧
      rowNat tr 26 (r + 1) Reg.blen = rowNat tr 26 r Reg.blen := by
  have hlt := reg_byte_not_last H hr hk
  have hmod : (r + 1) % tr.height 26 = r + 1 := Nat.mod_eq_of_lt hlt
  have ha : rowNat tr 26 r Reg.act = 1 := reg_byte_active H hr hk
  have hf0 := reg_byte_succ_not_start H hr ha hk
  rw [hmod] at hf0
  refine ⟨hlt, hf0, ?_⟩
  have := reg_len_const H hr (by rw [hmod]; exact hf0)
  rw [hmod] at this
  exact this

/-- The successor of a byte row keeps the group's `rid` and `ts`. -/
theorem reg_step_ids {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26)
    (hk : rowNat tr 26 r Reg.kind = 0) :
    rowNat tr 26 (r + 1) Reg.rid = rowNat tr 26 r Reg.rid ∧
      rowNat tr 26 (r + 1) Reg.ts = rowNat tr 26 r Reg.ts := by
  have hlt := reg_byte_not_last H hr hk
  have hmod : (r + 1) % tr.height 26 = r + 1 := Nat.mod_eq_of_lt hlt
  have ha : rowNat tr 26 r Reg.act = 1 := reg_byte_active H hr hk
  have hf0 := reg_byte_succ_not_start H hr ha hk
  rw [hmod] at hf0
  refine ⟨?_, ?_⟩
  · have := reg_rid_const H hr (by rw [hmod]; exact hf0); rw [hmod] at this; exact this
  · have := reg_ts_const H hr (by rw [hmod]; exact hf0); rw [hmod] at this; exact this

/-- **The group walk.**  From a group-start byte row `r0` with count `L`, the rows `r0 … r0+L−1`
are the group's bytes (`kind = 0`, `pos = i`, `len = L`) and row `r0+L` is its length row.

Proved by induction on the offset, carrying row existence (the first conjunct) so the successor
lemmas apply.  The `n < L` bound is not an input to termination: it is what makes the byte case
impossible at `n = L`, because `cLastByte` would then say `L = n` too. -/
theorem reg_group_walk {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r0 : Nat} (hr0 : r0 < tr.height 26)
    (hf : rowNat tr 26 r0 Reg.f = 1) (hk : rowNat tr 26 r0 Reg.kind = 0) :
    ∀ n, n ≤ rowNat tr 26 r0 Reg.blen → r0 + n < tr.height 26 →
      (rowNat tr 26 (r0 + n) Reg.blen = rowNat tr 26 r0 Reg.blen) ∧
      ((n < rowNat tr 26 r0 Reg.blen) →
        rowNat tr 26 (r0 + n) Reg.kind = 0 ∧ rowNat tr 26 (r0 + n) Reg.pos = n) := by
  intro n
  induction n with
  | zero =>
    intro _ hlt
    refine ⟨rfl, ?_⟩
    intro _
    have hp := reg_start_pos H hr0 hf hk
    exact ⟨hk, by simpa using hp⟩
  | succ n ih =>
    intro hle hlt
    have hnle : n ≤ rowNat tr 26 r0 Reg.blen := by omega
    have hnlt : r0 + n < tr.height 26 := by omega
    obtain ⟨hlen, hbyte⟩ := ih hnle hnlt
    have hk' : rowNat tr 26 (r0 + n) Reg.kind = 0 := (hbyte (by omega)).1
    obtain ⟨hstep, hf0', hlen'⟩ := reg_step H hnlt hk'
    -- `r0 + (n+1) = (r0+n) + 1`
    have hidx : r0 + (n + 1) = (r0 + n) + 1 := by omega
    rw [hidx]
    have hlen'' : rowNat tr 26 ((r0 + n) + 1) Reg.blen = rowNat tr 26 r0 Reg.blen :=
      hlen'.trans hlen
    refine ⟨hlen'', ?_⟩
    intro hn1
    -- the successor is a byte row (it cannot be a length row: then `cLastByte` gives `L = n+1`)
    have hkind : rowNat tr 26 ((r0 + n) + 1) Reg.kind = 0 := by
      rcases reg_kind_bit H hstep with h | h
      · exact h
      · exfalso
        have hmod2 : ((r0 + n) + 1) % tr.height 26 = (r0 + n) + 1 := Nat.mod_eq_of_lt hstep
        have hlb := reg_last_byte H hnlt (by rw [hmod2]; exact hf0') (by rw [hmod2]; exact h)
        have hb : rowNat tr 26 (r0 + n) Reg.blen = rowNat tr 26 (r0 + n) Reg.pos + 1 := hlb
        have hp : rowNat tr 26 (r0 + n) Reg.pos = n := (hbyte (by omega)).2
        omega
    refine ⟨hkind, ?_⟩
    have hmod : ((r0 + n) + 1) % tr.height 26 = (r0 + n) + 1 := Nat.mod_eq_of_lt hstep
    have hps := reg_pos_step H hnlt (by rw [hmod]; exact hf0')
      (by rw [hmod]; exact hkind)
    rw [hmod] at hps
    rw [hps]
    have hp0 := hbyte (by omega)
    omega




/-- The group's `rid` and `ts` are constant along the walk as well (needed for the message
theorem, which compares the group's byte messages against its length message). -/
theorem reg_group_ids {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r0 : Nat} (hr0 : r0 < tr.height 26)
    (hf : rowNat tr 26 r0 Reg.f = 1) (hk : rowNat tr 26 r0 Reg.kind = 0) :
    ∀ n, n ≤ rowNat tr 26 r0 Reg.blen → r0 + n < tr.height 26 →
      rowNat tr 26 (r0 + n) Reg.rid = rowNat tr 26 r0 Reg.rid ∧
      rowNat tr 26 (r0 + n) Reg.ts = rowNat tr 26 r0 Reg.ts := by
  intro n
  induction n with
  | zero => intro _ _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro hle hlt
    have hnle : n ≤ rowNat tr 26 r0 Reg.blen := by omega
    have hnlt : r0 + n < tr.height 26 := by omega
    obtain ⟨hrid, hts⟩ := ih hnle hnlt
    have hk' : rowNat tr 26 (r0 + n) Reg.kind = 0 :=
      (reg_group_walk H hr0 hf hk n hnle hnlt).2 (by omega) |>.1
    have hstep := reg_step_ids H hnlt hk'
    constructor
    · rw [show r0 + (n + 1) = (r0 + n) + 1 from by omega, hstep.1, hrid]
    · rw [show r0 + (n + 1) = (r0 + n) + 1 from by omega, hstep.2, hts]


/-! ## The space-6 slot encodings, evaluated -/

theorem reg_byteslot_eval (tr : Trace) (pub : List F) (r : Nat) :
    Expr.eval (tr.row pub 26 r) Reg.byteSlotE = ((rowNat tr 26 r Reg.rid * 16777216 +
      rowNat tr 26 r Reg.pos + 1 : Nat) : F) := by
  simp only [Reg.byteSlotE, Register.cap, Register.posBits, Reg.rid, Reg.pos,
    Chips.v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, Expr.eval_c, Trace.row, cell_cast]
  rw [show (2 ^ 24 : Nat) = 16777216 from by decide]
  simp only [Expr.eval_ofNat']
  rw [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add,
    ← Lean.Grind.Semiring.natCast_add]

theorem reg_lenslot_eval (tr : Trace) (pub : List F) (r : Nat) :
    Expr.eval (tr.row pub 26 r) Reg.lenSlotE = ((rowNat tr 26 r Reg.rid * 16777216 : Nat) : F) := by
  simp only [Reg.lenSlotE, Register.cap, Register.posBits, Reg.rid, Chips.v, Expr.eval_mul',
    Expr.eval_col, Expr.eval_c, Trace.row, cell_cast]
  rw [show (2 ^ 24 : Nat) = 16777216 from by decide]
  rw [← Lean.Grind.Semiring.natCast_mul]

/-- The two CH sends of `REG`, in order: the byte slot, then the length slot. -/
theorem reg_ch_sends :
    (Reg.inters.filter (fun i => decide (i.bus = busStk ∧ i.send = true))) =
      [chSend (Expr.c Register.space) Reg.byteSlotE (Expr.c Register.byteTag) [v Reg.bv, 0, 0, 0]
          (v Reg.ts) (v Reg.act * (1 - v Reg.kind)),
       chSend (Expr.c Register.space) Reg.lenSlotE (Expr.c Register.lenTag) [v Reg.blen, 0, 0, 0]
          (v Reg.ts) (v Reg.act * v Reg.kind)] := by decide

/-- **A byte row's space-6 send message** (raw `List F`). -/
theorem reg_byte_msg {tr : Trace} {pub : List F} {r : Nat}
    (hk : rowNat tr 26 r Reg.kind = 0) (ha : rowNat tr 26 r Reg.act = 1) :
    rowMsgs Reg.table tr pub 26 r busStk true =
      [[((6 : Nat) : F), ((rowNat tr 26 r Reg.rid * 16777216 + rowNat tr 26 r Reg.pos + 1 : Nat) : F),
        ((0 : Nat) : F), ((rowNat tr 26 r Reg.bv : Nat) : F), 0, 0, 0,
        ((rowNat tr 26 r Reg.ts : Nat) : F)]] := by
  rw [rowMsgs_eq]
  show (List.filterMap _ (List.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) Reg.inters)) = _
  rw [reg_ch_sends]
  have hc1 : ((Expr.eval (tr.row pub 26 r) (v Reg.act * (1 - v Reg.kind))).toNat) = 1 := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row]
    rw [show Reg.act = 0 from rfl, show Reg.kind = 1 from rfl]
    rw [cell_cast tr 26 r 0, cell_cast tr 26 r 1]
    rw [show ((rowNat tr 26 r 0 : Nat) : F) = 1 from by rw [show (0:Nat) = Reg.act from rfl]; rw [ha]; rfl,
        show ((rowNat tr 26 r 1 : Nat) : F) = 0 from by rw [show (1:Nat) = Reg.kind from rfl]; rw [hk]; rfl]
    decide
  have hc2 : ((Expr.eval (tr.row pub 26 r) (v Reg.act * v Reg.kind)).toNat) = 0 := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_col, Trace.row]
    rw [show Reg.act = 0 from rfl, show Reg.kind = 1 from rfl]
    rw [cell_cast tr 26 r 0, cell_cast tr 26 r 1]
    rw [show ((rowNat tr 26 r 1 : Nat) : F) = 0 from by rw [show (1:Nat) = Reg.kind from rfl]; rw [hk]; rfl]
    trivial
  simp only [List.filterMap_cons, List.filterMap_nil, chSend]
  rw [if_pos hc1, if_neg (by rw [hc2]; decide)]
  simp only [List.cons.injEq, and_true]
  show List.map (fun x => Expr.eval (tr.row pub 26 r) x)
    ([Expr.c Register.space, Reg.byteSlotE, Expr.c Register.byteTag] ++ [v Reg.bv, 0, 0, 0] ++ [v Reg.ts]) = _
  have hs := reg_byteslot_eval tr pub r
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Chips.v, Expr.eval_col, Expr.eval_c, Expr.eval_ofNat']
  rw [hs]
  simp only [Trace.row, cell_cast, Register.space, Register.byteTag]
  rfl

/-- **A length row's space-6 send message** (raw `List F`). -/
theorem reg_len_msg {tr : Trace} {pub : List F} {r : Nat}
    (hk : rowNat tr 26 r Reg.kind = 1) (ha : rowNat tr 26 r Reg.act = 1) :
    rowMsgs Reg.table tr pub 26 r busStk true =
      [[((6 : Nat) : F), ((rowNat tr 26 r Reg.rid * 16777216 : Nat) : F), ((2 : Nat) : F),
        ((rowNat tr 26 r Reg.blen : Nat) : F), 0, 0, 0, ((rowNat tr 26 r Reg.ts : Nat) : F)]] := by
  rw [rowMsgs_eq]
  show (List.filterMap _ (List.filter (fun i => decide (i.bus = busStk ∧ i.send = true)) Reg.inters)) = _
  rw [reg_ch_sends]
  have hc1 : ((Expr.eval (tr.row pub 26 r) (v Reg.act * (1 - v Reg.kind))).toNat) = 0 := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row]
    rw [show Reg.act = 0 from rfl, show Reg.kind = 1 from rfl]
    rw [cell_cast tr 26 r 0, cell_cast tr 26 r 1]
    rw [show ((rowNat tr 26 r 0 : Nat) : F) = 1 from by rw [show (0:Nat) = Reg.act from rfl]; rw [ha]; rfl,
        show ((rowNat tr 26 r 1 : Nat) : F) = 1 from by rw [show (1:Nat) = Reg.kind from rfl]; rw [hk]; rfl]
    trivial
  have hc2 : ((Expr.eval (tr.row pub 26 r) (v Reg.act * v Reg.kind)).toNat) = 1 := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_col, Trace.row]
    rw [show Reg.act = 0 from rfl, show Reg.kind = 1 from rfl]
    rw [cell_cast tr 26 r 0, cell_cast tr 26 r 1]
    rw [show ((rowNat tr 26 r 0 : Nat) : F) = 1 from by rw [show (0:Nat) = Reg.act from rfl]; rw [ha]; rfl,
        show ((rowNat tr 26 r 1 : Nat) : F) = 1 from by rw [show (1:Nat) = Reg.kind from rfl]; rw [hk]; rfl]
    rfl
  simp only [List.filterMap_cons, List.filterMap_nil, chSend]
  rw [if_neg (by rw [hc1]; decide), if_pos hc2]
  simp only [List.cons.injEq, and_true]
  show List.map (fun x => Expr.eval (tr.row pub 26 r) x)
    ([Expr.c Register.space, Reg.lenSlotE, Expr.c Register.lenTag] ++ [v Reg.blen, 0, 0, 0] ++ [v Reg.ts]) = _
  have hs := reg_lenslot_eval tr pub r
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Chips.v, Expr.eval_col, Expr.eval_c, Expr.eval_ofNat']
  rw [hs]
  simp only [Trace.row, cell_cast, Register.space, Register.lenTag]
  rfl

/-! ## Row messages and `Register.RegLenAgree`

A REG row sends exactly one space-6 message on CH: a byte row sends `byteMsg rid pos bv ts`, a
length row sends `lenMsg rid len ts`.  The walk therefore makes the length message of a group agree
with that group's byte count.

`Register.RegLenAgree` is stated over *all messages sharing a producer time*.  That is **false for a
length-only access**: `register_len` emits one length row and no byte row, so at its producer time
the register has a length message and zero byte messages (`regLenAgree_false_of_lone_length`).  The
AIR's real obligation is the group-local one — a length message is produced by the length row of a
group whose bytes are `pos = 0 … len−1` — and that is `regLenAgree_group`. -/

/-- The `Msg` a REG byte row produces: `byteMsg rid pos bv ts`.  `rid ≤ 99` keeps the byte slot
below `P`, so `decMsg`'s `toNat` is exact. -/
theorem reg_byte_row_msg {tr : Trace} {pub : List F} {r : Nat}
    (hrid : rowNat tr 26 r Reg.rid ≤ 99) (hpos : rowNat tr 26 r Reg.pos < 16777216)
    (hk : rowNat tr 26 r Reg.kind = 0) (ha : rowNat tr 26 r Reg.act = 1) :
    rowProd Reg.table tr pub 26 r =
      [Register.byteMsg (rowNat tr 26 r Reg.rid) (rowNat tr 26 r Reg.pos)
        (rowNat tr 26 r Reg.bv) (rowNat tr 26 r Reg.ts)] := by
  rw [rowProd, reg_byte_msg hk ha]
  simp only [List.map_cons, List.map_nil]
  have e := decMsg_cast 6 (rowNat tr 26 r Reg.rid * 16777216 + rowNat tr 26 r Reg.pos + 1) 0
    (rowNat tr 26 r Reg.bv) 0 0 0 (rowNat tr 26 r Reg.ts)
    (by decide) (by have hP := P_val; omega) (by decide) (rowNat_lt tr 26 r Reg.bv)
    (by decide) (by decide) (by decide) (rowNat_lt tr 26 r Reg.ts)
  rw [show [decMsg [((6 : Nat) : F),
      ((rowNat tr 26 r Reg.rid * 16777216 + rowNat tr 26 r Reg.pos + 1 : Nat) : F),
      ((0 : Nat) : F), ((rowNat tr 26 r Reg.bv : Nat) : F), (0 : F), (0 : F),
      (0 : F), ((rowNat tr 26 r Reg.ts : Nat) : F)]] = _ from congrArg (fun m => [m]) e]
  simp only [Register.byteMsg, Register.byteSlot, Register.slot, Register.cap, Register.posBits,
    Register.space, Register.byteTag, Nat.add_assoc]

/-- The `Msg` a REG length row produces: `lenMsg rid len ts`. -/
theorem reg_len_row_msg {tr : Trace} {pub : List F} {r : Nat}
    (hrid : rowNat tr 26 r Reg.rid ≤ 99)
    (hk : rowNat tr 26 r Reg.kind = 1) (ha : rowNat tr 26 r Reg.act = 1) :
    rowProd Reg.table tr pub 26 r =
      [Register.lenMsg (rowNat tr 26 r Reg.rid) (rowNat tr 26 r Reg.blen) (rowNat tr 26 r Reg.ts)] := by
  rw [rowProd, reg_len_msg hk ha]
  simp only [List.map_cons, List.map_nil]
  have e := decMsg_cast 6 (rowNat tr 26 r Reg.rid * 16777216) 2 (rowNat tr 26 r Reg.blen) 0 0 0
    (rowNat tr 26 r Reg.ts) (by decide) (by have hP := P_val; omega) (by decide)
    (rowNat_lt tr 26 r Reg.blen) (by decide) (by decide) (by decide) (rowNat_lt tr 26 r Reg.ts)
  rw [show [decMsg [((6 : Nat) : F), ((rowNat tr 26 r Reg.rid * 16777216 : Nat) : F),
      ((2 : Nat) : F), ((rowNat tr 26 r Reg.blen : Nat) : F), (0 : F), (0 : F),
      (0 : F), ((rowNat tr 26 r Reg.ts : Nat) : F)]] = _ from congrArg (fun m => [m]) e]
  simp only [Register.lenMsg, Register.lenSlot, Register.slot, Register.cap, Register.posBits,
    Register.space, Register.lenTag, Nat.mul_add, Nat.add_zero]

/-- **Existence along the group.**  Every offset `n ≤ L` lands inside the table.

This is not a consequence of "the group has `L` rows" but the induction that *establishes* it:
a byte row is never the last row (`reg_byte_not_last`), so as long as `n < L` the row `r0 + n` is a
byte row and the walk can step to `r0 + n + 1`.  The hypothesis `r0 + L < height` is therefore not
needed — it is the conclusion at `n = L`. -/
theorem reg_group_bounds {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r0 : Nat} (hr0 : r0 < tr.height 26)
    (hf : rowNat tr 26 r0 Reg.f = 1) (hk : rowNat tr 26 r0 Reg.kind = 0) :
    ∀ n, n ≤ rowNat tr 26 r0 Reg.blen → r0 + n < tr.height 26 := by
  intro n
  induction n with
  | zero => intro _; simpa using hr0
  | succ n ih =>
    intro hle
    have hnlt : r0 + n < tr.height 26 := ih (by omega)
    have hkn : rowNat tr 26 (r0 + n) Reg.kind = 0 :=
      (reg_group_walk H hr0 hf hk n (by omega) hnlt).2 (by omega) |>.1
    have := reg_byte_not_last H hnlt hkn
    simpa only [Nat.add_assoc] using this

/-- **The group obligation, in message form.**  The group starting at byte row `r0` has its length
row at `r0 + L` with `len = L`, its byte rows are `r0 … r0+L−1` at `pos = 0 … L−1`, and every one
of them produces the byte message of that position (its `rid` and `ts` being the group's).

A length-only access is `L = 0`: the byte claim is vacuous and the length row starts the group. -/
theorem regLenAgree_group {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {r0 : Nat} (hr0 : r0 < tr.height 26)
    (hf : rowNat tr 26 r0 Reg.f = 1) (hk : rowNat tr 26 r0 Reg.kind = 0)
    (hrid0 : rowNat tr 26 r0 Reg.rid ≤ 99) (hpos0 : rowNat tr 26 r0 Reg.pos < 16777216)
    (hactL' : ∀ n, n ≤ rowNat tr 26 r0 Reg.blen → r0 + n < tr.height 26 →
      rowNat tr 26 (r0 + n) Reg.kind = 1 → rowNat tr 26 (r0 + n) Reg.act = 1) :
    let L := rowNat tr 26 r0 Reg.blen
    r0 + L < tr.height 26 ∧
      rowNat tr 26 (r0 + L) Reg.kind = 1 ∧
      rowProd Reg.table tr pub 26 (r0 + L) =
        [Register.lenMsg (rowNat tr 26 r0 Reg.rid) L (rowNat tr 26 r0 Reg.ts)] ∧
      (∀ i, i < L → rowProd Reg.table tr pub 26 (r0 + i) =
        [Register.byteMsg (rowNat tr 26 r0 Reg.rid) i (rowNat tr 26 (r0 + i) Reg.bv)
          (rowNat tr 26 r0 Reg.ts)]) := by
  intro L
  have hneed : r0 + L < tr.height 26 := reg_group_bounds H hr0 hf hk L (Nat.le_refl L)
  have hkL : rowNat tr 26 (r0 + L) Reg.kind = 1 := by
    rcases reg_kind_bit H hneed with h | h
    · -- a byte row at offset `L` would have `pos = L`, contradicting `pos < len = L`
      exfalso
      have hwalk := reg_group_walk H hr0 hf hk L (Nat.le_refl L) hneed
      have hLpos : 0 < L := by
        rcases Nat.eq_zero_or_pos L with h0 | h0
        · exfalso
          have hp0 := reg_start_pos H hr0 hf hk
          have hgap0 := reg_gap_lt H hsend hr0 hk
          have := reg_pos_lt_len H hr0 hk hgap0
          omega
        · exact h0
      -- step from the last byte row `r0 + (L-1)` to `r0 + L`
      have hprevlt : r0 + (L - 1) < tr.height 26 := by omega
      have hkprev : rowNat tr 26 (r0 + (L - 1)) Reg.kind = 0 :=
        (reg_group_walk H hr0 hf hk (L - 1) (by omega) hprevlt).2 (by omega) |>.1
      have hposprev : rowNat tr 26 (r0 + (L - 1)) Reg.pos = L - 1 :=
        (reg_group_walk H hr0 hf hk (L - 1) (by omega) hprevlt).2 (by omega) |>.2
      have hidx : r0 + L = (r0 + (L - 1)) + 1 := by omega
      have hmod : ((r0 + (L - 1)) + 1) % tr.height 26 = (r0 + (L - 1)) + 1 :=
        Nat.mod_eq_of_lt (by omega)
      have ha := reg_byte_active H hprevlt hkprev
      have hf0prev : rowNat tr 26 ((r0 + (L - 1)) + 1) Reg.f = 0 := by
        have := reg_byte_succ_not_start H hprevlt ha hkprev
        rw [hmod] at this
        exact this
      have hkmod : rowNat tr 26 (((r0 + (L - 1)) + 1) % tr.height 26) Reg.kind = 0 := by
        rw [hmod]; rw [← hidx]; exact h
      have hpos := reg_pos_step H hprevlt (by rw [hmod]; exact hf0prev) hkmod
      rw [hmod] at hpos
      have hpos' : rowNat tr 26 (r0 + L) Reg.pos = rowNat tr 26 (r0 + (L - 1)) Reg.pos + 1 := by
        rw [hidx]; exact hpos
      have hpl := reg_pos_lt_len H hneed h (reg_gap_lt H hsend hneed h)
      omega
    · exact h
  have hlenL : rowNat tr 26 (r0 + L) Reg.blen = L := by
    have := reg_group_walk H hr0 hf hk L (Nat.le_refl L) hneed
    exact this.1
  have hactL : rowNat tr 26 (r0 + L) Reg.act = 1 := hactL' L (Nat.le_refl L) hneed hkL
  have hidsL := reg_group_ids H hr0 hf hk L (Nat.le_refl L) hneed
  have hridL : rowNat tr 26 (r0 + L) Reg.rid ≤ 99 := by rw [hidsL.1]; exact hrid0
  refine ⟨hneed, hkL, ?_, ?_⟩
  · rw [reg_len_row_msg hridL hkL hactL, hlenL, hidsL.1, hidsL.2]
  · intro i hi
    have hilt : r0 + i < tr.height 26 := by
      have : i ≤ L := by omega
      exact reg_group_bounds H hr0 hf hk i this
    have hki : rowNat tr 26 (r0 + i) Reg.kind = 0 :=
      (reg_group_walk H hr0 hf hk i (by omega) hilt).2 hi |>.1
    have hpi : rowNat tr 26 (r0 + i) Reg.pos = i :=
      (reg_group_walk H hr0 hf hk i (by omega) hilt).2 hi |>.2
    have hacti : rowNat tr 26 (r0 + i) Reg.act = 1 := reg_byte_active H hilt hki
    have hidsi := reg_group_ids H hr0 hf hk i (by omega) hilt
    have hridi : rowNat tr 26 (r0 + i) Reg.rid ≤ 99 := by rw [hidsi.1]; exact hrid0
    have hposi : rowNat tr 26 (r0 + i) Reg.pos < 16777216 := by
      rw [hpi]
      have := H.heightLe 26 (reg_walk_26 (nloc := nloc) (ngl := ngl)).1
      unfold maxLogHeight at this
      omega
    rw [reg_byte_row_msg hridi hposi hki hacti, hpi, hidsi.1, hidsi.2]


end WasmBase




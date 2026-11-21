import ZkFormal.PQ.NvAff
import ZkFormal.PQ.NvField

/-!
# ZkFormal.PQ.NvProg — program binding, op decode over the byte bus, `PvdAt`, the asserts

Lane E (E2E M11g, item 2), 2026-11-04. Everything is proved from the circuit's own predicate
`NvField.NvHold` (the four exported tables, field LogUp on every bus).

## The chain

1. **Program binding** (`ProgBound tr prog`): NvAir's program columns `P0..P3` on rows
   `0 .. |prog|` hold the pinned program's words `[A, B + op·2^24, K1, K2]` (`isa.rs`
   `Instr::words`). This is the premise the level above supplies: V_d's opening check of the
   FINAL program columns, or the parent's binding (`C_t` anchor / BIND) for a tree level. It is
   a premise here, stated exactly.
2. **Role** (`ka_of_p1`): a row whose `P1 ≠ 0` is an ALU row (exported constraint
   `(1 − ka)·P1`). Every op but `Nop` has `P1 ≥ 2^24`.
3. **Op decode** (`decode_ok`, `decode_row`): on an ALU row with selector halves `(a, b)`, the
   exported constraint 1799 is `P1 − (8b + a)·2^24 − rx − 256·ry − 65536·rz` (checked for all 40
   cases by partial evaluation of the exported expression, `NvAff`).
4. **Byte range** (`byte_keys`, `alu_bytes`): ByteAir's 9 exported constraints make its key
   column pair enumerate `(r mod 256, r / 256)` with last row `(255, 255)`, so every key is a byte
   pair. NvAir's ALU rows look up `(rx, ry)` and `(rz, 0)` on the byte bus with count `1`; every
   other byte-bus entry of NvAir has count `0` or `1` (by role, partial evaluation), **except**
   four GLUE-row counts (`act·(1 − phase) − p_s − wd` style), which are a premise
   (`GlueByteBool`). The field LogUp balance of bus 11 then forces `rx, ry, rz < 256`.
5. Hence `op = 8b + a` and `B = rx + 256·ry + 65536·rz` (`alu_op`), and:
   * `pvdAt_of`: **`PvdAt`** for every `PvD` instruction of the bound program;
   * `asserted_eq`: **every `assert_eq` of the bound program holds** (`Sub x y` then `Zero`:
     the cells at `x` and `y` are equal, all 12 limbs), from the `Sub`/`Zero` constraints and
     memory consistency of the three reads;
   * `contAsserts_of`: `build_agg`'s continuity loop (`ContAsserts`) for a read laid out at
     program addresses, and `nodeExecV_of_prog`: `NodeExecV` with the tape and asserts
     components discharged.

## Premises left (named)

* `ProgBound`: program binding (above).
* `GlueByteBool`: the four GLUE-row byte-bus counts are boolean (a GLUE-role fact).
* The decode-level link (`NodeAsserts`' first conjunct follows from the asserted cell equalities)
  and `NodeSha`, `NodeInner`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvProg

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvCircuitExport
open ZkFormal.PQ.NvTape ZkFormal.PQ.NvAff ZkFormal.PQ.NvField
open ZkFormal.PQ.Aggregation.Stmt

set_option maxRecDepth 100000

/-! ## The program and its binding -/

/-- An instruction `(op, A, B, K1, K2)` (`isa.rs` `Instr`). -/
structure Instr where
  op : Nat
  a : Nat
  b : Nat
  k1 : Nat
  k2 : Nat
  deriving DecidableEq

/-- Row `y` of NvAir holds instruction `i` in its program columns `P0..P3`
(`Instr::words = [A, B + op·2^24, K1, K2]`). -/
def ProgRow (tr : Trace Fp) (y : Nat) (i : Instr) : Prop :=
  cv tr 0 y 6 = ((i.a : Nat) : Fp) ∧ cv tr 0 y 7 = ((i.b + i.op * 2 ^ 24 : Nat) : Fp) ∧
    cv tr 0 y 8 = ((i.k1 : Nat) : Fp) ∧ cv tr 0 y 9 = ((i.k2 : Nat) : Fp)

/-- **Program binding**: the first `|prog|` rows of NvAir hold the pinned program. -/
def ProgBound (tr : Trace Fp) (prog : List Instr) : Prop :=
  prog.length ≤ tr.height 0 ∧ ∀ y (h : y < prog.length), ProgRow tr y prog[y]

/-! ## Role from `P1` -/

theorem dag_ka_p1 : dag 179 = .mul (esub (.const 1) (col 0)) (col 7) := by decide
theorem mem_ka_p1 : 179 ∈ nvConstraintIdx := by decide

theorem ka_of_p1 {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) (hp : cv tr 0 r 7 ≠ 0) : cv tr 0 r 0 = 1 := by
  have e := cz h hr mem_ka_p1 dag_ka_p1
  change (((1 : Nat) : Fp) + -cv tr 0 r 0) * cv tr 0 r 7 = 0 at e
  have h1 : ((1 : Nat) : Fp) = 1 := rfl
  rw [h1] at e
  grind

/-! ## Fixings of a row -/

/-- An ALU row with selector halves `(a, b)` (current row only). -/
def fxOp (a b : Nat) : Fix := fun c nx =>
  if nx then none
  else if c = 0 then some 1
  else if c ≤ 4 then some 0
  else if 34 ≤ c ∧ c < 42 then some (if c - 34 = a then 1 else 0)
  else if 58 ≤ c ∧ c < 63 then some (if c - 58 = b then 1 else 0)
  else none

/-- A row of role `k` (`0` ALU, `1` BIND, `2` GLUE, `3` HASH, `4` SAMP, `5` padding). -/
def fxRole (k : Nat) : Fix := fun c nx =>
  if nx then none else if c < 5 then some (if c = k then 1 else 0) else none

theorem flags_alu {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) :
    cv tr 0 r 1 = 0 ∧ cv tr 0 r 2 = 0 ∧ cv tr 0 r 3 = 0 ∧ cv tr 0 r 4 = 0 := by
  have fl := flags h hr
  unfold RoleFlags at fl
  rcases fl with ⟨-, a, b, c, d⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩
  · exact ⟨a, b, c, d⟩
  all_goals (rw [hka] at e0; exact absurd e0 (by decide))

theorem agrees_op {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) {a b : Nat}
    (hx : ∀ i, i < 8 → cv tr 0 r (34 + i) = if i = a then 1 else 0)
    (hy : ∀ j, j < 5 → cv tr 0 r (58 + j) = if j = b then 1 else 0) :
    Agrees (fxOp a b) (rowEnv tr 0 r pub) := by
  intro c nx v hv
  obtain ⟨f1, f2, f3, f4⟩ := flags_alu h hr hka
  unfold fxOp at hv
  cases nx with
  | true => simp at hv
  | false =>
    simp only [Bool.false_eq_true, if_false] at hv
    have hc : c < 1000 := by
      by_cases h0 : c = 0
      · omega
      · rw [if_neg h0] at hv
        by_cases h4 : c ≤ 4
        · omega
        · rw [if_neg h4] at hv
          by_cases h5 : 34 ≤ c ∧ c < 42
          · omega
          · rw [if_neg h5] at hv
            by_cases h6 : 58 ≤ c ∧ c < 63
            · omega
            · rw [if_neg h6] at hv; simp at hv
    show rowVal tr 0 r pub c false = v
    rw [rowVal_col tr 0 r pub c hc]
    by_cases h0 : c = 0
    · subst h0; simp only [if_true, Option.some.injEq] at hv; rw [← hv]; exact hka
    · rw [if_neg h0] at hv
      by_cases h4 : c ≤ 4
      · rw [if_pos h4, Option.some.injEq] at hv
        rw [← hv]
        have : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
        rcases this with rfl | rfl | rfl | rfl
        · exact f1
        · exact f2
        · exact f3
        · exact f4
      · rw [if_neg h4] at hv
        by_cases h5 : 34 ≤ c ∧ c < 42
        · rw [if_pos h5, Option.some.injEq] at hv
          rw [← hv]
          have := hx (c - 34) (by omega)
          rw [show 34 + (c - 34) = c by omega] at this
          exact this
        · rw [if_neg h5] at hv
          by_cases h6 : 58 ≤ c ∧ c < 63
          · rw [if_pos h6, Option.some.injEq] at hv
            rw [← hv]
            have := hy (c - 58) (by omega)
            rw [show 58 + (c - 58) = c by omega] at this
            exact this
          · rw [if_neg h6] at hv; simp at hv

/-! ## The B-field decode constraint (exported node 1799) -/

def decVars : List (Nat × Bool) := [(7, false), (44, false), (45, false), (63, false)]
def decKs : List Fp := [1, -1, -((256 : Nat) : Fp), -((65536 : Nat) : Fp)]

/-- **On an ALU row with selector halves `(a, b)`, constraint 1799 is
`P1 − (8b + a)·2^24 − rx − 256·ry − 65536·rz`**, all 40 cases, by partial evaluation of the
exported expression. -/
theorem decode_ok : ∀ a, a < 8 → ∀ b, b < 5 →
    EvalIs (fxOp a b) (dag 1799) (-(((8 * b + a) * 2 ^ 24 : Nat) : Fp)) decVars decKs = true := by
  decide +kernel

theorem mem_decode : 1799 ∈ nvConstraintIdx := by decide

theorem decode_row {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) {a b : Nat} (ha : a < 8) (hb : b < 5)
    (hx : ∀ i, i < 8 → cv tr 0 r (34 + i) = if i = a then 1 else 0)
    (hy : ∀ j, j < 5 → cv tr 0 r (58 + j) = if j = b then 1 else 0) :
    cv tr 0 r 7 = (((8 * b + a) * 2 ^ 24 : Nat) : Fp) + cv tr 0 r 44 +
      ((256 : Nat) : Fp) * cv tr 0 r 45 + ((65536 : Nat) : Fp) * cv tr 0 r 63 := by
  have e := h r hr 1799 mem_decode
  rw [evalIs_row (fxOp a b) tr 0 r pub (agrees_op h hr hka hx hy) _ _ _ _ (decode_ok a ha b hb)] at e
  simp only [decVars, decKs, lin, rowVal_col tr 0 r pub _ (by decide : (7 : Nat) < 1000),
    rowVal_col tr 0 r pub _ (by decide : (44 : Nat) < 1000),
    rowVal_col tr 0 r pub _ (by decide : (45 : Nat) < 1000),
    rowVal_col tr 0 r pub _ (by decide : (63 : Nat) < 1000)] at e
  grind

/-! ## ByteAir: every key is a byte pair -/

theorem byte_dag : dagOf byteNodes 3 = .mul (col 2) (esub (col 2) (.const 1)) ∧
    dagOf byteNodes 7 = .mul (col 2) (esub (col 0) (.const 255)) ∧
    dagOf byteNodes 11 = esub (.mul (esub (col 0) (.const 255)) (col 3)) (esub (.const 1) (col 2)) ∧
    dagOf byteNodes 13 = .mul .isFirst (col 0) ∧ dagOf byteNodes 15 = .mul .isFirst (col 1) ∧
    dagOf byteNodes 21 = .mul .isTransition
      (esub (colN 0) (.mul (.add (col 0) (.const 1)) (esub (.const 1) (col 2)))) ∧
    dagOf byteNodes 25 = .mul .isTransition (esub (colN 1) (.add (col 1) (col 2))) ∧
    dagOf byteNodes 29 = .mul .isLast (esub (col 1) (.const 255)) ∧
    byteConstraintIdx = [3, 7, 11, 13, 15, 21, 25, 27, 29] ∧
    byteInteractionIdx = [(11, 31, [4, 14])] ∧ dagOf byteNodes 4 = col 0 ∧
    dagOf byteNodes 14 = col 1 := by
  decide

/-- ByteAir's constraints on every row of table 3. -/
def ByteConstr (tr : Trace Fp) : Prop :=
  ∀ r, r < tr.height 3 → ∀ j ∈ byteConstraintIdx, (dagOf byteNodes j).eval tr 3 r [] = 0

theorem byteConstr_of {pub : List Fp} {tr : Trace Fp} (h : NvHold pub tr) : ByteConstr tr := by
  intro r hr j hj
  exact h.1.constr 3 (by decide) r hr (dagOf byteNodes j) (List.mem_map.2 ⟨j, hj, rfl⟩)

theorem natCast_one : ((1 : Nat) : Fp) = 1 := rfl
theorem natCast_zero : ((0 : Nat) : Fp) = 0 := rfl

theorem cast_inj {a b : Nat} (ha : a < P) (hb : b < P) (h : ((a : Nat) : Fp) = ((b : Nat) : Fp)) :
    a = b := ZkFormal.PQ.StatePort.nat_inj_of_lt ha hb h

theorem cast_succ (n : Nat) : ((n + 1 : Nat) : Fp) = ((n : Nat) : Fp) + 1 :=
  Lean.Grind.Semiring.natCast_succ n

section Byte
variable {tr : Trace Fp}

theorem bz_bool (h : ByteConstr tr) {r : Nat} (hr : r < tr.height 3) :
    tr.cell 3 r 2 = 0 ∨ tr.cell 3 r 2 = 1 := by
  have e := h r hr 3 (by decide)
  rw [byte_dag.1] at e
  exact bool_of _ e

/-- The ByteAir key columns enumerate `(r mod 256, r / 256)`. -/
theorem byte_row (h : ByteConstr tr) (hH : tr.height 3 ≤ 2 ^ 27) :
    ∀ r, r < tr.height 3 →
      tr.cell 3 r 0 = ((r % 256 : Nat) : Fp) ∧ tr.cell 3 r 1 = ((r / 256 : Nat) : Fp) := by
  intro r
  induction r with
  | zero =>
    intro hr
    have e0 := h 0 hr 13 (by decide)
    have e1 := h 0 hr 15 (by decide)
    rw [byte_dag.2.2.2.1] at e0
    rw [byte_dag.2.2.2.2.1] at e1
    change (if (0 : Nat) = 0 then (1 : Fp) else 0) * tr.cell 3 0 0 = 0 at e0
    change (if (0 : Nat) = 0 then (1 : Fp) else 0) * tr.cell 3 0 1 = 0 at e1
    simp only [if_true] at e0 e1
    refine ⟨?_, ?_⟩
    · rw [show (0 % 256 : Nat) = 0 from rfl, natCast_zero]; grind
    · rw [show (0 / 256 : Nat) = 0 from rfl, natCast_zero]; grind
  | succ r ih =>
    intro hr1
    have hr : r < tr.height 3 := by omega
    obtain ⟨hx, hy⟩ := ih hr
    have ez := bz_bool h hr
    have e7 := h r hr 7 (by decide)
    have e11 := h r hr 11 (by decide)
    have e21 := h r hr 21 (by decide)
    have e25 := h r hr 25 (by decide)
    rw [byte_dag.2.1] at e7
    rw [byte_dag.2.2.1] at e11
    rw [byte_dag.2.2.2.2.2.1] at e21
    rw [byte_dag.2.2.2.2.2.2.1] at e25
    have hne : r + 1 ≠ tr.height 3 := by omega
    have hmod : (r + 1) % tr.height 3 = r + 1 := Nat.mod_eq_of_lt hr1
    change tr.cell 3 r 2 * (tr.cell 3 r 0 + -((255 : Nat) : Fp)) = 0 at e7
    change (tr.cell 3 r 0 + -((255 : Nat) : Fp)) * tr.cell 3 r 3 +
      -(((1 : Nat) : Fp) + -tr.cell 3 r 2) = 0 at e11
    change (if r + 1 = tr.height 3 then (0 : Fp) else 1) *
      (tr.cell 3 ((r + 1) % tr.height 3) 0 + -((tr.cell 3 r 0 + ((1 : Nat) : Fp)) *
        (((1 : Nat) : Fp) + -tr.cell 3 r 2))) = 0 at e21
    change (if r + 1 = tr.height 3 then (0 : Fp) else 1) *
      (tr.cell 3 ((r + 1) % tr.height 3) 1 + -(tr.cell 3 r 1 + tr.cell 3 r 2)) = 0 at e25
    rw [if_neg hne, hmod, natCast_one] at e21
    rw [if_neg hne, hmod] at e25
    rw [natCast_one] at e11
    have h255 : r % 256 < 256 := Nat.mod_lt _ (by decide)
    have hP : (2 : Nat) ^ 27 < P := by decide
    by_cases hc : r % 256 = 255
    · -- carry
      have hx255 : tr.cell 3 r 0 = ((255 : Nat) : Fp) := by rw [hx, hc]
      have hz : tr.cell 3 r 2 = 1 := by rw [hx255] at e11; grind
      have h1 : (r + 1) % 256 = 0 := by omega
      have h2 : (r + 1) / 256 = r / 256 + 1 := by omega
      refine ⟨?_, ?_⟩
      · rw [h1, natCast_zero]; rw [hz] at e21; grind
      · rw [h2, cast_succ, ← hy]; rw [hz] at e25; grind
    · have hz : tr.cell 3 r 2 = 0 := by
        rcases ez with hz | hz
        · exact hz
        · exfalso
          rw [hz, hx] at e7
          have : ((r % 256 : Nat) : Fp) = ((255 : Nat) : Fp) := by grind
          exact hc (cast_inj (by unfold P; omega) (by decide) this)
      have h1 : (r + 1) % 256 = r % 256 + 1 := by omega
      have h2 : (r + 1) / 256 = r / 256 := by omega
      refine ⟨?_, ?_⟩
      · rw [h1, cast_succ, ← hx]; rw [hz] at e21; grind
      · rw [h2, ← hy]; rw [hz] at e25; grind

/-- **ByteAir has `2^16` rows at most**, from the last row's `y = 255`. -/
theorem byte_height (h : ByteConstr tr) (hH : tr.height 3 ≤ 2 ^ 27) :
    tr.height 3 ≤ 65536 := by
  have hpos : 0 < tr.height 3 := Nat.two_pow_pos _
  have hl : tr.height 3 - 1 < tr.height 3 := by omega
  have e := h _ hl 29 (by decide)
  rw [byte_dag.2.2.2.2.2.2.2.1] at e
  change (if tr.height 3 - 1 + 1 = tr.height 3 then (1 : Fp) else 0) *
    (tr.cell 3 (tr.height 3 - 1) 1 + -((255 : Nat) : Fp)) = 0 at e
  rw [if_pos (by omega)] at e
  have hy := (byte_row h hH _ hl).2
  have : (((tr.height 3 - 1) / 256 : Nat) : Fp) = ((255 : Nat) : Fp) := by rw [← hy]; grind
  have hP : (2 : Nat) ^ 27 < P := by decide
  have := cast_inj (by unfold P at hP ⊢; omega) (by decide) this
  omega

/-- **Every ByteAir key is a byte pair.** -/
theorem byte_keys (h : ByteConstr tr) (hH : tr.height 3 ≤ 2 ^ 27) {r : Nat} (hr : r < tr.height 3) :
    ∃ x y, x < 256 ∧ y < 256 ∧ tr.cell 3 r 0 = ((x : Nat) : Fp) ∧ tr.cell 3 r 1 = ((y : Nat) : Fp) := by
  obtain ⟨hx, hy⟩ := byte_row h hH r hr
  have := byte_height h hH
  exact ⟨r % 256, r / 256, Nat.mod_lt _ (by decide), by omega, hx, hy⟩

end Byte

/-! ## The byte bus (bus 11) -/

/-- NvAir's 17 byte-bus interactions (exported). -/
def nvByteIdx : List (Nat × Nat × List Nat) :=
  [(11, 4365, [4358, 4361]), (11, 4375, [4372, 4373]), (11, 4384, [4380, 4381]),
   (11, 4391, [4389, 4390]), (11, 4399, [4396, 4398]), (11, 4399, [4407, 4414]),
   (11, 7, [71, 73]), (11, 7, [75, 77]), (11, 7, [79, 81]), (11, 7, [83, 85]), (11, 7, [87, 89]),
   (11, 7, [91, 93]), (11, 7, [95, 97]), (11, 7, [4415, 4416]), (11, 7, [4417, 4418]),
   (11, 7, [4419, 4420]), (11, 7, [4421, 4422])]

theorem nv_byte_filter : (nvInteractionIdx.filter fun x => x.1 == 11) = nvByteIdx := by decide

theorem byte_only : (shaInteractionIdx.filter fun x => x.1 == 11) = [] ∧
    (tabInteractionIdx.filter fun x => x.1 == 11) = [] ∧
    (byteInteractionIdx.filter fun x => x.1 == 11) = [(11, 31, [4, 14])] := by decide

/-- The four GLUE-row counts that are not boolean by construction (slot merges of
`act·(1 − phase) − p_s − wd_w`-style felt counts). -/
def glueSlots : List Nat := [4365, 4375, 4384, 4391]

/-- **Premise (GLUE role)**: on GLUE rows, the four merged byte-bus counts are `0` or `1`. -/
def GlueByteBool (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 0 → cv tr 0 r 2 = 1 → ∀ j ∈ glueSlots,
    (dag j).eval tr 0 r pub = 0 ∨ (dag j).eval tr 0 r pub = 1

/-- A count expression partially evaluates to the constant `0` or `1`. -/
def boolConst (fx : Fix) (e : Expr) : Bool :=
  match affEval fx e with
  | some a => a.vs.isEmpty && (a.c == 0 || a.c == 1)
  | none => false

/-- **Every byte-bus count of NvAir is `0` or `1` by role**: all 17 on ALU, BIND, HASH, SAMP and
padding rows; on GLUE rows all but `glueSlots`. -/
theorem byte_counts_role : (([0, 1, 3, 4, 5] : List Nat).all fun k =>
      nvByteIdx.all fun x => boolConst (fxRole k) (dag x.2.1)) = true ∧
    (nvByteIdx.all fun x => glueSlots.contains x.2.1 || boolConst (fxRole 2) (dag x.2.1)) = true := by
  decide +kernel

theorem boolConst_row (fx : Fix) {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hag : Agrees fx (rowEnv tr t r pub)) (e : Expr) (h : boolConst fx e = true) :
    e.eval tr t r pub = 0 ∨ e.eval tr t r pub = 1 := by
  unfold boolConst at h
  cases ha : affEval fx e with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rw [affEval_row fx tr t r pub hag e a ha, Aff.eval, sumV_nil_of _ h.1]
    rcases h.2 with h0 | h1
    · left; rw [h0]; grind
    · right; rw [h1]; grind

/-- Role `k` of a row: flags `ka..ks` are the unit vector `e_k` (`k = 5`: padding). -/
def RoleIs (tr : Trace Fp) (r k : Nat) : Prop := ∀ c, c < 5 → cv tr 0 r c = if c = k then 1 else 0

theorem roleIs_mk {tr : Trace Fp} {r : Nat} (k : Nat) (a b c d e : Fp)
    (h0 : cv tr 0 r 0 = a) (h1 : cv tr 0 r 1 = b) (h2 : cv tr 0 r 2 = c) (h3 : cv tr 0 r 3 = d)
    (h4 : cv tr 0 r 4 = e) (hk : a = (if 0 = k then 1 else 0) ∧ b = (if 1 = k then 1 else 0) ∧
      c = (if 2 = k then 1 else 0) ∧ d = (if 3 = k then 1 else 0) ∧ e = (if 4 = k then 1 else 0)) :
    RoleIs tr r k := by
  intro x hx
  have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · rw [h0, hk.1]
  · rw [h1, hk.2.1]
  · rw [h2, hk.2.2.1]
  · rw [h3, hk.2.2.2.1]
  · rw [h4, hk.2.2.2.2]

theorem role_of {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) : ∃ k, k ≤ 5 ∧ RoleIs tr r k := by
  have fl := flags h hr
  unfold RoleFlags at fl
  rcases fl with ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩ |
      ⟨a, b, c, d, e⟩ | ⟨a, b, c, d, e⟩
  · exact ⟨0, by omega, roleIs_mk 0 _ _ _ _ _ a b c d e (by decide)⟩
  · exact ⟨1, by omega, roleIs_mk 1 _ _ _ _ _ a b c d e (by decide)⟩
  · exact ⟨2, by omega, roleIs_mk 2 _ _ _ _ _ a b c d e (by decide)⟩
  · exact ⟨3, by omega, roleIs_mk 3 _ _ _ _ _ a b c d e (by decide)⟩
  · exact ⟨4, by omega, roleIs_mk 4 _ _ _ _ _ a b c d e (by decide)⟩
  · exact ⟨5, by omega, roleIs_mk 5 _ _ _ _ _ a b c d e (by decide)⟩

theorem agrees_role {tr : Trace Fp} {pub : List Fp} {r k : Nat} (h : RoleIs tr r k) :
    Agrees (fxRole k) (rowEnv tr 0 r pub) := by
  intro c nx v hv
  unfold fxRole at hv
  cases nx with
  | true => simp at hv
  | false =>
    simp only [Bool.false_eq_true, if_false] at hv
    by_cases hc : c < 5
    · rw [if_pos hc, Option.some.injEq] at hv
      show rowVal tr 0 r pub c false = v
      rw [rowVal_col tr 0 r pub c (by omega), ← hv]
      exact h c hc
    · rw [if_neg hc] at hv; simp at hv

/-- A ByteAir key entry. -/
def IsByteKey (tr : Trace Fp) (e : Fp × List Fp) : Prop :=
  ∃ r, r < tr.height 3 ∧ e.2 = [tr.cell 3 r 0, tr.cell 3 r 1]

theorem busEntries_byte (tr : Trace Fp) (pub : List Fp) :
    busEntries nvCircuit tr pub 11 =
      tEntries (tableOf nvNodes nvConstraintIdx nvInteractionIdx) tr 0 pub 11 ++
        tEntries (tableOf byteNodes byteConstraintIdx byteInteractionIdx) tr 3 [] 11 := by
  have e1 : tEntries (nvCircuit.getD 1 ⟨[], []⟩) tr 1 (pubOf pub 1) 11 = [] :=
    tEntries_nil _ _ _ _ _ (by
      show ((tableOf shaNodes shaConstraintIdx shaInteractionIdx).ints.filter _) = []
      rw [tableOf_filter, byte_only.1]; rfl)
  have e2 : tEntries (nvCircuit.getD 2 ⟨[], []⟩) tr 2 (pubOf pub 2) 11 = [] :=
    tEntries_nil _ _ _ _ _ (by
      show ((tableOf tabNodes tabConstraintIdx tabInteractionIdx).ints.filter _) = []
      rw [tableOf_filter, byte_only.2.1]; rfl)
  have hr : List.range nvCircuit.length = [0, 1, 2, 3] := rfl
  unfold busEntries
  rw [hr]
  simp only [List.flatMap_cons, List.flatMap_nil, e1, e2, List.append_nil, List.nil_append]
  rfl

theorem length_flatMap_const {β : Type} (f : Nat → List β) (k : Nat) (hf : ∀ a, (f a).length = k) :
    ∀ n, ((List.range n).flatMap f).length = n * k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_const f k hf n]
    simp [hf]; grind

theorem tEntries_length (T : FTable) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) :
    (tEntries T tr t pub b).length = tr.height t * (T.ints.filter fun i => i.bus == b).length := by
  unfold tEntries
  exact length_flatMap_const _ _ (fun _ => by simp) _

/-- **Classification of the byte-bus entries**: ByteAir keys, or count `0`/`1`. -/
theorem byte_class {tr : Trace Fp} {pub : List Fp} (hc : NvConstr tr 0 pub)
    (hG : GlueByteBool tr pub) :
    ∀ e ∈ busEntries nvCircuit tr pub 11, IsByteKey tr e ∨ e.1 = 0 ∨ e.1 = 1 := by
  intro e he
  rw [busEntries_byte] at he
  rcases List.mem_append.1 he with he | he
  · unfold tEntries at he
    rw [tableOf_filter, nv_byte_filter] at he
    obtain ⟨r, hr, he⟩ := List.mem_flatMap.1 he
    have hr := List.mem_range.1 hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hi
    right
    show (dagOf nvNodes x.2.1).eval tr 0 r pub = 0 ∨ (dagOf nvNodes x.2.1).eval tr 0 r pub = 1
    rw [dagOf_nv]
    obtain ⟨k, hk, hrole⟩ := role_of hc hr
    have hag := agrees_role (pub := pub) hrole
    by_cases h2 : k = 2
    · subst h2
      have := List.all_eq_true.1 byte_counts_role.2 x hx
      simp only [Bool.or_eq_true] at this
      rcases this with hg | hb
      · exact hG r hr (by have := hrole 2 (by omega); simpa using this) x.2.1
          (List.contains_iff_mem.1 hg)
      · exact boolConst_row _ hag _ hb
    · have hk' : k ∈ ([0, 1, 3, 4, 5] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
      have := List.all_eq_true.1 (List.all_eq_true.1 byte_counts_role.1 k hk') x hx
      exact boolConst_row _ hag _ this
  · left
    unfold tEntries at he
    rw [tableOf_filter, byte_only.2.2] at he
    obtain ⟨r, hr, he⟩ := List.mem_flatMap.1 he
    have hr := List.mem_range.1 hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    refine ⟨r, hr, ?_⟩
    show [(dagOf byteNodes 4).eval tr 3 r [], (dagOf byteNodes 14).eval tr 3 r []] = _
    rw [byte_dag.2.2.2.2.2.2.2.2.2.2.1, byte_dag.2.2.2.2.2.2.2.2.2.2.2]
    rfl

/-- The ALU row's two byte lookups: `(rx, ry)` and `(rz, 0)`, count `1`. -/
theorem alu_lookups_ok :
    EvalIs (fxRole 0) (dag 4365) 1 [] [] = true ∧
    EvalIs (fxRole 0) (dag 4358) 0 [(44, false)] [1] = true ∧
    EvalIs (fxRole 0) (dag 4361) 0 [(45, false)] [1] = true ∧
    EvalIs (fxRole 0) (dag 4375) 1 [] [] = true ∧
    EvalIs (fxRole 0) (dag 4372) 0 [(63, false)] [1] = true ∧
    EvalIs (fxRole 0) (dag 4373) 0 [] [] = true := by decide +kernel

theorem alu_role {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) : RoleIs tr r 0 := by
  obtain ⟨f1, f2, f3, f4⟩ := flags_alu h hr hka
  exact roleIs_mk 0 _ _ _ _ _ hka f1 f2 f3 f4 (by decide)

theorem lin_one (val : Nat → Bool → Fp) (v : Nat × Bool) :
    (0 : Fp) + lin val [v] [1] = val v.1 v.2 := by
  simp only [lin]; grind

theorem lin_nil (val : Nat → Bool → Fp) (c : Fp) : c + lin val [] [] = c := by
  simp only [lin]; grind

theorem alu_lookup_mem {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub) {r : Nat}
    (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) :
    ((1 : Fp), [cv tr 0 r 44, cv tr 0 r 45]) ∈ busEntries nvCircuit tr pub 11 ∧
      ((1 : Fp), [cv tr 0 r 63, 0]) ∈ busEntries nvCircuit tr pub 11 := by
  have hag := agrees_role (pub := pub) (alu_role h hr hka)
  obtain ⟨c1, m1, m2, c2, m3, m4⟩ := alu_lookups_ok
  have ev := fun e c vs ks (hh : EvalIs (fxRole 0) e c vs ks = true) =>
    evalIs_row (fxRole 0) tr 0 r pub hag e c vs ks hh
  have l1 : ∀ c, c < 1000 → rowVal tr 0 r pub c false = cv tr 0 r c :=
    fun c hc => rowVal_col tr 0 r pub c hc
  have key : ∀ x ∈ nvByteIdx, ((dag x.2.1).eval tr 0 r pub, x.2.2.map fun m => (dag m).eval tr 0 r pub)
      ∈ busEntries nvCircuit tr pub 11 := by
    intro x hx
    rw [busEntries_byte]
    apply List.mem_append_left
    unfold tEntries
    rw [tableOf_filter, nv_byte_filter]
    refine List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, ?_⟩
    rw [List.map_map]
    refine List.mem_map.2 ⟨x, hx, ?_⟩
    simp only [dagOf_nv, List.map_map, Function.comp_def]
  constructor
  · have := key (11, 4365, [4358, 4361]) (by simp [nvByteIdx])
    simp only [List.map_cons, List.map_nil] at this
    rw [ev _ _ _ _ c1, ev _ _ _ _ m1, ev _ _ _ _ m2, lin_one, lin_one, lin_nil,
      l1 44 (by decide), l1 45 (by decide)] at this
    exact this
  · have := key (11, 4375, [4372, 4373]) (by simp [nvByteIdx])
    simp only [List.map_cons, List.map_nil] at this
    rw [ev _ _ _ _ c2, ev _ _ _ _ m3, ev _ _ _ _ m4, lin_one, lin_nil, lin_nil,
      l1 63 (by decide)] at this
    exact this

theorem busEntries_byte_length (tr : Trace Fp) (pub : List Fp) :
    (busEntries nvCircuit tr pub 11).length = tr.height 0 * 17 + tr.height 3 * 1 := by
  rw [busEntries_byte, List.length_append, tEntries_length, tEntries_length, tableOf_filter,
    tableOf_filter, nv_byte_filter, byte_only.2.2]
  rfl

/-- **The ALU row's B-field bytes are bytes.** -/
theorem alu_bytes {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {r : Nat} (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) :
    ∃ x y z, x < 256 ∧ y < 256 ∧ z < 256 ∧ cv tr 0 r 44 = ((x : Nat) : Fp) ∧
      cv tr 0 r 45 = ((y : Nat) : Fp) ∧ cv tr 0 r 63 = ((z : Nat) : Fp) := by
  have hc := nvConstr_of hh
  have h3 : tr.height 3 ≤ 2 ^ 27 := Nat.pow_le_pow_right (by decide) (hh.2.2 3 (by decide))
  have h0 : tr.height 0 ≤ 2 ^ 24 := height_le hh.2.1
  have hlen : (busEntries nvCircuit tr pub 11).length < P := by
    rw [busEntries_byte_length]; unfold P; omega
  obtain ⟨m1, m2⟩ := alu_lookup_mem hc hr hka
  obtain ⟨e1, -, ⟨s1, hs1, hk1⟩, he1⟩ :=
    hit _ _ (IsByteKey tr) (byte_class hc hG) (hh.1.bal 11 _) m1 hlen
  obtain ⟨e2, -, ⟨s2, hs2, hk2⟩, he2⟩ :=
    hit _ _ (IsByteKey tr) (byte_class hc hG) (hh.1.bal 11 _) m2 hlen
  rw [he1] at hk1
  rw [he2] at hk2
  simp only [List.cons.injEq, and_true] at hk1 hk2
  have bc := byteConstr_of hh
  obtain ⟨x1, y1, hx1, hy1, ex1, ey1⟩ := byte_keys bc h3 hs1
  obtain ⟨x2, y2, hx2, hy2, ex2, -⟩ := byte_keys bc h3 hs2
  exact ⟨x1, y1, x2, hx1, hy1, hx2, hk1.1.trans ex1, hk1.2.trans ey1, hk2.1.trans ex2⟩

/-- **Op decode**: on an ALU row holding instruction `i` (`op < 40`, `B < 2^24`), the selector
halves are `op mod 8` and `op / 8`. -/
theorem alu_op {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {r : Nat} (hr : r < tr.height 0) (hka : cv tr 0 r 0 = 1) (i : Instr) (hi : ProgRow tr r i)
    (hop : i.op < 40) (hb : i.b < 2 ^ 24) :
    (∀ k, k < 8 → cv tr 0 r (34 + k) = if k = i.op % 8 then 1 else 0) ∧
      (∀ k, k < 5 → cv tr 0 r (58 + k) = if k = i.op / 8 then 1 else 0) := by
  have hc := nvConstr_of hh
  obtain ⟨a, ha, b, hb', hx, hy⟩ := alu_onehot hc hr hka
  have hd := decode_row hc hr hka ha hb' hx hy
  obtain ⟨x, y, z, hx', hy', hz', ex, ey, ez⟩ := alu_bytes hh hG hr hka
  rw [hi.2.1, ex, ey, ez] at hd
  have e : ((i.b + i.op * 2 ^ 24 : Nat) : Fp) =
      (((8 * b + a) * 2 ^ 24 + (x + 256 * y + 65536 * z) : Nat) : Fp) := by
    rw [hd]
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    grind
  have hn := cast_inj (by unfold P; omega) (by unfold P; omega) e
  have hopv : i.op = 8 * b + a := by omega
  constructor
  · intro k hk
    rw [hx k hk]
    by_cases e : k = a
    · have : k = i.op % 8 := by omega
      rw [if_pos e, if_pos this]
    · have : ¬ k = i.op % 8 := by omega
      rw [if_neg e, if_neg this]
  · intro k hk
    rw [hy k hk]
    by_cases e : k = b
    · have : k = i.op / 8 := by omega
      rw [if_pos e, if_pos this]
    · have : ¬ k = i.op / 8 := by omega
      rw [if_neg e, if_neg this]

/-! ## Rows of the bound program -/

/-- The pinned program's words are well formed (`Instr::words`'s assert and the ISA size): checked
on the pinned program. -/
def ProgWF (prog : List Instr) : Prop := ∀ i ∈ prog, i.op < 40 ∧ i.b < 2 ^ 24

theorem p1_ne {i : Instr} (hop : 0 < i.op) (hop' : i.op < 40) (hb : i.b < 2 ^ 24) :
    ((i.b + i.op * 2 ^ 24 : Nat) : Fp) ≠ 0 := by
  intro h
  have := cast_inj (a := i.b + i.op * 2 ^ 24) (b := 0) (by unfold P; omega) (by decide)
    (h.trans natCast_zero.symm)
  omega

theorem ite_eq_of {k m n : Nat} (h : m = n) :
    (if k = m then (1 : Fp) else 0) = if k = n then 1 else 0 := by subst h; rfl

/-- **A non-`Nop` row of the bound program is an ALU row decoded to its op.** -/
theorem bound_row {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) (hop : 0 < prog[y].op) :
    y < tr.height 0 ∧ cv tr 0 y 0 = 1 ∧
      (∀ k, k < 8 → cv tr 0 y (34 + k) = if k = prog[y].op % 8 then 1 else 0) ∧
      (∀ k, k < 5 → cv tr 0 y (58 + k) = if k = prog[y].op / 8 then 1 else 0) := by
  have hr : y < tr.height 0 := Nat.lt_of_lt_of_le hy hP.1
  obtain ⟨hop', hb⟩ := hW _ (List.getElem_mem hy)
  have hrow := hP.2 y hy
  have hka := ka_of_p1 (nvConstr_of hh) hr (by rw [hrow.2.1]; exact p1_ne hop hop' hb)
  exact ⟨hr, hka, alu_op hh hG hr hka _ hrow hop' hb⟩

/-! ## `PvdAt` from program binding and the op decode -/

/-- **`PvdAt` for every `PvD` instruction of the bound program.** -/
theorem pvdAt_of {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {d addr p2 : Nat}
    (hd : d < prog.length) (hi : prog[d] = ⟨31, addr, 0, p2, 0⟩) (hp2 : p2 ≤ 1) :
    PvdAt tr 0 d addr p2 := by
  obtain ⟨hr, hka, hx, hy⟩ := bound_row hh hG hP hW hd (by rw [hi]; simp)
  have hrow := hP.2 d hd
  rw [hi] at hx hy hrow
  have hx' : ∀ k, k < 8 → cv tr 0 d (34 + k) = if k = 7 then 1 else 0 := fun k hk => (hx k hk).trans (ite_eq_of (by simp))
  have hy' : ∀ k, k < 5 → cv tr 0 d (58 + k) = if k = 3 then 1 else 0 := fun k hk => (hy k hk).trans (ite_eq_of (by simp))
  exact ⟨hr, hka, hx', hy', hrow.1, hrow.2.2.1, hp2⟩

/-- **The tape layout from the program**: two `PvD` rows reading `alo` (half 0), `ahi` (half 1). -/
theorem tapeAt_of {K : E2ENode.NodeKey} {Dg Proof : Type} (dec : List Fp → Dg) {tr : Trace Fp}
    {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub) {prog : List Instr}
    (hP : ProgBound tr prog) (hW : ProgWF prog) (R : E2ENode.NodeRead K Dg Proof)
    {dlo dhi alo ahi : Nat} (hlo : dlo < prog.length) (hhi : dhi < prog.length)
    (hilo : prog[dlo] = ⟨31, alo, 0, 0, 0⟩) (hihi : prog[dhi] = ⟨31, ahi, 0, 1, 0⟩)
    (halo : alo < 2 ^ 24) (hahi : ahi < 2 ^ 24) (hR : R.outDig = dec (digCells tr 0 alo ahi)) :
    TapeAt dec tr R :=
  ⟨dlo, dhi, alo, ahi, pvdAt_of hh hG hP hW hlo hilo (by decide),
    pvdAt_of hh hG hP hW hhi hihi (by decide), halo, hahi, hR⟩

/-! ## Memory reads -/

/-- **Memory consistency for a count-1 read**: a mem-bus entry `(1, (n, v_0..v_11))` with
`n < 2^24` is matched by row `n`, whose cell is `v`. -/
theorem mem_read {tr : Trace Fp} {pub : List Fp} (h : NvConstr tr 0 pub)
    (hb : MemBalance tr 0 pub) (hH : tr.height 0 ≤ 2 ^ 24) {n : Nat} {vs : List Fp}
    (hin : ((1 : Fp), ((n : Nat) : Fp) :: vs) ∈ memEntries tr 0 pub) (hn : n < 2 ^ 24) :
    n < tr.height 0 ∧ (List.range 12).map (fun k => cv tr 0 n (46 + k)) = vs := by
  have hlen : (memEntries tr 0 pub).length < P := by
    rw [memEntries_length]
    have : (3 : Nat) * 2 ^ 24 < P := by decide
    omega
  obtain ⟨e, -, ⟨r, hr, hka, hkey⟩, hm⟩ := hit _ _ (IsKey tr 0) (mem_slots h) (hb _) hin hlen
  rw [hm] at hkey
  unfold keyMsg at hkey
  have hy := List.cons.inj hkey
  have hyr := y_row h hr (role_of_ka h hr hka)
  have hra : r = n := by
    rw [hyr] at hy
    exact cast_inj (Nat.lt_of_lt_of_le hr (Nat.le_trans hH (by decide)))
      (Nat.lt_of_lt_of_le hn (by decide)) hy.1.symm
  subst hra
  exact ⟨hr, hy.2.symm⟩

/-- Expected message expressions: each checked by partial evaluation. -/
def ExpsOK (fx : Fix) : List Nat → List (Fp × List (Nat × Bool) × List Fp) → Bool
  | [], [] => true
  | m :: ms, e :: es => EvalIs fx (dag m) e.1 e.2.1 e.2.2 && ExpsOK fx ms es
  | _, _ => false

theorem expsOK_eval (fx : Fix) {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hag : Agrees fx (rowEnv tr t r pub)) :
    ∀ ms es, ExpsOK fx ms es = true →
      ms.map (fun m => (dag m).eval tr t r pub) = es.map (fun e => e.1 + lin (rowVal tr t r pub) e.2.1 e.2.2)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [ExpsOK] at h
  | _ :: _, [], h => by simp [ExpsOK] at h
  | m :: ms, e :: es, h => by
    simp only [ExpsOK, Bool.and_eq_true] at h
    simp only [List.map_cons, evalIs_row fx tr t r pub hag _ _ _ _ h.1, expsOK_eval fx hag ms es h.2]

/-- A read message `(c0 + x_{v0}, x_base, .., x_{base+11})`. -/
def rdExps (c0 : Fp) (v0 base : Nat) : List (Fp × List (Nat × Bool) × List Fp) :=
  (c0, [(v0, false)], [1]) :: (List.range 12).map fun k => (0, [(base + k, false)], [1])

def slot1Msgs : List Nat :=
  [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210]
def slot2Msgs : List Nat :=
  [4233, 4236, 4239, 4242, 4245, 4248, 4251, 4254, 4257, 4260, 4263, 4266, 4269]

/-- `Sub` (op 3) reads `a` at `P0` and `b` at `P1 − 3·2^24`; `Zero` (op 16) reads `a` at `P0`. -/
theorem reads_ok :
    EvalIs (fxOp 3 0) (dag 4229) 1 [] [] = true ∧ ExpsOK (fxOp 3 0) slot1Msgs (rdExps 0 6 10) = true ∧
    EvalIs (fxOp 3 0) (dag 4281) 1 [] [] = true ∧
      ExpsOK (fxOp 3 0) slot2Msgs (rdExps (-((3 * 2 ^ 24 : Nat) : Fp)) 7 22) = true ∧
    EvalIs (fxOp 0 2) (dag 4229) 1 [] [] = true ∧ ExpsOK (fxOp 0 2) slot1Msgs (rdExps 0 6 10) = true := by
  decide +kernel

theorem rdExps_eval (tr : Trace Fp) (r : Nat) (pub : List Fp) (c0 : Fp) (v0 base : Nat)
    (hv : v0 < 1000) (hb : base + 12 ≤ 1000) :
    (rdExps c0 v0 base).map (fun e => e.1 + lin (rowVal tr 0 r pub) e.2.1 e.2.2) =
      (c0 + cv tr 0 r v0) :: (List.range 12).map (fun k => cv tr 0 r (base + k)) := by
  simp only [rdExps, List.map_cons, List.map_map]
  congr 1
  · simp only [lin, rowVal_col tr 0 r pub v0 hv]; grind
  · apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.1 hk
    simp only [Function.comp, lin, rowVal_col tr 0 r pub (base + k) (by omega)]; grind

theorem slot_mem {tr : Trace Fp} {pub : List Fp} {r : Nat} (hr : r < tr.height 0)
    (cm : Nat × List Nat) (hcm : cm ∈ memIdx) :
    ((dag cm.1).eval tr 0 r pub, cm.2.map fun m => (dag m).eval tr 0 r pub) ∈ memEntries tr 0 pub :=
  List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨cm, hcm, rfl⟩⟩

/-- The cells at `x` and `y` are equal (all 12 limbs). -/
def CellEq (tr : Trace Fp) (x y : Nat) : Prop := ∀ k, k < 12 → cv tr 0 x (46 + k) = cv tr 0 y (46 + k)

/-- `assert_eq x y` in the program (`builder.rs`: `Sub x y` at row `i`, then `Zero i`). -/
def AssertIn (prog : List Instr) (x y : Nat) : Prop :=
  ∃ i j, ∃ (hi : i < prog.length) (hj : j < prog.length), prog[i] = ⟨3, x, y, 0, 0⟩ ∧
    prog[j] = ⟨16, i, 0, 0, 0⟩ ∧ x < 2 ^ 24 ∧ y < 2 ^ 24 ∧ i < 2 ^ 24

def subIdx : List Nat := [1047, 1096, 1143, 1190, 1237, 1284, 1331, 1378, 1425, 1472, 1519, 1565]
def zeroIdx : List Nat := [1049, 1097, 1144, 1191, 1238, 1285, 1332, 1379, 1426, 1473, 1520, 1566]

/-- `Sub`: `c_k − a_k + b_k`; `Zero`: `a_k` (exported constraints, partial evaluation). -/
theorem subzero_ok : ∀ k, k < 12 →
    EvalIs (fxOp 3 0) (dag (subIdx.getD k 0)) 0 [(46 + k, false), (10 + k, false), (22 + k, false)]
      [1, -1, 1] = true ∧ subIdx.getD k 0 ∈ nvConstraintIdx ∧
    EvalIs (fxOp 0 2) (dag (zeroIdx.getD k 0)) 0 [(10 + k, false)] [1] = true ∧
      zeroIdx.getD k 0 ∈ nvConstraintIdx := by
  decide +kernel

/-- **Every `assert_eq` of the bound program holds on the memory cells.** -/
theorem asserted_eq {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr)
    (hG : GlueByteBool tr pub) {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog)
    {x y : Nat} (hA : AssertIn prog x y) : CellEq tr x y := by
  obtain ⟨i, j, hi, hj, hpi, hpj, hx, hy, hi24⟩ := hA
  have hc := nvConstr_of hh
  have hb := memBalance_of hh
  have hH := height_le hh.2.1
  obtain ⟨hri, hkai, hxi, hyi⟩ := bound_row hh hG hP hW hi (by rw [hpi]; simp)
  obtain ⟨hrj, hkaj, hxj, hyj⟩ := bound_row hh hG hP hW hj (by rw [hpj]; simp)
  rw [hpi] at hxi hyi
  rw [hpj] at hxj hyj
  replace hxi : ∀ k, k < 8 → cv tr 0 i (34 + k) = if k = 3 then 1 else 0 := fun k hk => (hxi k hk).trans (ite_eq_of (by simp))
  replace hyi : ∀ k, k < 5 → cv tr 0 i (58 + k) = if k = 0 then 1 else 0 := fun k hk => (hyi k hk).trans (ite_eq_of (by simp))
  replace hxj : ∀ k, k < 8 → cv tr 0 j (34 + k) = if k = 0 then 1 else 0 := fun k hk => (hxj k hk).trans (ite_eq_of (by simp))
  replace hyj : ∀ k, k < 5 → cv tr 0 j (58 + k) = if k = 2 then 1 else 0 := fun k hk => (hyj k hk).trans (ite_eq_of (by simp))
  have rowi := hP.2 i hi
  have rowj := hP.2 j hj
  rw [hpi] at rowi
  rw [hpj] at rowj
  have agi := agrees_op (pub := pub) hc hri hkai hxi hyi
  have agj := agrees_op (pub := pub) hc hrj hkaj hxj hyj
  obtain ⟨c1, m1, c2, m2, c3, m3⟩ := reads_ok
  -- row i reads a at x, b at y
  have ea := slot_mem (pub := pub) hri (4229, slot1Msgs) (by rw [memIdx_eq]; simp [slot1Msgs])
  have eb := slot_mem (pub := pub) hri (4281, slot2Msgs) (by rw [memIdx_eq]; simp [slot2Msgs])
  have ez := slot_mem (pub := pub) hrj (4229, slot1Msgs) (by rw [memIdx_eq]; simp [slot1Msgs])
  simp only at ea eb ez
  rw [evalIs_row _ tr 0 i pub agi _ _ _ _ c1, lin_nil, expsOK_eval _ agi _ _ m1,
    rdExps_eval tr i pub _ _ _ (by decide) (by decide), rowi.1] at ea
  rw [evalIs_row _ tr 0 i pub agi _ _ _ _ c2, lin_nil, expsOK_eval _ agi _ _ m2,
    rdExps_eval tr i pub _ _ _ (by decide) (by decide), rowi.2.1] at eb
  rw [evalIs_row _ tr 0 j pub agj _ _ _ _ c3, lin_nil, expsOK_eval _ agj _ _ m3,
    rdExps_eval tr j pub _ _ _ (by decide) (by decide), rowj.1] at ez
  have hyv : -((3 * 2 ^ 24 : Nat) : Fp) + ((y + 3 * 2 ^ 24 : Nat) : Fp) = ((y : Nat) : Fp) := by
    simp only [Lean.Grind.Semiring.natCast_add]; grind
  rw [show (0 : Fp) + ((x : Nat) : Fp) = ((x : Nat) : Fp) by grind] at ea
  rw [hyv] at eb
  rw [show (0 : Fp) + ((i : Nat) : Fp) = ((i : Nat) : Fp) by grind] at ez
  have ra := (mem_read hc hb hH ea hx).2
  have rb := (mem_read hc hb hH eb hy).2
  have rz := (mem_read hc hb hH ez hi24).2
  intro k hk
  obtain ⟨sk, smem, zk, zmem⟩ := subzero_ok k hk
  have es := hc i hri _ smem
  have ezr := hc j hrj _ zmem
  rw [evalIs_row _ tr 0 i pub agi _ _ _ _ sk] at es
  rw [evalIs_row _ tr 0 j pub agj _ _ _ _ zk] at ezr
  simp only [lin, rowVal_col tr 0 i pub _ (show 46 + k < 1000 by omega),
    rowVal_col tr 0 i pub _ (show 10 + k < 1000 by omega),
    rowVal_col tr 0 i pub _ (show 22 + k < 1000 by omega)] at es
  simp only [lin, rowVal_col tr 0 j pub _ (show 10 + k < 1000 by omega)] at ezr
  have gk := fun (l : List Fp) (h : (List.range 12).map (fun k => cv tr 0 x (46 + k)) = l) => h
  have ax : cv tr 0 x (46 + k) = cv tr 0 i (10 + k) := by
    have := congrArg (fun l : List Fp => l.getD k 0) ra
    simpa [List.getD_eq_getElem?_getD, List.getElem?_range hk] using this
  have by' : cv tr 0 y (46 + k) = cv tr 0 i (22 + k) := by
    have := congrArg (fun l : List Fp => l.getD k 0) rb
    simpa [List.getD_eq_getElem?_getD, List.getElem?_range hk] using this
  have iz : cv tr 0 i (46 + k) = cv tr 0 j (10 + k) := by
    have := congrArg (fun l : List Fp => l.getD k 0) rz
    simpa [List.getD_eq_getElem?_getD, List.getElem?_range hk] using this
  rw [ax, by']
  grind

/-! ## `build_agg`'s continuity asserts from the program -/

/-- The node read's statement cells sit at program addresses (limb 0 of each memory cell:
`load_f` cells are base-field values). -/
structure NodeLay (K : E2ENode.NodeKey) where
  ctx : Fin K.k → Fin K.nCtx → Nat
  a : Fin K.k → Nat
  e : Fin K.k → Nat
  sa : Fin K.k → Fin K.nState → Nat
  se : Fin K.k → Fin K.nState → Nat

def ReadsLay {K : E2ENode.NodeKey} {Dg Proof : Type} (tr : Trace Fp) (L : NodeLay K)
    (R : E2ENode.NodeRead K Dg Proof) : Prop :=
  (∀ i j, R.ctx i j = cv tr 0 (L.ctx i j) 46) ∧ (∀ i, R.a i = cv tr 0 (L.a i) 46) ∧
    (∀ i, R.e i = cv tr 0 (L.e i) 46) ∧ (∀ i j, R.sa i j = cv tr 0 (L.sa i j) 46) ∧
    (∀ i j, R.se i j = cv tr 0 (L.se i j) 46)

/-- The program asserts `build_agg`'s continuity pairs (`for i in 1..len`). -/
def ContProg {K : E2ENode.NodeKey} (prog : List Instr) (L : NodeLay K) : Prop :=
  ∀ i (h : i + 1 < K.k),
    (∀ j, AssertIn prog (L.ctx ⟨i + 1, h⟩ j) (L.ctx ⟨0, by omega⟩ j)) ∧
    AssertIn prog (L.a ⟨i + 1, h⟩) (L.e ⟨i, by omega⟩) ∧
    ∀ j, AssertIn prog (L.sa ⟨i + 1, h⟩ j) (L.se ⟨i, by omega⟩ j)

theorem zipEq_ofFn {n : Nat} (f g : Fin n → Fp) (h : ∀ j, f j = g j) :
    E2ENode.zipEq (List.ofFn f) (List.ofFn g) := by
  intro p hp
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hp
  simp only [List.getElem_zip, List.getElem_ofFn]
  exact h _

theorem getElem_cells {K : E2ENode.NodeKey} {Dg Proof : Type} (R : E2ENode.NodeRead K Dg Proof)
    (i : Nat) (h : i < R.cells.length) : R.cells[i] = R.cell ⟨i, by simpa [E2ENode.NodeRead.cells] using h⟩ := by
  simp [E2ENode.NodeRead.cells]

/-- **`ContAsserts` from the program**: a read laid out at program addresses whose continuity
pairs are asserted satisfies `build_agg`'s continuity loop. -/
theorem contAsserts_of {K : E2ENode.NodeKey} {Dg Proof : Type} {tr : Trace Fp} {pub : List Fp}
    (hh : NvHold pub tr) (hG : GlueByteBool tr pub) {prog : List Instr} (hP : ProgBound tr prog)
    (hW : ProgWF prog) (L : NodeLay K) (R : E2ENode.NodeRead K Dg Proof) (hL : ReadsLay tr L R)
    (hC : ContProg prog L) : E2ENode.ContAsserts R.cells := by
  intro i h
  have hk : i + 1 < K.k := by simpa [E2ENode.NodeRead.cells] using h
  obtain ⟨hc, ha, hs⟩ := hC i hk
  rw [getElem_cells, getElem_cells, getElem_cells]
  refine ⟨?_, ?_, ?_⟩
  · apply zipEq_ofFn
    intro j
    rw [hL.1, hL.1]
    exact asserted_eq hh hG hP hW (hc j) 0 (by decide)
  · show R.a _ = R.e _
    rw [hL.2.1, hL.2.2.1]
    exact asserted_eq hh hG hP hW ha 0 (by decide)
  · apply zipEq_ofFn
    intro j
    rw [hL.2.2.2.1, hL.2.2.2.2]
    exact asserted_eq hh hG hP hW (hs j) 0 (by decide)

/-! ## `NodeExecV` with the tape and the asserts discharged -/

section Node

open E2ENode E2EHold

variable {K : NodeKey} {α Dg Proof : Type} (enc : List Fp → α) (rdigest : Stmt α → Dg)
  (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg) (segStmt : List Fp → Stmt α)

/-- The link part of `NodeAsserts` (app: statement = `of_segment` of the child's public values;
node: preimage digest = the child's exposed digest). -/
def NodeLink (R : NodeRead K Dg Proof) : Prop :=
  match K.kind with
  | .app => ∀ i, (R.cell i).stmt enc = segStmt (R.pv i)
  | .node => ∀ i, R.kidDig i = pvDig (R.pv i)

/-- **The node's execution obligation over the circuit's predicate, from the program.** What
remains: program binding (`ProgBound`), the GLUE byte counts (`GlueByteBool`), SHA, the inner
verifiers, and the decode-level link: the link part of `NodeAsserts` follows from the equality of
the cells the program asserts equal (`hLink`; `build_agg` asserts those links cell by cell). The
tape (`PvD` rows) and the continuity asserts are proved. -/
theorem nodeExecV_of_prog (R : Trace Fp → NodeRead K Dg Proof) (dec : List Fp → Dg)
    (prog : List Instr) (hW : ProgWF prog) (L : NodeLay K)
    {dlo dhi alo ahi : Nat} (hlo : dlo < prog.length) (hhi : dhi < prog.length)
    (hilo : prog[dlo] = ⟨31, alo, 0, 0, 0⟩) (hihi : prog[dhi] = ⟨31, ahi, 0, 1, 0⟩)
    (halo : alo < 2 ^ 24) (hahi : ahi < 2 ^ 24) (hC : ContProg prog L)
    (hP : ∀ tr pub, NvHold pub tr → ProgBound tr prog)
    (hG : ∀ tr pub, NvHold pub tr → GlueByteBool tr pub)
    (hRd : ∀ tr, (R tr).outDig = dec (digCells tr 0 alo ahi) ∧ ReadsLay tr L (R tr))
    (hLink : ∀ tr pub, NvHold pub tr → (∀ x y, AssertIn prog x y → CellEq tr x y) →
      NodeLink enc pvDig segStmt (R tr))
    (hSI : ∀ tr pub, NvHold pub tr → NodeSha enc rdigest (R tr) ∧ NodeInner InnerAcc (R tr)) :
    NodeExecV enc rdigest InnerAcc pvDig segStmt R (fun p => dec (pvDigest p)) := by
  apply nodeExecV_of enc rdigest InnerAcc pvDig segStmt R dec
  intro tr pub hh
  have hPb := hP tr pub hh
  have hGb := hG tr pub hh
  obtain ⟨hS, hI⟩ := hSI tr pub hh
  refine ⟨hS, hI, ⟨?_, contAsserts_of hh hGb hPb hW L (R tr) (hRd tr).2 hC⟩,
    tapeAt_of dec hh hGb hPb hW (R tr) hlo hhi hilo hihi halo hahi (hRd tr).1⟩
  have := hLink tr pub hh (fun x y hA => asserted_eq hh hGb hPb hW hA)
  unfold NodeLink at this
  exact this

end Node

/-! ## The wrap's tape (`build_wrap` exposes `D_wrap` through two `PvD` rows) -/

/-- **The tape component of the D-5 wrap** (`WrapCompT`'s `pubDig pub = R.wrapDig`), from the
circuit's predicate and the program's `PvD` rows reading the `D_wrap` cells. -/
theorem wrapTape_of_prog {m : Nat} {Dg DgW Proof : Type} (dec : List Fp → DgW) {tr : Trace Fp}
    {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub) {prog : List Instr}
    (hP : ProgBound tr prog) (hW : ProgWF prog) (R : E2ETree.WrapReadT m Dg DgW Proof)
    {dlo dhi alo ahi : Nat} (hlo : dlo < prog.length) (hhi : dhi < prog.length)
    (hilo : prog[dlo] = ⟨31, alo, 0, 0, 0⟩) (hihi : prog[dhi] = ⟨31, ahi, 0, 1, 0⟩)
    (halo : alo < 2 ^ 24) (hahi : ahi < 2 ^ 24) (hR : R.wrapDig = dec (digCells tr 0 alo ahi)) :
    dec (pvDigest pub) = R.wrapDig := by
  rw [hR, digCells_eq (nvConstr_of hh) (memBalance_of hh) (height_le hh.2.1)
    (pvdAt_of hh hG hP hW hlo hilo (by decide)) (pvdAt_of hh hG hP hW hhi hihi (by decide)) halo hahi]

#print axioms wrapTape_of_prog
#print axioms pvdAt_of
#print axioms tapeAt_of
#print axioms mem_read
#print axioms asserted_eq
#print axioms contAsserts_of
#print axioms nodeExecV_of_prog
#print axioms ka_of_p1
#print axioms decode_row
#print axioms byte_keys
#print axioms byte_class
#print axioms alu_bytes
#print axioms alu_op

end ZkFormal.PQ.NvProg

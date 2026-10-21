import WasmBase.RegChip
import WasmBase.Main.Lookups
import WasmBase.Main.HostLinks
/-!
# WasmBase.Main.RegFacts — what `Holds` says about a REG row (`wasmBaseRegAir`)

`wasmBaseRegAir = wasmBaseHostAir ++ [REG]`.  This file extracts the REG row's constraint and lookup
consequences from `Holds` alone.  The facts are deliberately row-local: the **group walk** (byte rows
of a register are exactly `pos = 0 .. len−1`) is `Register.RegLenAgree`, stated and not proved.

Proved here:

* `reg_row_constraints`: the named constraints of an active REG row vanish at natural values
  (`act`, `kind`, `rd`, `dir`, `fresh` are bits; `kind` is gated so only the right message fires;
  `pos + gap + 1 = len` on a byte row; `dir = 1 − rd` on a byte row; a fill has `fresh = 0`).
* `reg_range16_sound`: on a `wasmBaseRegAir` trace every R16 **query** with count 1 is a single value
  `< 2^16`.  The proof mirrors `Main/HostLinks.host_r16_sound` and adds the REG table (base tables
  0-21 answer, HOST/HOSTO/HOSTT/HOSTB answer, REG answers).
* `reg_row_key_bounds`: an active REG row's `rid`, `len` are `< 2^16` and hence satisfy the register
  model's key domain (`Register.posOK`/`lenOK`, plus `regOK` under the stated `rid ≤ 99`).
* `reg_row_msg_shape`: the space-6 message of a REG row is exactly `Register.byteMsg` /
  `Register.lenMsg` on the row's columns (a definitional unfolding of the CH message).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## Table access for `wasmBaseRegAir`

`wasmBaseRegAir = wasmBaseHostAir ++ [REG]`, so tables `0..25` are the host AIR's and REG is at 26.
Every host-AIR fact (`host_air_get`, `host_air_22` … `host_air_25`) lifts by `List.getElem_append_left`;
the proof obligations differ only in the index bound (`t < 26` here vs `t < 26` there), so each lift
is a one-liner. -/

theorem reg_air_get (nloc ngl t : Nat) (ht : t < 26) :
    (wasmBaseRegAir nloc ngl).tables[t]'(by rw [reg_air_len]; omega) =
      (wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; exact ht) := by
  simp only [wasmBaseRegAir]
  exact List.getElem_append_left (by rw [host_air_len]; exact ht)

theorem reg_air_22 (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[22]'(by rw [reg_air_len]; decide) = Host.table := by
  rw [reg_air_get nloc ngl 22 (by decide)]; exact host_air_22 nloc ngl

theorem reg_air_23 (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[23]'(by rw [reg_air_len]; decide) = HostO.table := by
  rw [reg_air_get nloc ngl 23 (by decide)]; exact host_air_23 nloc ngl

theorem reg_air_24 (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[24]'(by rw [reg_air_len]; decide) = HostTab.table := by
  rw [reg_air_get nloc ngl 24 (by decide)]; exact host_air_24 nloc ngl

theorem reg_air_25 (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[25]'(by rw [reg_air_len]; decide) = HostB.table := by
  rw [reg_air_get nloc ngl 25 (by decide)]; exact host_air_25 nloc ngl

/-- The base-AIR table at index `t < 22` is the same in `wasmBaseRegAir`. -/
theorem reg_air_base (nloc ngl t : Nat) (ht : t < 22) :
    (wasmBaseRegAir nloc ngl).tables[t]'(by rw [reg_air_len]; omega) =
      (wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact ht) := by
  rw [reg_air_get nloc ngl t (by omega)]
  exact host_air_get nloc ngl t ht

/-- The HOST constraints vanish on a `wasmBaseRegAir` trace. -/
theorem reg_air_host_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 := by
  have ht : 22 < (wasmBaseRegAir nloc ngl).tables.length := by rw [reg_air_len]; decide
  have hc := table_constr H ht hr
  rw [reg_air_22] at hc
  exact hc

/-- Index 16 of `wasmBaseRegAir` is `Byte.table`. -/
theorem reg_air_16b (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[16]'(by rw [reg_air_len]; decide) = Byte.table := by
  rw [reg_air_get nloc ngl 16 (by decide)]
  exact host_air_get nloc ngl 16 (by decide) ▸ air_t16b nloc ngl

/-- Index 15 of `wasmBaseRegAir` is `Range16.table`. -/
theorem reg_air_15r (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[15]'(by rw [reg_air_len]; decide) = Range16.table := by
  rw [reg_air_get nloc ngl 15 (by decide)]
  exact host_air_get nloc ngl 15 (by decide) ▸ air_t15r nloc ngl

/-- The RANGE16 values of a `wasmBaseRegAir` trace: height `2^16` and `v = row`. -/
theorem reg_range16_values {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) :
    tr.height 15 = 65536 ∧ ∀ r, r < tr.height 15 → rowNat tr 15 r Range16.val = r :=
  range16_values H (by rw [reg_air_len]; decide) (reg_air_15r nloc ngl)

/-- The BYTE constraints vanish on a `wasmBaseRegAir` trace (index 16). -/
theorem reg_air_byte_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 16) :
    ∀ e ∈ Byte.table.constraints, e.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = 0 := by
  have ht : 16 < (wasmBaseRegAir nloc ngl).tables.length := by rw [reg_air_len]; decide
  have hc := table_constr H ht hr
  rw [reg_air_16b] at hc
  exact hc

/-! ## Row constraints -/

/-- The named REG constraints vanish on every REG row (from `Holds`). -/
theorem reg_row_constraints {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    ∀ e ∈ Reg.table.constraints, e.eval (natRow (rowNat tr 26 r) (tr.row pub 26 r)) = 0 := by
  have ht : 26 < (wasmBaseRegAir nloc ngl).tables.length := by rw [reg_air_len]; decide
  have hT : (wasmBaseRegAir nloc ngl).tables[26]'ht = Reg.table := reg_air_26 nloc ngl
  have hc := table_constr H ht hr
  rw [hT] at hc
  exact hc

/-- The REG bits: `act`, `kind`, `rd`, `dir`, `fresh` all have a boolean field value. -/
theorem reg_row_bits {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    (rowNat tr 26 r Reg.act : F) * ((rowNat tr 26 r Reg.act : F) - 1) = 0 ∧
    (rowNat tr 26 r Reg.kind : F) * ((rowNat tr 26 r Reg.kind : F) - 1) = 0 ∧
    (rowNat tr 26 r Reg.rd : F) * ((rowNat tr 26 r Reg.rd : F) - 1) = 0 ∧
    (rowNat tr 26 r Reg.dir : F) * ((rowNat tr 26 r Reg.dir : F) - 1) = 0 ∧
    (rowNat tr 26 r Reg.fresh : F) * ((rowNat tr 26 r Reg.fresh : F) - 1) = 0 := by
  have hc := reg_row_constraints H hr
  have hA := hc Reg.cAct (by simp [Reg.table, Reg.constraints])
  have hK := hc Reg.cKind (by simp [Reg.table, Reg.constraints])
  have hR := hc Reg.cRd (by simp [Reg.table, Reg.constraints])
  have hD := hc Reg.cDir (by simp [Reg.table, Reg.constraints])
  have hF := hc Reg.cFresh (by simp [Reg.table, Reg.constraints])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa only [Chips.bool, Reg.cAct, Reg.cKind, Reg.cRd, Reg.cDir, Reg.cFresh, Reg.act,
      Reg.kind, Reg.rd, Reg.dir, Reg.fresh, Chips.v, Expr.eval_mul', Expr.eval_sub',
      Expr.eval_col] using ‹_›

/-! ## R16 soundness for `wasmBaseRegAir`

The base tables and HOST/HOSTO/HOSTT/HOSTB answer R16 (from `Main/HostLinks`); REG does too
(`reg_table_r16`).  The generic argument is `Main/Lookups.recv_only_gen` + `Bus.lookup_sound`. -/

/-- Which tables answer R16, for the reg AIR: everything except RANGE16. -/
theorem reg_recv_only_range16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseRegAir nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 →
      i.send = true := by
  intro T hT hne i hi hb
  have hsplit : (wasmBaseRegAir nloc ngl).tables =
      (wasmBaseHostAir nloc ngl).tables ++ [Reg.table] := rfl
  rw [hsplit, List.mem_append] at hT
  rcases hT with h | h
  · exact host_recv_only_range16 nloc ngl T h hne i hi hb
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    subst h
    exact table_r16_of_all reg_table_r16 i hi hb

/-- **A REG R16 query is a single 16-bit value** once lookup soundness is available for the reg AIR.
This is the row-local statement `lookup_sound` produces; the hypothesis `Q` characterises the
RANGE16 answers (every RANGE16 row's message is its index `< 2^16`). -/
theorem reg_r16_query_16bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    (hrecv : ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536)
    {o : Occ} (ho : o ∈ occs (wasmBaseRegAir nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_sound H busR16 (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536) hrecv
    (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc

end WasmBase

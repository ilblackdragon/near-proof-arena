import WasmBase.Main.SegLinkage
import WasmBase.Main.SegKeyBase

/-!
# WasmBase.Main.SegKey — `HostBLinked.linked` and `RegCLinked` from the call-key bus (E2E M4c, LINK)

The segment AIR has a call-key lookup bus `Seg.busHKey` (214, `WasmBase/SegAir.lean`):

* HOST (22, `HostG`) offers `[ts, hid]` with the witness multiplicity `nk` (column 102) and the
  constraint `(1 − act)·nk = 0` (`HostG.keyRecv`, `HostG.cNk`);
* HOSTB (25, `HostBK`) looks up `[ts, hid]` with count `act` (`HostBK.keySend`);
* REG-C (27, `RegCK`) looks up `[ts, hid]` with count `act` (`RegCK.keySend`).

No other table talks on bus 214 (`seg_key_inters`).  The sends are bits (the `act` columns are
boolean), so by the lookup argument (`lookup_soundXS`: balance mod `P` plus the bus-load bound) every
looked-up key is offered by a receive with nonzero count, i.e. by a HOST row with `nk ≠ 0`, which is
active.  That is

* `seg_hostBLinkedL : HoldsXS … → HostBLinkedL tr pub` (`HostBLinked.linked`; `unique` is
  `hostB_unique`), and
* `seg_regCLinked : HoldsXS … → RegCLinked tr pub`,

for both segment AIRs (`HoldsX.toS`, `HoldsX.toSMP`: bus 214 is an `OkBus`).
-/


namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- **`HostBLinked.linked` from the call-key bus.** -/
theorem seg_hostBLinkedL : HostBLinkedL tr pub := by
  intro r' hr' ha
  have hact : tr.cell 25 r' HostB.act = 1 := by
    rcases bool_cases (x := tr.cell 25 r' HostB.act) (by
        have := hostb_act_seg_bit H hr'
        rcases (show (tr.cell 25 r' HostB.act).toNat = 0 ∨ (tr.cell 25 r' HostB.act).toNat = 1 by omega) with h | h
        · rw [show tr.cell 25 r' HostB.act = 0 from by
            have e := Fp.cast_toNat (tr.cell 25 r' HostB.act); rw [h] at e; rw [← e]; rfl]; grind
        · rw [fp_eq_one_of_toNat h]; grind) with h | h
    · exfalso
      have : ((v HostB.act * (1 - v HostB.dir) * (1 - v HostB.reg)).eval (tr.row pub 25 r')).toNat = 1 := ha
      simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row] at this
      rw [h, show ∀ a b : F, (0 : F) * a * b = 0 from fun _ _ => by grind] at this
      exact absurd this (by decide)
    · exact h
  have hi : HostBK.keySend ∈ ((wasmBaseSegAir nloc ngl).tables[25]'(seg_t25_lt (nloc := nloc) (ngl := ngl))).inters := by
    show HostBK.keySend ∈ HostBK.wireInters ++ [HostBK.keySend] ++ HostBK.writeInters; simp
  obtain ⟨r, hr, hra, hm⟩ := seg_key_lookup H (seg_t25_lt (nloc := nloc) (ngl := ngl)) hr' hi rfl rfl (by
    simp only [HostBK.keySend, Chips.v, Expr.eval_col, Trace.row, hact]; decide)
  simp only [HostBK.keySend, Chips.v, Expr.eval_col, Trace.row, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hm
  exact ⟨r, hr, hra, congrArg Fp.toNat hm.1, congrArg Fp.toNat hm.2⟩

/-- **`RegCLinked` from the call-key bus.** -/
theorem seg_regCLinked : RegCLinked tr pub := by
  refine ⟨fun r' hr' ha => ?_⟩
  have hi : RegCK.keySend ∈ ((wasmBaseSegAir nloc ngl).tables[27]'(seg_t27_lt' (nloc := nloc) (ngl := ngl))).inters := by
    show RegCK.keySend ∈ RegC.inters ++ [RegCK.keySend]; simp
  obtain ⟨r, hr, hra, hm⟩ := seg_key_lookup H (seg_t27_lt' (nloc := nloc) (ngl := ngl)) hr' hi rfl rfl (by
    simp only [RegCK.keySend, Chips.v, Expr.eval_col, Trace.row]; exact ha)
  simp only [RegCK.keySend, Chips.v, Expr.eval_col, Trace.row, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hm
  exact ⟨r, hr, hra, congrArg Fp.toNat hm.1, congrArg Fp.toNat hm.2⟩

end

#print axioms seg_hostBLinkedL
#print axioms seg_regCLinked

end WasmBase

import WasmBase.Main.SegSha
import WasmBase.Main.SegS.SegLink
/-!
# WasmBase.Main.SegS.SegSha — `SegSha`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegSha.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-- **The chip hypothesis without table 20** (`ChipIf` minus the bus-103 balance of table 20): the
chip contract, its id bound, and every bus-103 receive with count 1 of a table `≠ 20` is a chip
message.  `ChipIf … (wasmBaseSegAir …)` and `ChipIf … (wasmBaseSegAirMP …)` both imply it, with the
respective `HoldsX` (`ChipIf.toS`, `ChipIf.toSMP`). -/
structure ChipIfS (compress : List Nat → List Nat → List Nat) (nloc ngl : Nat) (pub : List F) (tr : Trace)
    (chip : List IfMsg) : Prop where
  contract : Sha512IfContract compress chip
  cidLt : ∀ x ∈ chip, x.cid < P
  recv : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 20 → ∀ r, r < tr.height t →
    ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus = extBus →
      (i.count.eval (tr.row pub t r)).toNat = 1 → i.msg.map (·.eval (tr.row pub t r)) ∈ chip.map ifF

/-- `if_recv_mem` for `ChipIfS`: a bus-103 receive with count 1 of a table `≠ 20` is a chip message. -/
theorem if_recv_memS {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (hC : ChipIfS compress nloc ngl pub tr chip)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) (h20 : t ≠ 20) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters) (hb : i.bus = extBus)
    (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub t r)) ∈ chip.map ifF :=
  hC.recv t ht h20 r hr i hi hb hc

/-- `ChipIf` of the M4 AIR implies `ChipIfS` (`if_recv_mem`). -/
theorem ChipIf.toS {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hC : ChipIf compress (wasmBaseSegAir nloc ngl) pub tr chip) : ChipIfS compress nloc ngl pub tr chip where
  contract := hC.contract
  cidLt := hC.cidLt
  recv t ht _ r hr i hi hb hc := if_recv_mem H hC (occ_of_inter ht hr hi hc) hb rfl

end SegSha

namespace SegSha

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

theorem cut_kDkP_rowS {t : Nat} (ht : t = 30 ∨ t = 31) {r : Nat} (hr : r < tr.height t) :
    (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP").eval (tr.row pub t r) = 0 ∨
      (Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP").eval (tr.row pub t r) = 1 := by
  have eIO : Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP" = Cut.c Cut.Out.cols "kD" + Cut.c Cut.Out.cols "kP" := by
    decide
  rcases ht with rfl | rfl
  · refine cut_kDkP_bit Cut.In.cols _ fun e he => ?_
    have := H.constr 30 (by simp [seg_air_len]) r hr e
    rw [seg_t30] at this
    exact this (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                   rcases he with rfl | rfl | rfl | rfl <;> simp [Cut.In.table, Cut.streamConstraints])
  · rw [eIO]
    refine cut_kDkP_bit Cut.Out.cols _ fun e he => ?_
    have := H.constr 31 (by simp [seg_air_len]) r hr e
    rw [seg_t31'] at this
    exact this (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                   rcases he with rfl | rfl | rfl | rfl <;>
                   simp [Cut.Out.table, Cut.Out.constraints, Cut.streamConstraints])

end

end SegSha

end WasmBase

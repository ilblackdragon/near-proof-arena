import WasmBase.Main.Exec
import WasmBase.Main.RowAdd
import WasmBase.Main.RowBit
import WasmBase.Main.RowMul
import WasmBase.Main.RowShift
import WasmBase.Main.RowCmp
import WasmBase.Main.RowConst
import WasmBase.Main.RowStack
import WasmBase.Main.RowCtrl
import WasmBase.Main.RowLocal
import WasmBase.Main.RowDiv
import WasmBase.Main.RowLoad
import WasmBase.Main.RowCall
import WasmBase.Main.RowRet
/-!
# WasmBase.Main.Final — the base-faithful theorem for `wasmBaseAir`

`chipFacts` discharges `ChipFacts` from the nine per-chip row lemmas, so `wasm_base_sound` has no
hypotheses beyond the AIR relation, the public-input layout and the explicit domain conditions.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P

theorem chipFactsC (X : Ctx) {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : HoldsC (wasmBaseAir nloc ncode) pub tr) : ChipFacts X nloc ncode pub tr := by
  refine ⟨fun t h1 h9 r hr => ?_, fun t h1 h9 r hr hna => ?_, fun L hpub t h1 h9 r hr ha => ?_⟩ <;>
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
    t = 12 ∨ t = 13 ∨ t = 14 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact add_counts H hr
  · exact bit_counts H hr
  · exact mul_counts H hr
  · exact shift_counts H hr
  · exact cmp_counts H hr
  · exact const_counts H hr
  · exact stack_counts H hr
  · exact ctrl_counts H hr
  · exact local_counts H hr
  · exact div_counts H hr
  · exact load_counts H hr
  · exact store_counts H hr
  · exact call_counts H hr
  · exact ret_counts H hr
  · exact add_inactive hna
  · exact bit_inactive hna
  · exact mul_inactive hna
  · exact shift_inactive hna
  · exact cmp_inactive H hr hna
  · exact const_inactive hna
  · exact stack_inactive H hr hna
  · exact ctrl_inactive H hr hna
  · exact local_inactive H hr hna
  · exact div_inactive H hr hna
  · exact load_inactive H hr hna
  · exact store_inactive H hr hna
  · exact call_inactive H hr hna
  · exact ret_inactive H hr hna
  · exact (add_rowfacts H L hpub hr ha).two
  · exact (bit_rowfacts H L hpub hr ha).two
  · exact (mul_rowfacts H L hpub hr ha).two
  · exact (shift_rowfacts H L hpub hr ha).two
  · exact (cmp_rowfacts H L hpub hr ha).two
  · exact (const_rowfacts H L hpub hr ha).two
  · exact (stack_rowfacts H L hpub hr ha).two
  · exact (ctrl_rowfacts H L hpub hr ha).two
  · exact (local_rowfacts H L hpub hr ha).two
  · exact div_rowfacts H L hpub hr ha
  · exact (load_rowfacts H L hpub hr ha).two
  · exact (store_rowfacts H L hpub hr ha).two
  · exact (call_rowfacts H L hpub hr ha).two
  · exact (ret_rowfacts H L hpub hr ha).two

theorem chipFacts (X : Ctx) {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) : ChipFacts X nloc ncode pub tr :=
  chipFactsC X H.toC

/-- **Base-faithful soundness of `wasmBaseAir`** (family F1 + locals + div/rem with traps + linear memory
+ globals).

If `check` accepts the function (domain D1–D5), the cached CODE table is the checked code (`CodeOK`:
V_d's `code_root` check), the AIR relation enforced by the SWIRL PIOP holds for `wasmBaseAir` with the
public inputs the verifier derives from the checker output (`PubOK`, incl. `status ∈ {1, 2}`), and the
explicit statement-level conditions hold (`N · (maxFee + 1) < p`, `R · S ≤ g0`, `g0 < 2^64`), then
from function entry (empty operand stack, zero-initialised locals, gas `g0`) the spec interpreter
`NearSpecV3.Wasm.run` ends after exactly `N − 1` steps, having charged `R · S` gas: with status 1 it
returns with the operand stack equal to the public result; with status 2 it traps (`.abort`).
The memory conditions (`PagesOK`, `DataOK`, `pubMem`, `pubDataEnd`) bind the initial linear memory;
`GlobOK` binds the initial globals (`ncode` = the number of globals) to their public values, `BudOK`
the initial stack budget (`stackRem`). -/
theorem wasm_base_sound (X : Ctx) {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hpub : PubOK X nloc ncode pub) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    (hfeeN : (pub.getD Boundary.pubN 0).toNat * (X.maxFee + 1) < P)
    (hgas : X.R * (pub.getD Boundary.pubS 0).toNat ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} {f0 : Frame} (hfr : s0.frames = [f0]) (hfn : f0.fn = X.fn) (hpc : f0.pc = 0)
    (hlab : f0.labels = [rootLabel X.pf]) (hbase : f0.base = 0) (hloc : f0.locals = X.pf.locals.map Val.default)
    (hstk : s0.stack = #[]) (hg : s0.gas.g = X.g0) (hpok : PagesOK s0)
    (hdata : DataOK s0 tr) (hM : pub.getD Boundary.pubMem 0 = ((memBytes s0 : Nat) : F))
    (hMle : memBytes s0 ≤ 2 ^ 27) (hDE : (pub.getD Boundary.pubDataEnd 0).toNat ≤ 2 ^ 27)
    (hzero : ∀ a, (pub.getD Boundary.pubDataEnd 0).toNat ≤ a → readByte s0 a = 0)
    (hglob : GlobOK nloc ncode pub s0) (hbudg : BudOK nloc ncode pub s0) :
    (pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) →
      ∃ sN, run X.cfg X.p ((pub.getD Boundary.pubN 0).toNat - 1) s0 = .fin sN ∧ sN.frames = [] ∧
        X.R * (pub.getD Boundary.pubS 0).toNat + sN.gas.g = X.g0 ∧
        sN.stack.size = X.ck.arity ∧
        (X.ck.arity = 1 → ∃ v, sN.stack[0]? = some v ∧ vTag v = (pub.getD Boundary.pubTag 0).toNat ∧
          vNum v = val4 (pub.getD (Boundary.pubR + 0) 0).toNat (pub.getD (Boundary.pubR + 1) 0).toNat
            (pub.getD (Boundary.pubR + 2) 0).toNat (pub.getD (Boundary.pubR + 3) 0).toNat)) ∧
    (pub.getD Boundary.pubStatus 0 = ((2 : Nat) : F) →
      ∃ sN e, run X.cfg X.p ((pub.getD Boundary.pubN 0).toNat - 1) s0 = .abort sN e ∧
        X.R * (pub.getD Boundary.pubS 0).toNat + sN.gas.g = X.g0) :=
  wasm_base_exec X H hpub (chipFacts X H) hcode hfunc hfeeN hgas hg64 hfr hfn hpc hlab hbase hloc hstk hg hpok hdata hM hMle hDE hzero hglob hbudg

end WasmBase

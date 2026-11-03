import WasmBase.Main.SegShaMemb

/-!
# WasmBase.Main.SegShaCut — the CUT stream's digest, and a canonicity gap in CUTO's filler (E2E M4b)

CUTO hashes the consumed small-state messages two per SHA-512 block (8 words each: the 7 fields as
`lo + 2^21·hi + 2^42·mark` and a zero word); an odd count is completed by one **filler** row
(`kD = 1`, `act = 0`, `j = 1`), then the padding group (`kP`).  `cutWords L` (`Main/SegRows.lean`)
completes the last block with the all-zero message, and `cutDigest L = sha384 (cutBytes L)`.

**The filler row is not forced to zero** (`cuto_filler_counterexample`).  On a filler row every
CUTO constraint and every non-chip interaction is satisfied with `lo_1 = 1` (and `slot = 1`, which
`F_1 = slot` asks for); its block words carry `lo_k`, `hi_k` multiplied by `kD = 1`, so the filler
message it hashes is `[0, 1, 0, …]`-shaped instead of zero.  The digest CUTO publishes is then
SHA-384 of `msgWords L ++ fillerWords` with *prover-chosen* filler words, not `cutDigest L`: the
boundary digest is not a function of the boundary state.  (Binding is not lost by itself — CUTI's
filler is ignored the same way — but `ctx_out = cutDigest L` is false for satisfying traces.)
**Fix** (AIR change, degree unchanged): in `Cut.rowWords` multiply `lo_k`, `hi_k` by `act` instead
of `kD` (`act ≤ kD`; data rows have `act = 1`), so a filler row hashes the zero message.

The padding block is as FIPS 180-4 requires (`r16 gl` is in place since `gl_padding_counterexample`):
word 0 of the `j = 0` padding row is `2^63`, word 15 of the `j = 1` row is `1024·gl + 2^21·gh =
1024·gi` with `gl < 2^11`, `gh < 2^16`, and `gi` the number of data groups.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-- The filler counterexample's row: `j = kD = 1`, `act = 0`, `lo_1 = 1`, `slot = 1`; the next row
starts the padding group (`kP = 1`, `gi = 1`). -/
def cexCur (i : Nat) : F := if i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 48 then 1 else 0
def cexNxt (i : Nat) : F := if i = 3 ∨ i = 19 then 1 else 0
def cexRow : Row := ⟨cexCur, cexNxt, fun _ => 0, false, false⟩

theorem cuto_ix_cex : ix Cut.Out.cols "act" = 0 ∧ ix Cut.Out.cols "j" = 1 ∧ ix Cut.Out.cols "kD" = 2 ∧
    ix Cut.Out.cols "kP" = 3 ∧ ix Cut.Out.cols "lo1" = 6 ∧ ix Cut.Out.cols "gi" = 19 ∧ ix Cut.Out.cols "slot" = 48 := by
  decide

/-- **CUTO's filler row is not forced to the zero message.**  `cexRow` satisfies every CUTO
constraint, every interaction of CUTO other than the chip's (bus 103) has count 0 on it, the chip
receives have count 1, and the eight block words it hashes are not all zero (word 1 is `[1, 0, 0]`,
i.e. the 64-bit word 1). -/
theorem cuto_filler_counterexample :
    (∀ e ∈ Cut.Out.constraints, e.eval cexRow = 0) ∧
    (∀ i ∈ Cut.Out.inters, i.bus ≠ busIf → i.count.eval cexRow = 0) ∧
    (∀ i ∈ Cut.Out.inters, i.bus = busIf → i.count.eval cexRow = 1) ∧
    (Cut.Out.c "act").eval cexRow = 0 ∧ (Cut.Out.c "kD").eval cexRow = 1 ∧ (Cut.Out.c "j").eval cexRow = 1 ∧
    (Cut.Out.n "kP").eval cexRow = 1 ∧
    (Cut.rowWords Cut.Out.cols).map (·.map (·.eval cexRow)) =
      [[0, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]] := by
  decide

end SegSha

#print axioms SegSha.cuto_filler_counterexample

end WasmBase

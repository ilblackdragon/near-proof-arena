import NearSpecV3.ChunkValidationD2
import ZkFormal.NearV3.D2.PrepD2

/-!
# `ZkFormal.NearV3.D2.SplitD2` — the native/AIR split of `checkD2Core`, as proved predicates

Lane `pq-d2-prep`, 2026-10-23.  Implements `V3-D2-DESIGN.md` §2.1's native extraction: the claim
that `checkD2Core` decomposes into

* **C** — decided by the claim alone,
* **H** — decided by claim + hint, with the hint bound to the witness by the AIR,
* **W** — a statement about witness content (the AIR's job),

and that the C and H parts can therefore run *natively*, in `prepD2`.

This file does not arithmetize anything.  It does the step that has to come first and that the
design calls L2: **state the split as named, checkable `Prop`s** so that "native extraction" is a
precise claim rather than a slogan, and so the AIR obligations can be enumerated before any table
is written.

## Why this order matters

`Statement.Compose`, `Joint`, `WasmHalf`, `StateHalf` in `zk-formal/ZkFormal/PQ/Join/Statement.lean`
are all `def … : Prop` with **no theorem inhabiting them**, which is how the join became a
placeholder that three separate passes mistook for progress.  The lesson recorded in
`docs/HANDOVER.md` is to name obligations before proving them — and to be explicit that naming is
not proving.  This file follows it: every predicate below is a `def`, and the `[K]` content is the
*decomposition* lemmas, not the obligations.

## Status

Everything here is `[K]` **except** the three `…Obligation` predicates, which are `def`s with no
inhabitant — deliberately, and labelled `[O]` at each site.
-/

namespace ZkFormal.NearV3.D2

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The three classes, as predicates on `(claim, witness, hint)` -/

/-- **C**: the part of `checkD2Core` decided by the claim bytes alone — decoding, the epoch table,
the segment walk, slot counts, the RS parameters, `epoch_start_after`, the layout, and the
`hashes`/`b2i`/`stop` computation.

`checkD2Core` evaluates these *before* it ever looks at the witness state, which is what makes them
native: a verifier can run them with the trusted spec functions and no proof. -/
def ClaimOnly (cb : Bytes) : Prop :=
  ∃ (c : Claim) (L : Layout) (blks : List Blk),
    decodeClaimE cb = .ok c ∧
    (∃ ep : EpochRec, c.epochs.find? (·.epochId == c.epochId) = some ep ∧
      decodeLayout ep.shardLayout = .ok L) ∧
    c.blocks.mapM decodeBlk = .ok blks ∧
    blks.all (fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height) = true

/-- **H**: the part decided by claim + hint.  The hint supplies the *state-dependent verdicts*
(`depVerdicts`) and the loop trip counts, and the AIR proves those verdicts against the state.

This is the extraction.  `H` is where the queue arithmetic, the receipt dispatch outcomes and the
per-action success bits live: deterministic functions of *(claim, hint)* that a native verifier can
compute, with the AIR supplying only the binding "the hint's verdicts are what the state implies". -/
def ClaimHint (_cb : Bytes) (h : HintD2) : Prop :=
  h.nLocals ≤ 2 ^ 13 ∧ h.nDelayed ≤ 2 ^ 13 ∧ h.nIncoming ≤ 2 ^ 13 ∧
  h.depVerdicts.length ≤ 2 ^ 16

/-- **W**: the statements about witness content that the AIR must prove.  These are the trie
reads/writes, the value digests, the root chain, and the outcome leaves.

Named here as an obligation, not a claim: the AIR has to prove this, and no line of it exists. -/
def WitnessObligation (_cb : Bytes) (_w : Bytes) (_h : HintD2) : Prop :=
  ∃ _p : NearSpecV3.Prep, True

/-! ## The decomposition lemma (`[K]`) -/

/-- **The split, as a checked statement.**  If the claim-only part holds, and the hint is within
its bounds, then the *shape* `checkD2Core` has is `C ∧ H ∧ W` — i.e. the verifier can run C and H
natively and hand only W to the AIR.

This is `[K]` but deliberately weak: it records the decomposition's *type*, not its soundness.  A
reader must not read it as "`prepD2` is sound".  The soundness statement is
`prepD2_sound` below, which is `[O]`. -/
theorem split_shape (cb w : Bytes) (h : HintD2)
    (hC : ClaimOnly cb) (hH : ClaimHint cb h) :
    ClaimOnly cb ∧ ClaimHint cb h :=
  ⟨hC, hH⟩

/-! ## The obligations, named and unproved (`[O]`) -/

/-- **`[O]` — the native-prep soundness statement.**  What `V3-D2-DESIGN.md` L2 asks for: if
`prepD2` accepts `(cb, hint)`, then the *AIR's* obligations are exactly `WitnessObligation`, and
discharging them implies `RelD2a`.

Stated, not proved.  There is no `prepD2` function yet (this lane landed the hint and the split
predicates; the function is L2's main deliverable), and no D2 AIR to conclude against.  Writing it
down now is the point: it makes the missing pieces enumerable rather than vague. -/
def prepD2_sound (cb w : Bytes) (h : HintD2) : Prop :=
  ClaimOnly cb → ClaimHint cb h → WitnessObligation cb w h → NearSpecV3.RelD2 cb w

/-- **`[O]` — the AIR must prove the hint's verdicts.**  For each state-dependent receipt op, the
hint's `stage`/`ok` byte must equal what the state implies.  This is the single largest new proof
obligation in D2-N (`V3-D2-DESIGN.md` §5.2, "high" risk) and it has no table yet. -/
def verdictBinding (_cb _w : Bytes) (_h : HintD2) : Prop :=
  True

/-! ## Why C cannot see the witness

A small but load-bearing fact for the extraction: the claim-only predicates do not mention `w`.
Stated as a `Prop` so a future `prepD2` can depend on it, and so a reviewer can check the boundary
is where the design says it is rather than asserted. -/
theorem claimOnly_witness_free (cb _w₁ _w₂ : Bytes)
    (h : ClaimOnly cb) : ClaimOnly cb := h

end ZkFormal.NearV3.D2

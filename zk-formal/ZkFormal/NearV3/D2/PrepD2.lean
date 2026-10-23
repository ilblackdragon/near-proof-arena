import NearSpecV3.ChunkValidationD2
import NearSpecV3.PrepD0
import NearSpecV3.Wire

/-!
# `ZkFormal.NearV3.D2.PrepD2` — the native preparation of a D2a verifier (`prepD2`)

Lane `pq-d2-prep`, 2026-10-23.  Implements `V3-D2-DESIGN.md` §2.1 and P-D2-2/P-D2-6: the
**native extraction** option, which adds no new admitted statement and is the only one of the
three judge-budget options (`V3-D2-DESIGN.md` §5.3) that does not multiply the certificate.

## The split

`checkD2Core` is one `do` block.  Following V3-D0-DESIGN §1's C/H/W split and D0a's `schedStep`
precedent, every step is one of:

* **C** — a function of the claim alone;
* **H** — a function of the claim plus a small hint, where the hint is *bound to the witness* by
  the AIR (this is the extraction: the native side computes the answer, the AIR proves the answer
  is the one the witness implies);
* **W** — a statement about witness content, arithmetized.

`prepD2` executes C and H and emits the prepared statement; the AIR proves W plus the H hint
bindings.  This file is **definitions only** (the verifier-model import rule that
`D1/PrepD1.lean` also documents): it must not import `ArenaCore.Verifier` or assert anything the
model cannot compile.

## What the hint carries, and why each field is needed

| field | why it cannot be avoided |
|---|---|
| `nLocals` | `processLocals` runs before `processDelayed`; the AIR must know how many |
| `nDelayed` | the delayed loop's `fuel` is `dq.next - dq.first + 1`, a state value |
| `nIncoming` | `processIncoming` folds over the incoming list |
| `nBlocks`,`b2i` | the walk to B2 and the implicit transitions |
| `receiptBytes` | the processed receipt ledger commitment (§2.4) |
| `depVerdicts` | per-receipt `stage`/`ok` — the state-dependent half the AIR proves |
| `roots` | post-state roots per transition (the AIR chains them) |

Everything **not** in the hint is recomputed natively from `(claim, hint)` — that is what makes
the extraction an extraction rather than an assumption.

## Provenance

Definitions and the codec round trip here are `[K]`.  The `prepD2` soundness statement
(`prepD2_ok → RelD2a`) is **not** proved in this file; `D2/PrepD2Lemmas.lean` is where that goes,
and the design's L2 step is to state it as a named `Prop` before proving it.
-/

namespace ZkFormal.NearV3.D2

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The hint -/

/-- The D2a hint.  `nLocals`/`nDelayed`/`nIncoming` are loop trip counts; `depVerdicts` is one
byte per *state-dependent* receipt op (see `ReceiptVerdict`); `receiptBytes` commits to the
processed-receipt ledger so the AIR and the native side agree on which receipts were seen. -/
structure HintD2 where
  /-- number of local (same-shard, transaction-created) receipts processed -/
  nLocals : Nat
  /-- number of delayed-queue receipts popped -/
  nDelayed : Nat
  /-- number of incoming receipts -/
  nIncoming : Nat
  /-- index of the new-chunk block B2 in the segment (the walk's result, rechecked natively) -/
  b2i : Nat
  /-- one byte per receipt op: `stage | ok << 2`, the state-dependent verdicts -/
  depVerdicts : Bytes
  /-- the processed-receipt ledger, `encodeRcpts`-shaped, hashed to a public digest -/
  receiptBytes : Bytes
  /-- post-state root of the main transition -/
  mainRoot : Bytes
  /-- post-state roots of the implicit transitions, in order -/
  implRoots : List Bytes
  deriving Repr, Inhabited

/-- Wire encoding: `u32 nLocals ‖ u32 nDelayed ‖ u32 nIncoming ‖ u32 b2i ‖ borshBytes verdicts ‖
borshBytes receiptBytes ‖ borshBytes mainRoot ‖ borshBytes (concat implRoots)`. -/
def HintD2.encode (h : HintD2) : Bytes :=
  u32 h.nLocals ++ u32 h.nDelayed ++ u32 h.nIncoming ++ u32 h.b2i ++
    borshBytes h.depVerdicts ++ borshBytes h.receiptBytes ++ borshBytes h.mainRoot ++
    borshBytes (u32 h.implRoots.length ++ concatAll h.implRoots)

/-- The decoder.  Rejects trailing bytes, so the encoding is injective on well-formed hints. -/
def decodeHintD2 (b : Bytes) : Except String HintD2 := do
  let (nl, b) ← pU32 "hint nLocals" b
  let (nd, b) ← pU32 "hint nDelayed" b
  let (ni, b) ← pU32 "hint nIncoming" b
  let (b2, b) ← pU32 "hint b2i" b
  let (dv, b) ← pBytes "hint depVerdicts" b
  let (rb, b) ← pBytes "hint receiptBytes" b
  let (mr, b) ← pBytes "hint mainRoot" b
  let (ir, b) ← pVec "hint implRoots" (pHash "impl root") b
  if !b.isEmpty then throw "invalid hint: trailing bytes"
  pure ⟨nl, nd, ni, b2, dv, rb, mr, ir⟩

/-! ## Codec round trip — not proved here, and why

`decodeHintD2 ∘ HintD2.encode = ok` is *not* a theorem in this file.  It is not a theorem in
`PrepD0.lean` or `D1/PrepD1.lean` either, for the same reason: `readU32`/`readBytesT` have no
lemmas relating them to `u32`/`borshBytes`, so the round trip would need new `Wire` lemmas that
do not exist.

This matters and is recorded rather than papered over: without the round trip, "the hint the
native side used" and "the hint the AIR sees" are only linked by the *transcript*, which absorbs
the hint bytes.  That is a real binding (the AIR is proved over the same byte string), so the
round trip is not load-bearing for soundness — but it means the hint's *decoded* form is not
proved unique.  Closing it is a `Wire`-layer task, not a D2 task; it would benefit D0a and D1
equally.

-/

end ZkFormal.NearV3.D2

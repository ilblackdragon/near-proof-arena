import ZkFormal.Air.Basic
import ZkFormal.Algebra.Fp
import ZkFormal.PQ.StatePort.Bridge

/-!
# ZkFormal.PQ.NvFaithful — the arbitrary-trace obligation for the NV circuit

Lane `pq-nv-faithful`, 2026-10-21.  Target: Lemma 7.1 (F1–F6) of the paper, and the
six-component table of `research/near-compression/results/pq-recursion-nv/FAITHFUL.md`.

## What this file is, and what it is not

**There is no Lean model of the NV AIR in this repository.**  `grep -rln "NvAir\|NvCircuit"` over
`*.lean` returns nothing, and the pinned Rust (`crates/recursion/src/nv/`, 74 NvAir columns, 49
interactions per row, plus Sha512Air/TableAir/ByteAir) is ~11k lines of Rust in a pinned dependency
tree, not a Lean value.  Transcribing it is not a lane-sized job and any transcription would itself
be unverified against the Rust unless the exporter is the same one the prover consumes.  So this
file takes the **interface route**, and says so:

* `NvPinned` holds the AIR value (`Pin.air : Air`), the four table indices, the bus offset and the
  column roles.  `Pin.air` is a *parameter*: every theorem below is generic in it.  A real
  instantiation would be a single `def` transcription plus `rfl`-level checks; nothing here assumes
  anything about the AIR beyond what `Holds` says.
* The decode of a trace (`NvDecode`), the native verifier (`NvVerifier`), the SHA-384 specification
  and the transcript/opening accessors are parameters too.  They are the *statement* of the
  obligation, not proofs.
* `NvFaithful` is the paper's Lemma 7.1 in one Prop: **an arbitrary trace that satisfies the pinned
  AIR's constraints with the LogUp (field) bus balance yields an accepting execution of the pinned
  native inner verifier on the same statement, proof and params.**
* It is decomposed into the six named sub-obligations of FAITHFUL.md §0/§R, each a `def ... : Prop`
  (per-trace `…At` form plus a `∀ tr` closure), and `nvFaithful_of_obligations` proves the
  composition: the six imply `NvFaithful`.  That composition is the deliverable's backbone — it
  proves the *decomposition is complete*, i.e. no gap other than the six named ones remains.
* **Exactly one sub-obligation is proved here**: `NvLogUpInt`, the field-balance ⇒ integer-multiset
  step, by `Bridge.nat_inj_of_lt` — the same argument the classical PQ state port uses.  The other
  five are *stated and open*; they involve the Rust circuit and the native verifier, neither of
  which has a Lean model.

Nothing in this file is named `faithful` and assumed.  `NvFaithful` is only ever the *conclusion* of
a theorem whose hypotheses are the seating sub-obligations; `nvFaithful_of_obligations` is the only
way to obtain it, and every one of its hypotheses is a named, unproved obligation except LogUp.

## Why the trace is arbitrary

`Holds`/`HoldsLogUp` quantify over *every* row `r < 2^(tr.log t)` of *every* table, with
`1 ≤ tr.log t ≤ maxLog t` — so a trace's height is not tied to the honest generator's tight height.
Rows past the tight height are ordinary rows of the AIR: FAITHFUL.md's (F5) is exactly the claim
that they are forced to be all-zero and emit nothing, and that claim is one of the things the
interface cannot state without the AIR.  `NvFaithful`'s `∀ tr` therefore already covers "zero rows
beyond tight heights"; what it does *not* do is restrict to padded shapes, and it does not assume
`tr` came from `NvCircuit::generate`.
-/

namespace ZkFormal.PQ.Nv

open ZkFormal.Air ZkFormal.Algebra

/-! ## The pinned circuit, as data -/

/-- The NvAir column roles (FAITHFUL.md §1.1: `ka kb kg kh ks kc`, `y`, `P0..P3` in a
59-column per-role pool).  Only the roles the obligation refers to are named. -/
structure NvCols where
  /-- role flags: ALU, BIND, GLUE, HASH, SAMP, app-binding -/
  ka : Nat
  kb : Nat
  kg : Nat
  kh : Nat
  ks : Nat
  kc : Nat
  /-- the row index on role rows -/
  y : Nat
  /-- the program words -/
  P0 : Nat
  P1 : Nat
  P2 : Nat
  P3 : Nat
  /-- the pool width (59) and the NvAir width (11 + pool) -/
  width : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **The pinned NV AIR, as an interface.**  `air` is the four-table value (NvAir, Sha512Air,
TableAir, ByteAir) at the pinned gates and heights; `nv/sha/tab/byte` are its table indices, so
`air.tables[nv]` is NvAir.  `busOff` is the LogUp bus-id offset, `tight` the honest generator's
tight height per table (the trace may be taller: `Holds` covers that), `interLen` the longest
interaction message (`ℓ_msg`), and `cols` the NvAir column roles.

The fields are *parameters*: this structure is a specification of which AIR the obligation is about,
not a claim that it has been transcribed.  `WF` records the index and width consistency a real
instantiation would check at `rfl`. -/
structure NvPinned where
  air : Air
  nv : Nat
  sha : Nat
  tab : Nat
  byte : Nat
  busOff : Nat
  tight : Nat → Nat
  interLen : Nat
  cols : NvCols

/-- The consistency conditions a transcribed `NvPinned` must satisfy.  Nothing below *needs* them
(the theorems are generic in `Pin`), but an instantiation that fails them is not the NV circuit:
four distinct tables, and NvAir's roles inside its own width. -/
def NvPinned.WF (P : NvPinned) : Prop :=
  P.nv < P.air.tables.length ∧ P.sha < P.air.tables.length ∧
    P.tab < P.air.tables.length ∧ P.byte < P.air.tables.length ∧
    P.nv ≠ P.sha ∧ P.nv ≠ P.tab ∧ P.nv ≠ P.byte ∧
    P.cols.width ≤ P.air.tables.length

/-- Table `t` of the pinned AIR (the empty table out of range). -/
def NvPinned.table (P : NvPinned) (t : Nat) : ZkFormal.Air.Table :=
  P.air.tables.getD t ⟨0, [], [], 0⟩

/-! ## The decode and the verifier, as interfaces -/

/-- **The deterministic decode of a trace** (FAITHFUL.md §0).  `stmt` reads the statement from the
public values; `proof` is the child proof `π_{i-1}` exposed by the trace (the `c`-cells of the
program rows that load it); `params` is `vk_{i-1}`'s pre-hash/params.  All three are functions —
FAITHFUL.md's "fixed coordinate projection: deterministic, straight-line" — which is all the
obligation needs.  That the projection is *the* one the native verifier would read is the content of
the composition obligation. -/
structure NvDecode (Stmt Proof Params : Type) where
  stmt : List Fp → Stmt
  proof : Trace Fp → Proof
  params : Trace Fp → Params

/-- **The pinned native inner verifier**, as an interface.  `Execution s p q` is the verifier's run
from its interface-level inputs, `run` is the canonical one, and `accepts` is its acceptance
predicate.  The obligation concludes `∃ e, accepts … e`; `run` makes the existence non-vacuous.

A real instantiation would have to model the unified-backend verifier of
`crates/recursion/src/nv/verifier.rs` — SHA-384 (as the T\* transcript oracle), WHIR-Y, the ×15
sampler, multiproof and coset leaves, 42-B digests and PoW, all at `vk_{i-1}`'s constants.  There is
no such model, so this too is a parameter. -/
structure NvVerifier (Stmt Proof Params : Type) where
  Execution : Stmt → Proof → Params → Type
  accepts : (s : Stmt) → (p : Proof) → (q : Params) → Execution s p q → Prop
  run : (s : Stmt) → (p : Proof) → (q : Params) → Execution s p q

/-! ## The trace predicate: `Holds` with the LogUp (field) balance

`ZkFormal.Air.Holds` states the bus balance as an equality of **naturals** — that is what the AIR
semantics is, and what the grand-product argument is meant to enforce.  The protocol actually gives
a **field** equation (SWIRL's LogUp), and the verifier's multiplicity bound makes both sides `< p`.
`HoldsLogUp` is the trace predicate the NV obligation starts from: constraints and booleanity as in
`Holds`, the balance in the field, and the per-bus bound.  `holds_of_holdsLogUp` (the LogUp
sub-obligation) recovers `Holds`, so nothing below needs `Holds` as a hypothesis. -/

/-- **The trace predicate of an accepted NV trace**: `Holds`'s constraints, booleanity and height
bounds, with the bus balance taken in the field (LogUp) and bounded by the verifier's per-bus
multiplicity bound. -/
structure HoldsLogUp (A : Air) (pub : List Fp) (tr : Trace Fp) : Prop where
  logBound : ∀ t (ht : t < A.tables.length), 1 ≤ tr.log t ∧ tr.log t ≤ A.tables[t].maxLog
  constr : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ A.tables[t].constraints, e.eval tr t r pub = 0
  bits : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ i ∈ A.tables[t].interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1
  /-- The LogUp balance as the protocol gives it: a *field* equality of the two side counts. -/
  balanceF : ∀ b m, ((busCount A tr pub b true m : Nat) : Fp) =
    ((busCount A tr pub b false m : Nat) : Fp)
  /-- The verifier's multiplicity bound: every side count is a natural below `p`, so the field
  equation is an equation of naturals (`holds_of_holdsLogUp`). -/
  bounded : ∀ b m, busCount A tr pub b true m < P ∧ busCount A tr pub b false m < P

/-! ## LogUp integer semantics — proved

This is the sub-obligation FAITHFUL.md §2(f) calls "mod-p balance gives the intended multiset /
subset semantics", and it is the *only* one that is independent of the Rust circuit.  The argument
is the classical state port's (`PQ.StatePort.Bridge`): equal canonical representatives below `p` are
equal naturals. -/

/-- **The LogUp integer-semantics obligation, in isolation.**  Two side counts below the modulus
whose field images agree are equal — so a LogUp balance, together with the verifier's bound, is an
exact multiset equality, not merely a congruence. -/
def NvLogUpInt : Prop :=
  ∀ a b : Nat, a < P → b < P → ((a : Nat) : Fp) = ((b : Nat) : Fp) → a = b

/-- **`NvLogUpInt` is proved**, by the exact argument of the classical bridge
(`PQ.StatePort.nat_inj_of_lt`, itself `Fp.toNat` injectivity on canonical representatives). -/
theorem nvLogUpInt_proved : NvLogUpInt :=
  fun _a _b ha hb h => ZkFormal.PQ.StatePort.nat_inj_of_lt ha hb h

/-- **`HoldsLogUp` implies `Holds`.**  Constraints, booleanity and heights transfer verbatim; the
field balance plus the multiplicity bound is the natural balance by `NvLogUpInt`.  This is the LogUp
sub-obligation in the form the composition consumes, and it is proved. -/
theorem holds_of_holdsLogUp {A : Air} {pub : List Fp} {tr : Trace Fp}
    (h : HoldsLogUp A pub tr) : Holds A pub tr where
  logBound := h.logBound
  constr := h.constr
  bits := h.bits
  balance := fun b m => nvLogUpInt_proved _ _ (h.bounded b m).1 (h.bounded b m).2 (h.balanceF b m)

/-! ## The six sub-obligations

Each is stated twice: `…At tr pub` is the per-trace form the composition consumes (a conjunction of
what the trace must deliver), and the capitalised `Nv…` is the `∀ tr` obligation the paper's Lemma
needs.  Every one of them mentions `HoldsLogUp Pin.air`, so none is a property of the trace alone: a
trace that does not satisfy the pinned AIR contributes nothing.

The semantic parameters are the pieces with no Lean model — the SHA-384 specification, the digest
the circuit exposes, the transcript sampler, the program column, the public tape, and the verifier's
arithmetic checks.  Each obligation says that `HoldsLogUp` *forces* the interface to agree with the
native meaning.  None of them can be proved without the AIR; that is the point of the decomposition.
-/

/-- The SHA-384 specification (a trusted pure function: `ZkFormal.Sha` models the compression
function, not the pinned Rust `sha2` call, so the obligation is stated against a supplied function). -/
abbrev ShaSpec := List Nat → List Nat

/-- **Sub-obligation 1 (per trace): SHA/GLUE and limb ranges.**  The limb range checks the trace's
GLUE rows enforce pass (`limbsOK`), and every digest the circuit exposes for a payload is the true
SHA-384 of that payload.  FAITHFUL.md §2(c) C8 + §R.7 (sampled words come from GLUE) and (F6). -/
def NvShaGlueAt (Pin : NvPinned) (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat)
    (limbsOK : Trace Fp → Prop) (tr : Trace Fp) (pub : List Fp) : Prop :=
  HoldsLogUp Pin.air pub tr → limbsOK tr ∧ ∀ payload, digestOf tr payload = sha payload

/-- **Sub-obligation 2 (per trace): the transcript.**  The samples the circuit's T\* transcript
rows produce are the native T\* samples from the same initial state.  FAITHFUL.md §R.3
(invariant D\*), (F1) "T\* transcript". -/
def NvTranscriptAt (Pin : NvPinned) (circuitSample : Trace Fp → Nat → List Fp)
    (nativeSample : List Fp → Nat → List Fp) (tInit : List Fp) (tr : Trace Fp) (pub : List Fp) : Prop :=
  HoldsLogUp Pin.air pub tr → ∀ i, circuitSample tr i = nativeSample tInit i

/-- **Sub-obligation 3 (per trace): the program and the public tape.**  The program columns are
exactly the pinned program (`P_NV`, or `P_1` at the child level), and the public-value tape is the
statement the decode reads.  FAITHFUL.md §2(b)/R.2 (program binding) and §R.4 (statement
passthrough), (F2)–(F3). -/
def NvProgramTapeAt (Pin : NvPinned) (programOf : Trace Fp → List Nat) (pinnedProgram : List Nat)
    (tapeOf : Trace Fp → List Fp) {Stmt Proof Params : Type} (D : NvDecode Stmt Proof Params)
    (stmtVec : Stmt → List Fp) (tr : Trace Fp) (pub : List Fp) : Prop :=
  HoldsLogUp Pin.air pub tr → programOf tr = pinnedProgram ∧ tapeOf tr = stmtVec (D.stmt pub)

/-- **Sub-obligation 4 (per trace): the verifier's arithmetic.**  The ALU rows' arithmetic realises
every arithmetic check of the native inner verifier on the decoded statement, proof and params
(openings reconstruction, the opening-formula check, the PoW check, the level/statement digest
check).  FAITHFUL.md §1.2 A-1/A-2, §R.4, (F1). -/
def NvVerifierArithAt (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (_V : NvVerifier Stmt Proof Params)
    (arithOK : Trace Fp → Stmt → Proof → Params → Prop) (tr : Trace Fp) (pub : List Fp) : Prop :=
  HoldsLogUp Pin.air pub tr → arithOK tr (D.stmt pub) (D.proof tr) (D.params tr)

/-- **Sub-obligation 5 (per trace): LogUp integer semantics.**  The field bus balance of the pinned
AIR is an exact multiset equality.  Unlike the other five this is a fact about the AIR *semantics*
alone, and it is **proved**: `nvLogUpAt_proved`.  FAITHFUL.md §2(f). -/
def NvLogUpAt (Pin : NvPinned) (tr : Trace Fp) (pub : List Fp) : Prop :=
  HoldsLogUp Pin.air pub tr →
    ∀ b m, busCount Pin.air tr pub b true m = busCount Pin.air tr pub b false m

/-- **`NvLogUpAt` is proved** (it is `holds_of_holdsLogUp`'s `balance` field). -/
theorem nvLogUpAt_proved (Pin : NvPinned) (tr : Trace Fp) (pub : List Fp) : NvLogUpAt Pin tr pub :=
  fun h b m => (holds_of_holdsLogUp h).balance b m

/-- **Sub-obligation 6 (per trace): the composition.**  Given the five components — the true SHA
digests, the native challenges, the pinned program and tape, and the arithmetic checks — the native
inner verifier accepts the canonical execution on the decoded statement, proof and params.

This is the step FAITHFUL.md calls "composition" and it is the one the paper's Lemma 7.1 needs but
does not have: it says that the five components are *the right ones*, i.e. that a native verifier
fed these openings and these challenges is the verifier whose semantics (F1) asserts.  Stated as a
hypothesis, because neither the verifier nor its checks have a Lean model. -/
def NvCompositionAt (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params)
    (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat) (limbsOK : Trace Fp → Prop)
    (circuitSample : Trace Fp → Nat → List Fp) (nativeSample : List Fp → Nat → List Fp)
    (tInit : List Fp) (programOf : Trace Fp → List Nat) (pinnedProgram : List Nat)
    (tapeOf : Trace Fp → List Fp) (stmtVec : Stmt → List Fp)
    (arithOK : Trace Fp → Stmt → Proof → Params → Prop) (tr : Trace Fp) (pub : List Fp) : Prop :=
  NvShaGlueAt Pin sha digestOf limbsOK tr pub →
  NvTranscriptAt Pin circuitSample nativeSample tInit tr pub →
  NvProgramTapeAt Pin programOf pinnedProgram tapeOf D stmtVec tr pub →
  NvVerifierArithAt Pin D V arithOK tr pub →
  NvLogUpAt Pin tr pub →
  V.accepts (D.stmt pub) (D.proof tr) (D.params tr) (V.run (D.stmt pub) (D.proof tr) (D.params tr))

/-! ## The six obligations, closed over all traces -/

/-- Sub-obligation 1 over all traces. -/
def NvShaGlue (Pin : NvPinned) (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat)
    (limbsOK : Trace Fp → Prop) : Prop :=
  ∀ tr pub, NvShaGlueAt Pin sha digestOf limbsOK tr pub

/-- Sub-obligation 2 over all traces. -/
def NvTranscript (Pin : NvPinned) (circuitSample : Trace Fp → Nat → List Fp)
    (nativeSample : List Fp → Nat → List Fp) (tInit : List Fp) : Prop :=
  ∀ tr pub, NvTranscriptAt Pin circuitSample nativeSample tInit tr pub

/-- Sub-obligation 3 over all traces. -/
def NvProgramTape (Pin : NvPinned) {Stmt Proof Params : Type} (programOf : Trace Fp → List Nat)
    (pinnedProgram : List Nat) (tapeOf : Trace Fp → List Fp) (D : NvDecode Stmt Proof Params)
    (stmtVec : Stmt → List Fp) : Prop :=
  ∀ tr pub, NvProgramTapeAt Pin programOf pinnedProgram tapeOf D stmtVec tr pub

/-- Sub-obligation 4 over all traces. -/
def NvVerifierArith (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params)
    (arithOK : Trace Fp → Stmt → Proof → Params → Prop) : Prop :=
  ∀ tr pub, NvVerifierArithAt Pin D V arithOK tr pub

/-- Sub-obligation 5 over all traces (**proved**: `nvLogUp`). -/
def NvLogUp (Pin : NvPinned) : Prop := ∀ tr pub, NvLogUpAt Pin tr pub

/-- **`NvLogUp` is proved.** -/
theorem nvLogUp (Pin : NvPinned) : NvLogUp Pin := fun tr pub => nvLogUpAt_proved Pin tr pub

/-- Sub-obligation 6 over all traces. -/
def NvComposition (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params)
    (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat) (limbsOK : Trace Fp → Prop)
    (circuitSample : Trace Fp → Nat → List Fp) (nativeSample : List Fp → Nat → List Fp)
    (tInit : List Fp) (programOf : Trace Fp → List Nat) (pinnedProgram : List Nat)
    (tapeOf : Trace Fp → List Fp) (stmtVec : Stmt → List Fp)
    (arithOK : Trace Fp → Stmt → Proof → Params → Prop) : Prop :=
  ∀ tr pub, NvCompositionAt Pin D V sha digestOf limbsOK circuitSample nativeSample tInit
    programOf pinnedProgram tapeOf stmtVec arithOK tr pub

/-! ## `NvFaithful` and the composition -/

/-- **The arbitrary-trace NV obligation (Lemma 7.1).**  For **every** trace and public vector that
satisfy the pinned AIR's constraints with the LogUp field balance, there is an accepting execution of
the pinned native inner verifier whose statement, proof and params are the trace's own decode — the
same openings, statement and params, nothing re-chosen.

The hypotheses are the trace predicate only.  There is no `tr`-shape restriction, no generator
assumption, and no hidden premise: the six sub-obligations enter solely through
`nvFaithful_of_obligations`, whose closure is this file's deliverable. -/
def NvFaithful (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params) : Prop :=
  ∀ tr pub, HoldsLogUp Pin.air pub tr →
    ∃ e : V.Execution (D.stmt pub) (D.proof tr) (D.params tr),
      V.accepts (D.stmt pub) (D.proof tr) (D.params tr) e

/-- **The composition: the six sub-obligations imply `NvFaithful`.**

This is the backbone.  Each of the five *stated* obligations supplies one component at the trace;
the sixth (LogUp) is proved, both as `NvLogUpAt` (needed by the composition step) and, inside it, as
`holds_of_holdsLogUp` (the field-to-natural step).  The composition obligation then says the five
components are exactly the native verifier's acceptance condition, and the conclusion's witness is
the verifier's canonical run — so `NvFaithful` is obtained *only* through the six, with no other
gap. -/
theorem nvFaithful_of_obligations (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params)
    (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat) (limbsOK : Trace Fp → Prop)
    (circuitSample : Trace Fp → Nat → List Fp) (nativeSample : List Fp → Nat → List Fp)
    (tInit : List Fp) (programOf : Trace Fp → List Nat) (pinnedProgram : List Nat)
    (tapeOf : Trace Fp → List Fp) (stmtVec : Stmt → List Fp)
    (arithOK : Trace Fp → Stmt → Proof → Params → Prop)
    (hSHA : NvShaGlue Pin sha digestOf limbsOK)
    (hTR : NvTranscript Pin circuitSample nativeSample tInit)
    (hPROG : NvProgramTape Pin programOf pinnedProgram tapeOf D stmtVec)
    (hARITH : NvVerifierArith Pin D V arithOK)
    (hLOGUP : NvLogUp Pin)
    (hCOMP : NvComposition Pin D V sha digestOf limbsOK circuitSample nativeSample tInit
      programOf pinnedProgram tapeOf stmtVec arithOK) :
    NvFaithful Pin D V := by
  intro tr pub h
  exact ⟨V.run (D.stmt pub) (D.proof tr) (D.params tr),
    hCOMP tr pub (hSHA tr pub) (hTR tr pub) (hPROG tr pub) (hARITH tr pub) (hLOGUP tr pub)⟩

/-- **The same composition with the LogUp obligation discharged.**  Only the five obligations about
the Rust circuit and the native verifier remain as hypotheses; the LogUp step is
`holds_of_holdsLogUp`, proved.  This is the precise statement of "what is left" for the paper: five
named hypotheses, each about a piece of the pinned circuit's semantics, and nothing else. -/
theorem nvFaithful_of_five (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params)
    (sha : ShaSpec) (digestOf : Trace Fp → List Nat → List Nat) (limbsOK : Trace Fp → Prop)
    (circuitSample : Trace Fp → Nat → List Fp) (nativeSample : List Fp → Nat → List Fp)
    (tInit : List Fp) (programOf : Trace Fp → List Nat) (pinnedProgram : List Nat)
    (tapeOf : Trace Fp → List Fp) (stmtVec : Stmt → List Fp)
    (arithOK : Trace Fp → Stmt → Proof → Params → Prop)
    (hSHA : NvShaGlue Pin sha digestOf limbsOK)
    (hTR : NvTranscript Pin circuitSample nativeSample tInit)
    (hPROG : NvProgramTape Pin programOf pinnedProgram tapeOf D stmtVec)
    (hARITH : NvVerifierArith Pin D V arithOK)
    (hCOMP : NvComposition Pin D V sha digestOf limbsOK circuitSample nativeSample tInit
      programOf pinnedProgram tapeOf stmtVec arithOK) :
    NvFaithful Pin D V :=
  nvFaithful_of_obligations Pin D V sha digestOf limbsOK circuitSample nativeSample tInit
    programOf pinnedProgram tapeOf stmtVec arithOK hSHA hTR hPROG hARITH (nvLogUp Pin) hCOMP

/-! ## Axiom guards

Everything asserted above is a definition, a proved theorem, or a hypothesis of a theorem.  The two
proved results (`nvLogUpInt_proved`, `holding_of_holdsLogUp` and its consumers) are checked below. -/

#print axioms nvLogUpInt_proved
#print axioms holds_of_holdsLogUp
#print axioms nvLogUpAt_proved
#print axioms nvLogUp
#print axioms nvFaithful_of_obligations
#print axioms nvFaithful_of_five

end ZkFormal.PQ.Nv

import ZkFormal.Air.Basic

/-!
# ZkFormal.V2.Air — the AIR DSL of `np-udr-stark-v2`: public-message bus (lane L4)

Design: `docs/zk-formal/V3-D0-DESIGN.md` §2.4, §10 decision 2.  `np-udr-stark-v2` is
`np-udr-stark-v1` plus a **public-message bus**: the verifier reads variable-length
lists of records from the public vector and puts them on the AIR's buses, as sends
or receives.  v1 is not modified.  Every v1 definition stays as it is.  A v2 AIR is a v1 AIR
(`AirP.toAir`) plus public segments, and `holdsP_iff_holds` shows that an AIR with no
segments has exactly v1's semantics.

## Public segments

A `PubSeg` describes `n` consecutive records of `width` field elements of the public
vector `pub`:

* `n` is read from `pub` at the static index `countAt`, as a little-endian base-256
  number of `4` elements (`pub` is the claim's bytes in the deployed verifier, so a
  segment can hold up to `2^32 - 1` records);
* record `j < n` is `pub[start + j·width + c]` for `c < width`;
* each record is one message on bus `bus`, sent (`send = true`) or received, with
  multiplicity one.

Field elements are read as naturals through `PubVal.val` (for BabyBear: the canonical
representative).  A segment **fits** if `start + n·width ≤ min |pub| maxPub`.  `HoldsP`
requires every segment to fit.  The verifier checks the same condition.  `maxPub`
is the static bound on the used part of `pub`.  Together with `width ≥ 1`
(`AirP.wf`), it bounds the number of public messages statically, which keeps the
grand-product soundness budgets (`fpBoundP`, `multBoundP`) finite.

## Semantics

`HoldsP AP pub tr` is v1's `Holds` with two changes:
* the segments fit;
* the balance counts public messages:
  `busCount send + pubCount send = busCount recv + pubCount recv` for every bus and message.
-/

namespace ZkFormal.V2

open ZkFormal.Air

/-- One public segment: `count` records of `width` elements on bus `bus`. -/
structure PubSeg where
  bus : Nat
  send : Bool
  width : Nat
  /-- Static `pub` index of the record count (4 elements, little-endian base 256). -/
  countAt : Nat
  /-- `pub` offset of the first record (records are consecutive, `width` each). -/
  start : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A v2 AIR: a v1 AIR plus public segments and a static bound on the used part of `pub`. -/
structure AirP extends Air where
  pubSegs : List PubSeg
  maxPub : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Reading a public element as a natural (the count of a segment). -/
class PubVal (F : Type) where
  val : F → Nat

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- Little-endian base-256 value of a list of digits. -/
def leNat : List Nat → Nat
  | [] => 0
  | d :: ds => d + 256 * leNat ds

/-- Number of records of segment `s` (4 public elements at `countAt`, little-endian). -/
def PubSeg.count (s : PubSeg) (pub : List F) : Nat :=
  leNat ((List.range 4).map fun k => PubVal.val (pub.getD (s.countAt + k) 0))

/-- Record `j` of segment `s`. -/
def PubSeg.record (s : PubSeg) (pub : List F) (j : Nat) : List F :=
  (List.range s.width).map fun c => pub.getD (s.start + j * s.width + c) 0

/-- The records of segment `s`. -/
def PubSeg.msgs (s : PubSeg) (pub : List F) : List (List F) :=
  (List.range (s.count pub)).map (s.record pub)

/-- The segment lies in `pub` and below the static bound. -/
def PubSeg.fits (s : PubSeg) (maxPub : Nat) (pub : List F) : Bool :=
  decide (s.start + s.count pub * s.width ≤ pub.length) &&
    decide (s.start + s.count pub * s.width ≤ maxPub)

/-- Every segment fits. -/
def pubFit (AP : AirP) (pub : List F) : Bool :=
  AP.pubSegs.all fun s => s.fits AP.maxPub pub

/-- All public messages `(bus, send, record)`, segment by segment. -/
def pubMsgs (AP : AirP) (pub : List F) : List (Nat × Bool × List F) :=
  AP.pubSegs.flatMap fun s => (s.msgs pub).map fun m => (s.bus, s.send, m)

/-- Multiplicity of message `m` on bus `b`, side `send`, among the public messages. -/
def pubCount (AP : AirP) (pub : List F) (b : Nat) (send : Bool) (m : List F) : Nat :=
  ((pubMsgs AP pub).filter fun x => decide (x = (b, send, m))).length

/-- **The v2 AIR semantic predicate**: v1's `Holds` with fitting public segments
and the public messages counted in every bus balance. -/
structure HoldsP (AP : AirP) (pub : List F) (tr : Trace F) : Prop where
  logBound : ∀ t (ht : t < AP.tables.length), 1 ≤ tr.log t ∧ tr.log t ≤ AP.tables[t].maxLog
  constr : ∀ t (ht : t < AP.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ AP.tables[t].constraints, e.eval tr t r pub = 0
  bits : ∀ t (ht : t < AP.tables.length), ∀ r, r < tr.height t →
    ∀ i ∈ AP.tables[t].interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1
  /-- Every public segment fits in `pub` and below `maxPub`. -/
  pubFit : pubFit AP pub = true
  /-- Every bus balances, public messages included. -/
  balance : ∀ b m, busCount AP.toAir tr pub b true m + pubCount AP pub b true m =
    busCount AP.toAir tr pub b false m + pubCount AP pub b false m

theorem pubMsgs_nil {AP : AirP} (h : AP.pubSegs = []) (pub : List F) : pubMsgs AP pub = [] := by
  simp [pubMsgs, h]

theorem pubCount_nil {AP : AirP} (h : AP.pubSegs = []) (pub : List F) (b : Nat) (s : Bool)
    (m : List F) : pubCount AP pub b s m = 0 := by
  simp [pubCount, pubMsgs_nil h]

/-- **v2 with no public segments is v1.** -/
theorem holdsP_iff_holds (AP : AirP) (h : AP.pubSegs = []) (pub : List F) (tr : Trace F) :
    HoldsP AP pub tr ↔ Holds AP.toAir pub tr := by
  constructor
  · intro hp
    refine ⟨hp.logBound, hp.constr, hp.bits, fun b m => ?_⟩
    have := hp.balance b m
    rw [pubCount_nil h, pubCount_nil h] at this
    simpa using this
  · intro hh
    refine ⟨hh.logBound, hh.constr, hh.bits, by simp [pubFit, h], fun b m => ?_⟩
    rw [pubCount_nil h, pubCount_nil h, hh.balance b m]

/-- A v1 AIR as a v2 AIR without public segments. -/
def AirP.ofAir (A : Air) : AirP := { A with pubSegs := [], maxPub := 0 }

theorem holdsP_ofAir (A : Air) (pub : List F) (tr : Trace F) :
    HoldsP (AirP.ofAir A) pub tr ↔ Holds A pub tr :=
  holdsP_iff_holds (AirP.ofAir A) rfl pub tr

end

/-! ## Static well-formedness (soundness budgets including public messages) -/

/-- Static bound on the number of public messages (per side, and in total):
a fitting segment of width `w ≥ 1` holds at most `maxPub / w` records. -/
def AirP.pubBound (AP : AirP) : Nat :=
  (AP.pubSegs.map fun s => AP.maxPub / s.width).sum

/-- Largest public record width. -/
def AirP.pubWidth (AP : AirP) : Nat := (AP.pubSegs.map (·.width)).foldr max 0

/-- v1's `multBound` plus the public messages (each of multiplicity one). -/
def AirP.multBoundP (AP : AirP) : Nat := AP.multBound + AP.pubBound

/-- v1's `fpBound` with the public messages counted:
`(#(row, interaction) pairs + #public messages) · (max message length + 1)`. -/
def AirP.fpBoundP (AP : AirP) : Nat :=
  ((AP.tables.map fun T => 2 ^ T.maxLog * T.interactions.length).sum + AP.pubBound) *
    (max ((AP.tables.flatMap fun T => T.interactions.map fun i => i.msg.length).foldr max 0)
      AP.pubWidth + 1)

/-- v2 well-formedness: v1's table conditions, public buses within `numBuses`,
record widths `≥ 1`, and the bad-challenge budgets with public messages counted.
(Implies v1's `Air.wf`; see `AirP.wf_air`.) -/
def AirP.wf (AP : AirP) (maxDeg : Nat) : Bool :=
  AP.tables.all (Table.wf AP.toAir maxDeg) &&
  AP.pubSegs.all (fun s => decide (s.bus < AP.numBuses) && decide (1 ≤ s.width)) &&
  decide (AP.multBoundP ≤ busBudget) && decide (AP.fpBoundP ≤ busBudget)

theorem AirP.multBound_le (AP : AirP) : AP.multBound ≤ AP.multBoundP := Nat.le_add_right _ _

theorem AirP.fpBound_le (AP : AirP) : AP.fpBound ≤ AP.fpBoundP := by
  unfold AirP.fpBoundP Air.fpBound
  exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.add_le_add_right (Nat.le_max_left _ _) 1)

/-- v2 well-formedness implies v1's. -/
theorem AirP.wf_air (AP : AirP) (d : Nat) (h : AP.wf d = true) : AP.toAir.wf d = true := by
  simp only [AirP.wf, Air.wf, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1.1.1, Nat.le_trans AP.multBound_le h.1.2⟩, Nat.le_trans AP.fpBound_le h.2⟩

end ZkFormal.V2

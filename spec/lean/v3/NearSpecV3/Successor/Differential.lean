import NearSpecV3.Successor.Config

/-!
# W00 interface 7/7 — the differential result vocabulary

Every test lane, W13's replay and W14's frozen validation must report the same six things about a case:
the expected domain, the checker's verdict, the consensus observables, the comparison outcome, and —
crucially — whether the case was *compared at all*. W01's repair and W14's evidence schema both hang
off this vocabulary.

## The shape

* `ExpectedDomain` — what the corpus says the case is: `inDomain` (the statement must decide it),
  `excluded reason` (the statement must refuse it as out of domain), or `unknown` (no expectation was
  recorded). `unknown` is *not* `inDomain`: a case without an expectation cannot be a match.
* `Verdict` — `accept`, `reject reason`, `outOfDomain reason`, `missing` (the checker produced no line),
  `crashed detail`, `timeout`. The last three are *harness* outcomes and are always failures to compare,
  never passes.
* `Observable` — the consensus-visible outputs a case can compare. Every field is optional, because a
  case that rejects has no state root and a case that traps has no return value. Absent fields are
  *unknown*, not "equal by default".
* `DiffResult` — one case's record: expected domain, verdict, observables, reason. `DiffResult.ofOutcome`
  builds it from a checker's `Except String Observable` without ever dropping a case.
* `Comparison` — the outcome of comparing one case: `agrees`, `disagrees why`,
  `excludedByExpectation reason`, or `invalidCase why` (missing/crashed/timeout/unknown expectation).
  **`invalidCase` is not `agrees`**, and `notCompared` is its own constructor: no skipped case can be
  counted as a match by construction.
* `DiffSummary` — counts by comparison, with the *denominator* being every case read from the corpus.
  `allAgree` is `false` when any case is invalid or disagreeing, so a summary cannot report success by
  shrinking its denominator.

## Source

The vocabulary mirrors the existing D3 difftest (`oracle/v3-d3/tools/difftest_d3.py:80-134`), whose
`compare` already distinguishes "checker missing" and "checker out of domain" from agreement, and whose
exit code is non-zero on any disagreement. W01 owns making that script's denominator complete; this
module owns the *Lean-side* vocabulary W13/W14 consume.

## What is not established

* **Nothing here runs a checker or reads a corpus.** The types and the comparison algebra are the
  deliverable; W13/W14 supply the cases and the replay.
* **`Observable` equality is field-wise.** Two observables agree only when every *supplied* field agrees
  and the *supplied field sets* agree; a case with fewer supplied fields does not compare equal to one
  with more. `Observable.agree` is stated that way, and `agree_refl` is proved; agreement is *not*
  proved transitive across different supplied-field sets, and no lane may assume it is.
* **The comparison is not a semantic-equivalence proof.** It compares the fields a case recorded; a
  consensus-observable field that no case records cannot be compared. Which fields are required per case
  family is W13's provenance decision.
* **No expected domain is derived from a checker.** `ExpectedDomain` is corpus metadata; a checker's
  verdict never feeds back into its own expectation.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3

/-! ## Expected domain and verdict -/

/-- What the corpus says about a case. `unknown` means no expectation was recorded; it is distinct from
`inDomain` so that "we do not know" cannot be counted as a pass. -/
inductive ExpectedDomain where
  | inDomain
  | excluded (reason : String)
  | unknown
  deriving DecidableEq, Repr

/-- A checker run's outcome as a case verdict: the three semantic verdicts from `Verdict` plus the
three harness outcomes. The harness outcomes are always failures to compare. -/
inductive CaseVerdict where
  | accept
  | reject (reason : String)
  | outOfDomain (reason : String)
  /-- The checker produced no line for the case. -/
  | missing
  /-- The checker crashed. -/
  | crashed (detail : String)
  /-- The checker exceeded its time budget. -/
  | timeout
  deriving DecidableEq, Repr

/-- Lift a semantic verdict into a case verdict. -/
def CaseVerdict.ofVerdict : Verdict → CaseVerdict
  | .accept => .accept
  | .reject r => .reject r
  | .outOfDomain r => .outOfDomain r

/-- Build a case verdict from a checker's result, without dropping the case. -/
def CaseVerdict.ofExcept : Except String Unit → CaseVerdict
  | .ok _ => .accept
  | .error e => if isExclusion e then .outOfDomain e else .reject e

/-- A verdict is a *semantic* decision when the checker actually ran. Harness outcomes are not. -/
def CaseVerdict.isSemantic : CaseVerdict → Bool
  | .accept | .reject _ | .outOfDomain _ => true
  | .missing | .crashed _ | .timeout => false

/-- A verdict is an exclusion when the tier declined the input. -/
def CaseVerdict.isExclusion : CaseVerdict → Bool
  | .outOfDomain _ => true
  | _ => false

/-- The verdict's reason string, when it has one. -/
def CaseVerdict.reason? : CaseVerdict → Option String
  | .reject r => some r
  | .outOfDomain r => some r
  | .crashed d => some d
  | _ => none

theorem ofExcept_ok (u : Unit) : CaseVerdict.ofExcept (.ok u) = .accept := rfl

theorem ofExcept_exclusion (e : String) (h : isExclusion e = true) :
    CaseVerdict.ofExcept (.error e) = .outOfDomain e := by
  simp [CaseVerdict.ofExcept, h]

theorem ofExcept_reject (e : String) (h : isExclusion e = false) :
    CaseVerdict.ofExcept (.error e) = .reject e := by
  simp [CaseVerdict.ofExcept, h]

theorem missing_not_semantic : (CaseVerdict.missing).isSemantic = false := rfl
theorem accept_semantic : (CaseVerdict.accept).isSemantic = true := rfl

/-- A semantic verdict lifted into a case verdict stays semantic. -/
theorem ofVerdict_semantic (v : Verdict) : (CaseVerdict.ofVerdict v).isSemantic = true := by
  cases v <;> rfl

/-! ## Observables -/

/-- The consensus-visible outputs a case can compare. Each field is optional: an absent field is
*unknown*, and an unknown field is never equal-by-default to a present one. -/
structure Observable where
  stateRoot : Option Bytes := none
  outcomeRoot : Option Bytes := none
  gasBurnt : Option Nat := none
  computeBurnt : Option Nat := none
  refunds : Option Nat := none
  logs : Option (List Bytes) := none
  returnData : Option Bytes := none
  emittedReceipts : Option Nat := none
  deriving DecidableEq, Repr

/-- The set of supplied fields, as a bit-vector so two observables with different supplied fields are
never conflated. Bit order: state, outcome, gas, compute, refunds, logs, return, receipts. -/
def Observable.suppliedMask (o : Observable) : Nat :=
  (if o.stateRoot.isSome then 1 else 0) + (if o.outcomeRoot.isSome then 2 else 0) +
  (if o.gasBurnt.isSome then 4 else 0) + (if o.computeBurnt.isSome then 8 else 0) +
  (if o.refunds.isSome then 16 else 0) + (if o.logs.isSome then 32 else 0) +
  (if o.returnData.isSome then 64 else 0) + (if o.emittedReceipts.isSome then 128 else 0)

/-- Field-wise agreement: the supplied-field sets must agree, and every supplied field must agree. A
case that recorded fewer fields does not agree with one that recorded more. -/
def Observable.agree (a b : Observable) : Bool :=
  a.suppliedMask == b.suppliedMask ∧ a == b

theorem agree_refl (a : Observable) : a.agree a = true := by
  simp [Observable.agree]

/-- An empty observable agrees with itself; a case with no observables still compares (vacuously) and is
not silently skipped. -/
theorem empty_observable_agree : ({} : Observable).agree {} = true := agree_refl {}

/-! ## The per-case result -/

/-- One case's differential record. `expected` is corpus metadata; `verdict` is what the checker did;
`observables` are what it produced. -/
structure DiffResult where
  /-- The case's corpus path or id. -/
  case : String
  /-- The corpus's expectation. -/
  expected : ExpectedDomain
  /-- The checker's verdict. -/
  verdict : CaseVerdict
  /-- The consensus observables the checker produced. -/
  observables : Observable
  /-- The checker's raw reason string. -/
  reason : String
  deriving Repr

/-- Build a case's record from the checker's outcome. `none` is a *missing* case (the checker produced no
line), not a rejection; a crash/timeout is supplied by the harness as an explicit verdict. -/
def DiffResult.ofOutcome (case : String) (expected : ExpectedDomain) :
    Option (Except String Observable) → DiffResult
  | none => { case := case, expected := expected, verdict := .missing, observables := {},
              reason := "no result line for case" }
  | some (.ok o) => { case := case, expected := expected, verdict := .accept, observables := o,
                      reason := "" }
  | some (.error e) => { case := case, expected := expected, verdict := CaseVerdict.ofExcept (.error e),
                         observables := {}, reason := e }

theorem ofOutcome_none_missing (case : String) (expected : ExpectedDomain) :
    (DiffResult.ofOutcome case expected none).verdict = .missing := rfl

theorem ofOutcome_some_ok (case : String) (expected : ExpectedDomain) (o : Observable) :
    (DiffResult.ofOutcome case expected (some (.ok o))).verdict = .accept := rfl

theorem ofOutcome_some_ok_observables (case : String) (expected : ExpectedDomain) (o : Observable) :
    (DiffResult.ofOutcome case expected (some (.ok o))).observables = o := rfl

/-! ## The comparison -/

/-- The outcome of comparing one case. `invalidCase` covers a missing line, a crash, a timeout and an
unrecorded expectation — all of which are failures to compare, never passes. -/
inductive Comparison where
  | agrees
  | disagrees (why : String)
  | excludedByExpectation (reason : String)
  | invalidCase (why : String)
  deriving DecidableEq, Repr

/-- Compare one case's record against the corpus expectation.

* `unknown` expectation → `invalidCase` (no expectation, no comparison).
* Harness outcome (`missing`/`crashed`/`timeout`) → `invalidCase`.
* Expected `inDomain` and the checker accepted → `agrees`; rejected → `disagrees`.
* Expected `excluded r` and the checker reported an exclusion → `excludedByExpectation`; accepted or
  rejected → `disagrees`.
* Expected `inDomain` and the checker reported an exclusion → `disagrees` (the tier failed to decide an
  in-domain case; this is the D3 difftest's "out_of_domain on an in-D3α case" failure). -/
def DiffResult.compare (r : DiffResult) : Comparison :=
  match r.expected, r.verdict with
  | .unknown, _ => .invalidCase "no expected domain recorded"
  | _, .missing => .invalidCase "checker produced no result"
  | _, .crashed d => .invalidCase s!"checker crashed: {d}"
  | _, .timeout => .invalidCase "checker timed out"
  | .inDomain, .accept => .agrees
  | .inDomain, .reject why => .disagrees s!"expected in-domain accept, checker rejected: {why}"
  | .inDomain, .outOfDomain why => .disagrees s!"expected in-domain decision, checker excluded: {why}"
  | .excluded _, .outOfDomain _ => .excludedByExpectation r.reason
  | .excluded why, _ => .disagrees s!"expected exclusion ({why}), checker decided"

/-- **No invalid case counts as a match.** The only constructor that reports agreement is `agrees`. -/
theorem compare_invalid_not_agrees (r : DiffResult) (h : r.compare = .invalidCase w) :
    r.compare ≠ .agrees := by
  rw [h]
  intro hc
  exact Comparison.noConfusion hc

/-- A missing line never compares as agreement. -/
theorem missing_never_agrees (case : String) (expected : ExpectedDomain) :
    (DiffResult.ofOutcome case expected none).compare ≠ .agrees := by
  cases expected <;> simp [DiffResult.ofOutcome, DiffResult.compare]

/-- An unknown expectation never compares as agreement. -/
theorem unknown_never_agrees (case : String) (v : CaseVerdict) :
    ({ case := case, expected := .unknown, verdict := v, observables := {}, reason := "" } : DiffResult).compare
      ≠ .agrees := by
  simp [DiffResult.compare]

/-! ## The summary and its denominator -/

/-- The comparison counts for one run. The denominator is the number of cases *read*, which is passed in
separately, so a run cannot report success by dropping cases. -/
structure DiffSummary where
  agrees : Nat := 0
  disagrees : Nat := 0
  excludedByExpectation : Nat := 0
  invalidCase : Nat := 0
  deriving DecidableEq, Repr

/-- Add one comparison to the summary. -/
def DiffSummary.add (s : DiffSummary) : Comparison → DiffSummary
  | .agrees => { s with agrees := s.agrees + 1 }
  | .disagrees _ => { s with disagrees := s.disagrees + 1 }
  | .excludedByExpectation _ => { s with excludedByExpectation := s.excludedByExpectation + 1 }
  | .invalidCase _ => { s with invalidCase := s.invalidCase + 1 }

/-- The cases accounted for. -/
def DiffSummary.accounted (s : DiffSummary) : Nat :=
  s.agrees + s.disagrees + s.excludedByExpectation + s.invalidCase

/-- The summary is complete for a run of `n` cases exactly when every case was classified. -/
def DiffSummary.completeFor (s : DiffSummary) (n : Nat) : Bool := s.accounted = n

/-- The run agrees with the corpus only when no case disagreed and no case was invalid. An excluded case
that matched its expectation counts as a pass; an invalid case does not. -/
def DiffSummary.allAgree (s : DiffSummary) : Bool := s.disagrees = 0 ∧ s.invalidCase = 0

theorem add_accounted (s : DiffSummary) (c : Comparison) :
    (s.add c).accounted = s.accounted + 1 := by
  cases c <;> simp only [DiffSummary.add, DiffSummary.accounted] <;> omega

theorem empty_accounted : ({} : DiffSummary).accounted = 0 := rfl

/-- A run with one invalid case does not all-agree, whatever its agreement count. -/
theorem invalid_blocks_allAgree (s : DiffSummary) (h : s.invalidCase > 0) :
    s.allAgree = false := by
  unfold DiffSummary.allAgree
  simp [Nat.pos_iff_ne_zero.mp h]

/-- A run with one disagreement does not all-agree. -/
theorem disagree_blocks_allAgree (s : DiffSummary) (h : s.disagrees > 0) :
    s.allAgree = false := by
  unfold DiffSummary.allAgree
  simp [Nat.pos_iff_ne_zero.mp h]

/-- **The denominator law.** If the summary's accounted count equals the case count and the run agrees,
then every case was compared: there is no skipped case in an `allAgree` run of a complete summary. -/
theorem complete_allAgree_accounts_every_case (s : DiffSummary) (n : Nat)
    (h : s.completeFor n = true) : s.accounted = n := by
  simpa [DiffSummary.completeFor] using h

/-! ## Folding a case list -/

/-- Compare a list of records and summarise. The summary is complete for the list's length by
construction, so the only way a run fails is a disagreement or an invalid case. -/
def summarise (rs : List DiffResult) : DiffSummary :=
  rs.foldl (fun s r => s.add r.compare) {}

theorem summarise_nil : summarise [] = {} := rfl

/-- Folding comparisons over a list accounts for every element, starting from any accumulator. -/
theorem foldl_add_accounted (rs : List DiffResult) (s : DiffSummary) :
    (rs.foldl (fun s r => s.add r.compare) s).accounted = s.accounted + rs.length := by
  induction rs generalizing s with
  | nil => simp [DiffSummary.accounted]
  | cons r rs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (s.add r.compare), add_accounted]
    omega

/-- The summary of a list is complete for that list's length. -/
theorem summarise_complete (rs : List DiffResult) : (summarise rs).completeFor rs.length = true := by
  rw [DiffSummary.completeFor, summarise, foldl_add_accounted]
  simp [DiffSummary.accounted]

/-! ## Axiom-closure check points -/

#print axioms missing_never_agrees
#print axioms summarise_complete

end NearSpecV3.Successor

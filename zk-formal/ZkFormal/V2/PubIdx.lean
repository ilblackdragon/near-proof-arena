import ZkFormal.V2.Air

/-!
# `PubIdx`: the public records of a v2 AIR, indexed by bus and side

A **shared interface** for link-layer proofs that need to know *which* records a public
segment carries. A link proof states what it needs as "the public records on bus `b`, side `s`
are `recs b s`", which is `PubIdx`. It never has to look at segment layout or `pub` offsets.

* `PubIdx AP pub enc`: a family `recs : Nat → Bool → List (List Nat)` of records per bus and
  side, with `pubCount AP pub b s M = ((recs b s).map (·.map enc)).count M` for every message `M`.
  `enc` is the embedding of record values into the field, e.g. `Fp.ofNat`.
* `PubIdx.ofPerm`: the "records are exactly these" constructor. If the public messages of
  every bus and side are a permutation of the encoded records, `PubIdx` holds.
* `PubIdx.count_filter`: the counting fact that link proofs use for one record kind, i.e. the
  records with a given head.

**Instantiation.** The indexed-public-segment protocol extension (R1, pending) must instantiate
`PubIdx` at assembly. It proves that the prepared statement's encoding puts exactly the rendered
records of each bus into the public segments. Until then, a link theorem takes a `PubIdx`
argument, and the assembly theorem discharges it. Users:
* the scheduler lane (`NearV3/Sched`): scan/raw records (`ScanPub.par`) and key records (`KeyPub`);
* the receipt lane will reuse it.
-/

namespace ZkFormal.V2

open ZkFormal.Air

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- The public messages on bus `b`, side `s` (payloads only). -/
def pubOn (AP : AirP) (pub : List F) (b : Nat) (s : Bool) : List (List F) :=
  ((pubMsgs AP pub).filter fun x => decide (x.1 = b ∧ x.2.1 = s)).map fun x => x.2.2

theorem pubCount_eq_count (AP : AirP) (pub : List F) (b : Nat) (s : Bool) (M : List F) :
    pubCount AP pub b s M = (pubOn AP pub b s).count M := by
  unfold pubCount pubOn
  induction pubMsgs AP pub with
  | nil => rfl
  | cons x t ih =>
    obtain ⟨b', s', m'⟩ := x
    by_cases h : b' = b ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := h
      by_cases hm : m' = M
      · subst hm; simp [List.filter_cons, ih]
      · simp [List.filter_cons, hm, ih, List.count_cons]
    · have h' : ¬ ((b', s', m') = (b, s, M)) := by
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
      simp only [List.filter_cons, h', decide_false, Bool.false_eq_true, ↓reduceIte, ih]
      have : decide (b' = b ∧ s' = s) = false := by simp [h]
      rw [this]; rfl

/-- **The public records of a v2 AIR, by bus and side.** -/
structure PubIdx (AP : AirP) (pub : List F) (enc : Nat → F) where
  recs : Nat → Bool → List (List Nat)
  count : ∀ b s M, pubCount AP pub b s M = ((recs b s).map (·.map enc)).count M

/-- **"The records are exactly these"**: the public messages of every bus and side are a
permutation of the encoded records. -/
def PubIdx.ofPerm {AP : AirP} {pub : List F} {enc : Nat → F} (recs : Nat → Bool → List (List Nat))
    (h : ∀ b s, (pubOn AP pub b s).Perm ((recs b s).map (·.map enc))) : PubIdx AP pub enc :=
  ⟨recs, fun b s M => by rw [pubCount_eq_count]; exact (h b s).count_eq M⟩

/-- Counting one record kind: if the records satisfying `P` are `L`, every message `M` with `P M`
occurs `L.count M` times. -/
theorem PubIdx.count_filter {AP : AirP} {pub : List F} {enc : Nat → F} (I : PubIdx AP pub enc)
    (b : Nat) (s : Bool) (P : List F → Bool) (L : List (List F))
    (hL : ((I.recs b s).map (·.map enc)).filter P = L) (M : List F) (hM : P M = true) :
    pubCount AP pub b s M = L.count M := by
  rw [I.count b s M, ← hL, List.count_filter hM]

end

end ZkFormal.V2

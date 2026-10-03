import ArenaCore.Verifier
import ArenaCore.Security.Adversary

/-!
# ArenaCore.Security.ROM — the random-oracle soundness game

For Fiat–Shamir-style (and Merkle-based) backends the profile may authorise
the random-oracle model (`sha256RandomOracle`).  The game is played against
the **deployed non-interactive verifier**, not an interactive protocol: the
verifier is an `OracleVerifier` (for the interpreter route: the candidate's
exact bytecode), and in the game *its* protocol-hash calls (`ROHASH`, deployed
as `SHA-256("NPAI-RO-v1" ‖ m)`) — together with the
adversary's and the honest prover's — are answered by one lazily-sampled
random oracle.

## Lazy sampling on a finite tape

The random oracle is a uniformly random function `Bytes → {0,1}^256`
restricted to the queried points.  It is represented by a tape of `n`
uniform symbols in `[0, 2^256)`: the i-th *distinct* query receives the
big-endian encoding of the i-th tape symbol; repeated queries are answered
consistently from the table.  For an experiment making at most `n` distinct
queries this is exactly a uniform random function on the queried points.
If the experiment makes *more* distinct queries than the tape holds, the
`overflow` flag is set and the experiment counts as **won by the
adversary** — so a candidate gains nothing by choosing the tape length too
short.

## Adversary

An oracle program over `romSpec W` that may ask

* `hash x`         — the random oracle at `x`;
* `prove cb w`     — the honest prover on claim bytes `cb` with witness `w`;
  answered only if `cb` decodes to a claim `c` with `Rel c w` (otherwise
  `[]`).  The honest prover's own hash calls go through the same oracle.

with separate, explicit budgets on hash queries and proof queries
(`hashWeight`, `proveWeight`).  It outputs `(claim, proof)`; it wins if the
verifier (with the same oracle) accepts a claim outside the language.
-/

namespace ArenaCore.Security

/-- Size of the random-oracle range: 2^256. -/
def roRange : Nat := 2 ^ 256

/-- Lazily-sampled random oracle state. -/
structure LazyRO where
  /-- unused fresh answers -/
  tape : List Nat
  /-- answered queries (most recent first) -/
  table : List (Bytes × Bytes)
  /-- set when a fresh query found the tape empty -/
  overflow : Bool

namespace LazyRO

def init (tape : List Nat) : LazyRO := ⟨tape, [], false⟩

/-- Fresh answer from a tape symbol: 32 big-endian bytes. -/
def answer (t : Nat) : Bytes := Bytes.beN 32 t

/-- The lazy random oracle, usable as the interpreter's/verifier's
`HashOracle`. -/
def query : Interp.HashOracle LazyRO := fun s x =>
  match s.table.lookup x with
  | some y => (y, s)
  | none =>
    match s.tape with
    | [] => (List.replicate 32 0, { s with overflow := true })
    | t :: ts => (answer t, { s with tape := ts, table := (x, answer t) :: s.table })

end LazyRO

/-- Adversary queries in the ROM game. -/
inductive RomQuery (W : Type) where
  | hash (x : Bytes)
  | prove (cb : Bytes) (w : W)

abbrev romSpec (W : Type) : OracleSpec := ⟨RomQuery W, fun _ => Bytes⟩

def hashWeight {W : Type} : RomQuery W → Nat
  | .hash _ => 1
  | .prove _ _ => 0

def proveWeight {W : Type} : RomQuery W → Nat
  | .hash _ => 0
  | .prove _ _ => 1

/-- ROM adversaries for challenge `S`. -/
abbrev RomAdversary (S : ChallengeSpec) := OracleComp (romSpec S.Witness) (Bytes × Bytes)

/-- Oracle implementation for the ROM game (hash: lazy RO; prove: honest
prover `P` on true statements only). -/
noncomputable def romImpl (S : ChallengeSpec) (P : OracleProver S) (pub : Bytes) :
    (q : RomQuery S.Witness) → LazyRO → Bytes × LazyRO
  | .hash x, s => LazyRO.query s x
  | .prove cb w, s =>
    open Classical in
    match S.decodeClaim cb with
    | some c => if S.Rel c w then P.run LazyRO.query s pub c w else ([], s)
    | none => ([], s)

/-- The adversary wins on `tape`: oracle overflow, or the verifier — run
with the same lazy oracle, continuing its state — accepts a claim outside
the language `L`. -/
noncomputable def romWins (S : ChallengeSpec) (L : Bytes → Prop) (v : OracleVerifier)
    (P : OracleProver S) (pub : Bytes) (A : RomAdversary S) (tape : List Nat) : Prop :=
  let r1 := OracleComp.simulate (romImpl S P pub) A (LazyRO.init tape)
  let r2 := v.run LazyRO.query r1.2 pub r1.1.1 r1.1.2
  r2.2.overflow = true ∨ (r2.1 = true ∧ ¬ L r1.1.1)

/-- ROM soundness: every adversary making at most `qHash` hash queries and
`qProve` proof queries wins with probability at most `num/den` over a tape
of `tapeLen` fresh oracle answers. -/
def RomSound (S : ChallengeSpec) (L : Bytes → Prop) (v : OracleVerifier) (P : OracleProver S)
    (pub : Bytes) (qHash qProve tapeLen num den : Nat) : Prop :=
  ∀ A : RomAdversary S,
    OracleComp.QueryBound hashWeight A qHash →
    OracleComp.QueryBound proveWeight A qProve →
    PrLE tapeLen roRange (romWins S L v P pub A) num den

theorem RomSound.mono {S : ChallengeSpec} {L L' : Bytes → Prop} (hLL' : ∀ cb, L cb → L' cb)
    {v : OracleVerifier} {P : OracleProver S} {pub : Bytes} {qH qP n num den : Nat}
    (h : RomSound S L v P pub qH qP n num den) : RomSound S L' v P pub qH qP n num den := by
  intro A hH hP
  refine PrLE.mono (fun t hw => ?_) (h A hH hP)
  unfold romWins at hw ⊢
  rcases hw with hw | ⟨hacc, hn⟩
  · exact Or.inl hw
  · exact Or.inr ⟨hacc, fun hL => hn (hLL' _ hL)⟩

end ArenaCore.Security

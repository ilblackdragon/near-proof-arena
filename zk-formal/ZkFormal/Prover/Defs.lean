import ZkFormal.Udr.Rbr
import ZkFormal.Bcs.TransDefs
import ZkFormal.Stark.ParseLemmas

/-!
# ZkFormal.Prover.Defs — the honest prover model `P` (lane L7)

The candidate's honest prover is the **BCS compilation of an honest IOP prover**,
written as a hash-query tree (`proveTree`), so that `TreeProver.toProver` runs it
against any oracle — the lazy random oracle of the ROM game, or a pure `H` in
`ProverComplete`.  It is a mathematical model (never executed; the Rust prover of
lane L8 is the executed one), but it is total and makes a bounded number of
oracle queries for *every* input.

* `IopProver F K`: a header and a next-message function on partial IOP transcripts
  (oracles are full matrices, `Stark.Oracle F`).
* `buildTree`: the MMCS tree of one oracle (FORMATS.md §5) — every node digest is
  one wide-hash `WH` (two oracle queries), leaves `WH(LEAF, rows)`, inner nodes
  `WH(NODE, u8 lvl ‖ l ‖ r ‖ rows)`.
* `multiproofBytes`: the multiproof stream that L4's `Stark.multiproof` parses.
* `proveTree V pr pub cb`: `d₀`, then for each slot of `V.schedule pr.hdr` either
  commit to `pr.next τ` (build trees, emit the message bytes, absorb) or derive the
  challenge exactly like the verifier's `chain`; then the query answers, the
  positions and all multiproofs.  A header that `V.headerOk` rejects yields the
  empty proof without any query.

`Reach V pr cb τ`: the IOP transcripts the honest prover reaches against any
challenges in the image of the challenge decoders; `IopComplete`: every reachable
complete transcript passes the global check and the local check at every position.
-/

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-- A pure hash function as the interpreter's stateless oracle (as in `ProverComplete`). -/
def pureH (H : Bytes → Bytes) : Interp.HashOracle Unit := fun u m => (H m, u)

/-- `mapM` for oracle computations (structural). -/
def mapOC {α β : Type} (f : α → OracleComp hashSpec β) : List α → OracleComp hashSpec (List β)
  | [] => .pure []
  | a :: as => OracleComp.bind (f a) fun b => OracleComp.bind (mapOC f as) fun bs => .pure (b :: bs)

/-- An honest IOP prover: its header and its next message on a partial transcript. -/
structure IopProver (F K : Type) where
  hdr : List Nat
  next : PT K (Oracle F) → List (PartV K (Oracle F))

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- Shapes `(log, width)` of an oracle. -/
def shapesOf (o : Oracle F) : List (Nat × Nat) := o.map fun M => (M.log, M.width)

/-- Bytes of the rows injected at depth `k` (matrices of log `k`), index `j`. -/
def rowsBytes (o : Oracle F) (k j : Nat) : Bytes :=
  (o.filter fun M => M.log == k).flatMap fun M => (M.row j).flatMap (encF (K := K))

/-- The MMCS tree of an oracle: `result[k]` = the `2^k` digests at depth `k`
(`k = 0` is the root, `k = n` the leaves, `n = treeLog`). -/
def buildTree (o : Oracle F) : OracleComp hashSpec (List (List Bytes)) :=
  let n := treeLog (shapesOf o)
  OracleComp.bind (mapOC (fun j => WH tagLeaf (rowsBytes (K := K) o n j)) (List.range (2 ^ n)))
    fun leaves => go n n leaves [leaves]
where
  /-- From depth `k` (digests `below`) up to the root. -/
  go (n : Nat) : Nat → List Bytes → List (List Bytes) → OracleComp hashSpec (List (List Bytes))
    | 0, _, acc => .pure acc
    | k + 1, below, acc =>
      OracleComp.bind (mapOC (fun j => WH tagNode ((UInt8.ofNat (n - k) :: below.getD (2 * j) []) ++
          below.getD (2 * j + 1) [] ++ rowsBytes (K := K) o k j)) (List.range (2 ^ k)))
        fun lvl => go n k lvl (lvl :: acc)

/-- The root of built tree levels. -/
def rootOf (lv : List (List Bytes)) : Bytes := (lv.getD 0 []).getD 0 []

/-- One level of a multiproof (parents at depth `k` of the known nodes at depth `k+1`,
ascending): for each parent, the missing sibling digest (if exactly one child is known),
then the injected rows.  Returns the bytes and the parents. -/
def upBytes (lv : List (List Bytes)) (o : Oracle F) (k : Nat) : List Nat → Bytes × List Nat
  | [] => ([], [])
  | [x] =>
    ((lv.getD (k + 1) []).getD (x ^^^ 1) [] ++ rowsBytes (K := K) o k (x / 2), [x / 2])
  | x :: x' :: rest =>
    if x % 2 = 0 ∧ x' = x + 1 then
      let r := upBytes lv o k rest
      (rowsBytes (K := K) o k (x / 2) ++ r.1, x / 2 :: r.2)
    else
      let r := upBytes lv o k (x' :: rest)
      ((lv.getD (k + 1) []).getD (x ^^^ 1) [] ++ rowsBytes (K := K) o k (x / 2) ++ r.1, x / 2 :: r.2)
termination_by l => l.length

/-- Levels `k = fuel-1, …, 0` of a multiproof stream. -/
def levelsBytes (lv : List (List Bytes)) (o : Oracle F) : Nat → List Nat → Bytes
  | 0, _ => []
  | k + 1, cur => let r := upBytes (K := K) lv o k cur; r.1 ++ levelsBytes lv o k r.2

/-- The multiproof stream of an oracle for sorted, duplicate-free leaf indices `S`. -/
def multiproofBytes (lv : List (List Bytes)) (o : Oracle F) (S : List Nat) : Bytes :=
  let n := treeLog (shapesOf o)
  S.flatMap (fun j => rowsBytes (K := K) o n j) ++ levelsBytes (K := K) lv o n S

/-- Openings of all oracles at positions `xs` (query domain `2^n0`). -/
def openBytes (n0 : Nat) (xs : List Nat) : List (Oracle F × List (List Bytes)) → Bytes
  | [] => []
  | (o, lv) :: os =>
    multiproofBytes (K := K) lv o (sortDedup (xs.map fun x => x >>> (n0 - treeLog (shapesOf o)))) ++
      openBytes n0 xs os

/-- Proof bytes of one part (`root` is used for oracle parts). -/
def partBytes : PartV K (Oracle F) → Bytes → Bytes
  | .header l, _ => encHeader l
  | .oracle _, root => root
  | .elems xs, _ => xs.flatMap (encK (F := F))

/-- Replace the oracles of a message by their roots (in order). -/
def withRoots : List (PartV K (Oracle F)) → List Bytes → List (PartV K Bytes)
  | [], _ => []
  | .oracle _ :: ps, r :: rs => .oracle r :: withRoots ps rs
  | .oracle _ :: ps, [] => .oracle [] :: withRoots ps []
  | .header l :: ps, rs => .header l :: withRoots ps rs
  | .elems xs :: ps, rs => .elems xs :: withRoots ps rs

/-- Proof bytes of a message given its roots. -/
def msgBytes : List (PartV K (Oracle F)) → List Bytes → Bytes
  | [], _ => []
  | .oracle o :: ps, r :: rs => partBytes (.oracle o) r ++ msgBytes ps rs
  | .oracle o :: ps, [] => partBytes (.oracle o) [] ++ msgBytes ps []
  | p :: ps, rs => partBytes p [] ++ msgBytes ps rs

/-- The oracles of a message, in order. -/
def msgOracles (m : List (PartV K (Oracle F))) : List (Oracle F) :=
  m.filterMap fun | .oracle o => some o | _ => none

/-- Commit-phase prover state. -/
structure CState (F K : Type) where
  d : Bytes
  τ : PT K (Oracle F)
  raw : Bytes
  trees : List (Oracle F × List (List Bytes))

/-- Commit to a message: build its trees, emit its bytes, absorb it. -/
def commitMsg (st : CState F K) (m : List (PartV K (Oracle F))) : OracleComp hashSpec (CState F K) :=
  let os := msgOracles m
  OracleComp.bind (mapOC (buildTree (K := K)) os) fun lvs =>
  let roots := lvs.map rootOf
  let raw := msgBytes (F := F) m roots
  OracleComp.bind (WH tagAbs (absBody st.d roots (clearOf (withRoots (F := F) m roots) raw))) fun d' =>
  .pure ⟨d', st.τ.push m, st.raw ++ raw, st.trees ++ os.zip lvs⟩

/-- The commit phase along a schedule. -/
def commitLoop (pr : IopProver F K) : List Slot → CState F K → OracleComp hashSpec (CState F K)
  | [], st => .pure st
  | .msg _ :: ss, st => OracleComp.bind (commitMsg st (pr.next st.τ)) fun st' => commitLoop pr ss st'
  | .chal ood :: ss, st =>
    OracleComp.bind (WH tagChal st.d) fun d' =>
    commitLoop pr ss ⟨d', st.τ.pushChal (Bcs.Transport.decChal (F := F) ood (d'.take 32)), st.raw, st.trees⟩

/-- **The honest prover model**: BCS compilation of the IOP prover `pr`. -/
def proveTree (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes) : OracleComp hashSpec Bytes :=
  if V.headerOk pr.hdr then
    OracleComp.bind (WH tagInit (initMsg pub cb)) fun d0 =>
    OracleComp.bind (commitLoop pr (V.schedule pr.hdr) ⟨d0, PT.init cb, [], []⟩) fun st =>
    OracleComp.bind (queryAnswers st.d V.numChunks) fun answers =>
    let n0 := V.queryLog pr.hdr
    .pure (st.raw ++ openBytes (K := K) n0 (V.positions n0 answers) st.trees)
  else .pure []

/-! ## IOP-side completeness -/

/-- Transcripts the honest IOP prover reaches against challenges in the image of the
challenge decoders (`decodeChal`, and `decodeOod` at the OOD slot). -/
inductive Reach (V : IopSpec F K) (pr : IopProver F K) (cb : Bytes) : PT K (Oracle F) → Prop
  | init : Reach V pr cb (PT.init cb)
  | msg (τ : PT K (Oracle F)) : Reach V pr cb τ → V.NextIsProver τ → Reach V pr cb (τ.push (pr.next τ))
  | chal (τ : PT K (Oracle F)) (ood : Bool) (y : Bytes) : Reach V pr cb τ →
      (V.slots τ)[τ.entries.length]? = some (.chal ood) →
      Reach V pr cb (τ.pushChal (Bcs.Transport.decChal (F := F) ood y))

/-- Perfect completeness of the IOP prover (every challenge sequence). -/
def IopComplete (V : IopSpec F K) (pr : IopProver F K) (cb : Bytes) : Prop :=
  ∀ τ, Reach V pr cb τ → V.AtQuery τ →
    V.global (V.prep τ.erase) = true ∧
    ∀ x, x < V.domSize τ → V.ChecksPass τ x (V.trueOpenings τ x)

/-- Well-formedness of the IOP prover (what serialization and parsing need). -/
structure ProverWf (V : IopSpec F K) (pr : IopProver F K) (cb : Bytes) : Prop where
  hdrOk : V.headerOk pr.hdr = true
  hdrLen : pr.hdr.length = V.numTables
  hdrSmall : ∀ h ∈ pr.hdr, h < 256
  tablesSmall : V.numTables < 2 ^ 32
  /-- every reachable transcript has the right shape … -/
  shaped : ∀ τ, Reach V pr cb τ → Udr.Shaped V τ
  /-- … and, once started, carries `pr.hdr` as its header. -/
  header : ∀ τ, Reach V pr cb τ → τ.entries ≠ [] → τ.header? = some pr.hdr

end

end ZkFormal.Prover

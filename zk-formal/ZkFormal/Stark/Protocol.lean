import ZkFormal.Air.Basic
import ZkFormal.Stark.Bcs

/-!
# ZkFormal.Stark.Protocol — `np-udr-stark-v1` as an `IopSpec` (lane L4)

`Iop.verifier A prm : IopSpec F K` is the IOP verifier of DESIGN.md §4 for the
AIR `A`; `verifier A prm : TreeVerifier` is its BCS compilation, the deployed
verifier model, and `verifier_eq_compile` holds by definition.  The exact
round structure, orderings and byte layout are specified in
`docs/zk-formal/FORMATS.md` §2–§4; this file is the normative definition.

Round structure for a header `logs` (table heights `2^logs[t]`, LDE logs
`m_t = logs[t] + logBlowup`, query domain `n0 = max m_t`):

| # | prover message                                  | challenge |
|---|-------------------------------------------------|-----------|
| 0 | header, main oracle (table `t`: `(m_t, width_t)`)| `α_fp`    |
| 1 | –                                               | `γ`       |
| 2 | aux oracle (`(m_t, 8·aux_t)`), finals (K)       | `α_c`     |
| 3 | quotient oracle (`(m_t, 8·quot_t)`)             | `z` (OOD) |
| 4 | OOD values (K)                                  | `r_1`     |
| 4+k | – (`k = 1 … L-1`)                             | `r_{k+1}` |
| FRI | per layer `i < ℓ`: [roll-in: – / `γ_i`], then `root_i` or – / `β_i` | |
| end | [roll-in at `ℓ`: – / `γ_ℓ`], final polynomial (2 K) | query phase |
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind ZkFormal.Air

/-! ## Static layout (from the AIR, the parameters and the header) -/

/-- Consecutive chunks of size `g ≥ 1` (the last one possibly shorter). -/
def chunksOf {α : Type} (g : Nat) (l : List α) : List (List α) := go l.length l
where
  go : Nat → List α → List (List α)
    | 0, _ => []
    | _, [] => []
    | f + 1, l => l.take g :: go f (l.drop g)

/-- Number of send (`s = true`) or receive interactions of a table. -/
def _root_.ZkFormal.Air.Table.numSide (T : Air.Table) (s : Bool) : Nat := (T.interactions.filter (fun (i : Interaction) => i.send == s)).length

/-- Running-product columns of one side: `⌈n / g⌉`. -/
def numGroups (n g : Nat) : Nat := (n + g - 1) / max g 1

/-- Aux columns (K) of a table: for every interaction with `k ≥ 2`
multiplicity bits, `k-1` power columns and `k-1` partial-product columns;
then the send running products, then the receive running products. -/
def _root_.ZkFormal.Air.Table.auxCount (T : Air.Table) (g : Nat) : Nat :=
  (T.interactions.map fun i => 2 * (i.mult.length - 1)).sum +
  numGroups (T.numSide true) g + numGroups (T.numSide false) g

/-- Formal degree of an interaction's fingerprint factor `φ_i`. -/
def _root_.ZkFormal.Air.Interaction.phiDegree (i : Interaction) : Nat :=
  match i.mult with
  | [] => 0
  | [b] => b.degree + (i.msg.map Expr.degree).foldr max 0
  | _ => 1

/-- Formal degree of the generated aux constraints of a table. -/
def _root_.ZkFormal.Air.Table.auxDegree (T : Air.Table) (g : Nat) : Nat :=
  let dm (i : Interaction) := (i.msg.map Expr.degree).foldr max 0
  let multi := T.interactions.map fun i =>
    match i.mult with
    | [] | [_] => 0
    | b0 :: b1 :: bs =>
      max (2 * dm i) (max 2 (max (b0.degree + dm i + b1.degree + 1)
        ((bs.map fun b => b.degree + 2).foldr max 0)))
  let side (s : Bool) : List Nat :=
    (chunksOf (max g 1) (T.interactions.filter (fun (i : Interaction) => i.send == s))).map fun grp =>
      2 + (grp.map Interaction.phiDegree).sum
  (multi ++ side true ++ side false).foldr max 2

/-- Constraint degree of a table (at least 2). -/
def _root_.ZkFormal.Air.Table.degree (T : Air.Table) (g : Nat) : Nat :=
  max (T.auxDegree g) ((T.allConstraints.map Expr.degree).foldr max 2)

/-- Number of quotient chunks (K columns): `degree - 1`. -/
def _root_.ZkFormal.Air.Table.quotCount (T : Air.Table) (g : Nat) : Nat := T.degree g - 1

/-- Per-table layout under a header. -/
structure TLayout where
  log : Nat
  lde : Nat
  width : Nat
  aux : Nat
  quot : Nat
  sendG : Nat
  recvG : Nat
  deriving Repr, DecidableEq, Inhabited

def layout (A : Air) (prm : Params) (hdr : List Nat) : List TLayout :=
  (A.tables.zip hdr).map fun (T, l) =>
    { log := l, lde := l + prm.logBlowup, width := T.width, aux := T.auxCount prm.auxGroup,
      quot := T.quotCount prm.auxGroup,
      sendG := numGroups (T.numSide true) prm.auxGroup,
      recvG := numGroups (T.numSide false) prm.auxGroup }

/-- `log₂` of the query domain (largest LDE). -/
def queryLog (A : Air) (prm : Params) (hdr : List Nat) : Nat :=
  ((layout A prm hdr).map (·.lde)).foldr max 0

/-- Index of the final FRI layer: degree bound `2^finalLog` reached. -/
def finalLayer (A : Air) (prm : Params) (hdr : List Nat) : Nat :=
  queryLog A prm hdr - prm.logBlowup - prm.finalLog

/-- Does a table class roll in at layer `i` (`0 < i`)? -/
def rollInAt (A : Air) (prm : Params) (hdr : List Nat) (i : Nat) : Bool :=
  0 < i && (layout A prm hdr).any fun L => L.lde + i == queryLog A prm hdr

/-- Number of DEEP functions of a class (LDE log `m`). -/
def classCount (lay : List TLayout) (m : Nat) : Nat :=
  ((lay.filter (·.lde == m)).map fun L => 2 * L.width + 2 * L.aux + L.quot).sum

/-- Number of multilinear batching rounds: `⌈log₂ (max class count)⌉`, at least 1. -/
def batchRounds (lay : List TLayout) : Nat :=
  let c := (lay.map fun L => classCount lay L.lde).foldr max 2
  max 1 (Nat.log2 (2 * c - 1))

/-- FRI layer `i < ℓ` is committed, with arity `2^a`: layer 0, roll-in layers,
and every `maxArityLog`-th layer after the previous commitment.  Returns the
committed layers with their arity logs. -/
def friCommits (A : Air) (prm : Params) (hdr : List Nat) : List (Nat × Nat) :=
  let ℓ := finalLayer A prm hdr
  go ℓ 0 ℓ
where
  /-- from committed layer `c` (fuel bounds the number of commitments) -/
  go (ℓ : Nat) : Nat → Nat → List (Nat × Nat)
    | _, 0 => []
    | c, fuel + 1 =>
      if ℓ ≤ c then [] else
      -- next stop: first roll-in layer in (c, c + maxArity], else c + maxArity, capped at ℓ
      let cand := (List.range prm.maxArityLog).map (c + 1 + ·)
      let nxt := match cand.find? (fun i => rollInAt A prm hdr i) with
        | some i => min i ℓ
        | none => min (c + max prm.maxArityLog 1) ℓ
      (c, nxt - c) :: go ℓ nxt fuel

/-! ## Header admissibility and the schedule -/

/-- Admissible headers: one log per table, `1 ≤ log ≤ maxLog`, the LDE fits
`maxLogLde` and the positions (`posBits`), and the AIR is well formed. -/
def headerOk (A : Air) (prm : Params) (hdr : List Nat) : Bool :=
  hdr.length == A.tables.length &&
  (A.tables.zip hdr).all (fun (T, l) => decide (1 ≤ l) && decide (l ≤ T.maxLog)
    && decide (l + prm.logBlowup ≤ prm.maxLogLde) && decide (l + prm.logBlowup ≤ prm.posBits)) &&
  A.wf (2 ^ prm.logBlowup) &&
  (A.tables.all fun T => decide (T.degree prm.auxGroup ≤ 2 ^ prm.logBlowup))

/-- The FRI part of the schedule. -/
def friSchedule (A : Air) (prm : Params) (hdr : List Nat) : List Slot :=
  let ℓ := finalLayer A prm hdr
  let commits := friCommits A prm hdr
  let n0 := queryLog A prm hdr
  let layer (i : Nat) : List Slot :=
    (if rollInAt A prm hdr i then [.msg [], .chal false] else []) ++
    (match commits.lookup i with
     | some a => [.msg [.oracle [(n0 - i - a, 8 * 2 ^ a)]], .chal false]
     | none => [.msg [], .chal false])
  ((List.range ℓ).flatMap layer) ++
  (if rollInAt A prm hdr ℓ then [.msg [], .chal false] else []) ++
  [.msg [.elems 2]]

def schedule (A : Air) (prm : Params) (hdr : List Nat) : List Slot :=
  let lay := layout A prm hdr
  let finals := (lay.map fun L => L.sendG + L.recvG).sum
  let ood := (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum
  [.msg [.header A.tables.length, .oracle (lay.map fun L => (L.lde, L.width))], .chal false,
   .msg [], .chal false,
   .msg [.oracle (lay.map fun L => (L.lde, 8 * L.aux)), .elems finals], .chal false,
   .msg [.oracle (lay.map fun L => (L.lde, 8 * L.quot))], .chal true,
   .msg [.elems ood], .chal false] ++
  ((List.range (batchRounds lay - 1)).flatMap fun _ => [.msg [], .chal false]) ++
  friSchedule A prm hdr

end ZkFormal.Stark

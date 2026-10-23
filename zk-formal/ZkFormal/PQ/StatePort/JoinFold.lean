import ZkFormal.PQ.StatePort.Join
import NearSpecV3.Wasm.Exec
import NearSpecV3.D2.Actions
import NearSpecV3.ChunkValidationD1a

/-!
# ZkFormal.PQ.StatePort.JoinFold — the interface between the state proof and the Wasm proof

Lane `pq-state-port`.  `Join.lean` proves the bus partition.  This module states the *composition
target* precisely enough that the two lanes can work against it without either re-deriving the
other, and records the one shape that is already forced by the spec.

Nothing here is proved beyond the trivialities it states about `Res`: the HOST chip, the host
tables and the coverage theorem do not exist yet (`JOIN-INTERFACE.md` §2–§5).  What is real is that
the *signature* is now fixed, so "the join" has a definition rather than a paragraph.

## The idea

`NearSpecV3.Wasm.run` is deterministic given the machine state.  A proved Wasm execution therefore
has a **fixed** trace, and the only thing the state proof can influence is what the host functions
answer.  That is exactly the abstraction the interface needs: the Wasm side proves

  `run X.cfg X.p n s0 = <outcome>`

*relative to a host-response function* `resp : Nat → HostAnswer` (time-indexed), and the state side
proves that `resp` is what the state tables actually did (trie reads/writes, gas, receipts).  Neither
side embeds the other.

`HostAnswer` is new here; `Res` and `St` are the existing spec types.
-/

namespace ZkFormal.PQ.StatePort

open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- What a host function returns: a status, its result words, the gas budget after the call
(`sync` + host cost), and the payload bytes (for register-filling calls).  `status` matches the
`HOSTR` message's second field (`JOIN-INTERFACE.md` §3). -/
structure HostAnswer where
  /-- `0` ok, `1` gas exceeded, `2` host error. -/
  status : Nat
  /-- Result words pushed back onto the operand stack. -/
  results : List UInt64
  /-- The budget register after the call (`g_after`). -/
  gasAfter : Nat
  /-- Payload bytes (register contents, `storage_read` values, context strings). -/
  bytes : List UInt8
  deriving Repr, Inhabited

/-- The abstract host: `resp ts` is what the host answers for the call at Wasm time `ts`. -/
abbrev HostResp := Nat → HostAnswer

/-- **The Wasm-side obligation**, as a proposition over the existing spec `run`.

**RETIRED CLAUSE (2026-10-23).**  This definition previously ended with the conjunct
`∀ ts ∈ hostTimes, resp ts = resp ts` — a tautology by `rfl`.  It was documented as "every response
was `resp` at that time", i.e. the HOST-chip correspondence, so it *looked* like the place where the
host half of the join was stated.  It stated nothing: `wasmRunStmt_iff` below proves the whole
relation is `run cfg p n s0 = outcome ∧ hostTimes.Pairwise (· < ·)`, with `resp` **unconstrained and
unmentioned**.  A join could therefore consume `WasmRunStmt` and learn nothing about the host.

The honest host correspondence is *not* expressible as an equation about `resp` alone: it must relate
`resp` to the host calls the abstract machine actually made, which needs the HOST message tape that
`WasmBase.HostChip` owns.  That is the `[O]` half named in
`docs/logs/pq-prepare-link-2026-10-23.md`; it is not reconstructed here, because inventing a second
vague predicate would just relocate the problem the way `compose_pv86` relocated `join_additive`'s.

What this definition now says, explicitly and nothing more: the spec run's outcome is `outcome`, and
the host-call times are strictly increasing.  Both are real and checkable; neither is the host
correspondence. -/
def WasmRunStmt (cfg : NearCfg) (p : Prepared) (n : Nat) (s0 : St) (resp : HostResp)
    (hostTimes : List Nat) (outcome : Res) : Prop :=
  run cfg p n s0 = outcome ∧
  hostTimes.Pairwise (· < ·)

/-- **`WasmRunStmt` carries no host content.**  The `resp` argument is inert: any `resp` satisfies
the relation as soon as the run and the time-order do.  This is the theorem that stops a future pass
from citing `WasmRunStmt` as the Wasm/host half of the join. -/
theorem wasmRunStmt_iff (cfg : NearCfg) (p : Prepared) (n : Nat) (s0 : St) (resp : HostResp)
    (ts : List Nat) (out : Res) :
    WasmRunStmt cfg p n s0 resp ts out ↔ run cfg p n s0 = out ∧ ts.Pairwise (· < ·) :=
  Iff.rfl

/-- **The host response is not constrained by `WasmRunStmt`.**  Two different host behaviours that
agree on nothing still both satisfy the obligation for the same run.  Stated as an explicit witness
so the inertness is visible without reading the `iff`. -/
theorem wasmRunStmt_resp_inert (cfg : NearCfg) (p : Prepared) (n : Nat) (s0 : St)
    (resp resp' : HostResp) (ts : List Nat) (out : Res) :
    WasmRunStmt cfg p n s0 resp ts out ↔ WasmRunStmt cfg p n s0 resp' ts out :=
  Iff.rfl

/-- **RETIRED 2026-10-22 — this statement is vacuous and is NOT the D3 join.**

Kept only so the audit trail in `zk-formal/test/AuditPQStatePort.lean` and the reports that cite
it still elaborate.  Do not cite it as the join and do not strengthen it: its conclusion type is
`RelD1a`, so no proof of it can ever reach `NearSpecV3.D3.RelD3`.

The defect is structural and independent of the proof.  A `RelD1a` witness contains **no**
`FunctionCall` at all, on three decoder rejects (`TxD1.lean:97`, `Codec.lean:75`,
`ChunkValidationD1.lean:63`), so the `runs` hypothesis constrains nothing and the statement is
`RelD1a → RelD1a`.  `join_additive` below is the one-line proof that this is so;
`ZkFormal.PQ.Join.joinStmt_backing_is_erasable` (`Join/Compose.lean`) proves the backing
hypothesis is erasable, i.e. the vacuity is a theorem rather than an accident.

The honest replacement is `ZkFormal.PQ.Join.compose_pv86` (`Join/Compose.lean`), whose conclusion
is `NearSpecV3.D3.RelD3` on the **D2** witness — the relation the D3 verifier actually checks —
with the per-call agreement `hagree` and the state pipeline verdict `hstate` as its real premises. -/
def JoinStmt : Prop :=
  ∀ (B : Nat) (cb w : Bytes) (cfg : NearCfg) (resp : HostResp)
    (runs : List (Prepared × Nat × St × Res)),
    NearSpecV3.RelD1a B cb w →
    (∀ r ∈ runs, ∃ (p : Prepared) (n : Nat) (s0 : St) (ts : List Nat) (out : Res),
      r = (p, n, s0, out) ∧ WasmRunStmt cfg p n s0 resp ts out) →
    NearSpecV3.RelD1a B cb w

/-- **`join_additive` is a vacuity witness, not a join.**  The proof is `exact hrel`: the
conclusion is the premise.  Its value is that it makes the defect checkable — the statement cannot
be satisfied in any other way, so it cannot be the D3 join.  See `JoinStmt`'s docstring and
`Join/Compose.lean` for the replacement (`compose_pv86`, concluding `RelD3`).

The name is kept for the audit file's `#check`; treat it as `[K]` evidence *of the vacuity*, not
evidence of a join. -/
theorem join_additive : JoinStmt := by
  intro B cb w cfg resp runs hrel _hruns
  exact hrel

end ZkFormal.PQ.StatePort

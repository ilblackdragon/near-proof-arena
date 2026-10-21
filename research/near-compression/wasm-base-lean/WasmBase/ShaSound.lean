import WasmBase.ShaAir
/-!
# WasmBase.ShaSound — the SHA-256 AIR's digest is the spec's `sha256`

The classical table's soundness (`ZkFormal.Sha.sha_bus_sound_closed`) is stated about
`ZkFormal.Air.Holds`, i.e. about `ZkFormal.Air.Expr` evaluation on a `ZkFormal.Air.Trace`.  Two
bridges move it to the PQ stack; neither re-proves any SHA-256 arithmetic:

* `eval_z` — a `WasmBase` evaluation of the embedding `toW e` on a row equals the classical
  `ZkFormal.Air.Expr.eval` of `e` on the same row of the same trace, when the table height is a
  power of two (`hpow`).  This is what makes the PQ table *the same constraint system*;
* `sha_local` — the resulting `ZkFormal.Sha.ShaLocal` hypothesis;
* `sha_digest_is_spec` — `ZkFormal.Sha.sha_bus_sound_closed` applied to it.

Nothing about SHA-256 is proved here: the digest is `ArenaCore.sha256`, which
`NearSpecV3.Wasm.Crypto.sha256` *is* (`Crypto.lean:16`), i.e. the function the NEAR `sha256` host
call applies (`Host.lean:629`, `Host.hashHost C.sha256Base C.sha256Byte Crypto.sha256`).
-/
namespace WasmBase
namespace Chips
namespace Sha

/-- A power-of-two `WasmBase` trace as a classical trace with the same cells
(`log = log₂ height`). -/
def toZTrace (tr : Trace) : ZkFormal.Air.Trace F := ⟨fun t => Nat.log2 (tr.height t), tr.cell⟩

theorem toZTrace_height (tr : Trace) (t : Nat) (hpow : tr.height t = 2 ^ Nat.log2 (tr.height t)) :
    (toZTrace tr).height t = tr.height t := by
  simp only [ZkFormal.Air.Trace.height, toZTrace]
  exact hpow.symm

/-- **The embedding preserves evaluation.**  The classical value of `e` on row `(t, r)` of
`toZTrace tr` is the PQ value of `toW e` on the same row of `tr`.  The only side condition is that
the table height is a power of two, because that is where the two cyclic next rows coincide
(`(r+1) % 2^log₂ H` vs `(r+1) % H`).

Proved pointwise on the expression, so neither an `Env` structure equality nor a `Decidable`
instance transport is needed. -/
theorem eval_z (tr : Trace) (pub : List F) (t r : Nat)
    (hpow : tr.height t = 2 ^ Nat.log2 (tr.height t)) (e : ZkFormal.Air.Expr) :
    e.eval (toZTrace tr) t r pub = (toW e).eval (tr.row pub t r) := by
  have hH : (toZTrace tr).height t = tr.height t := toZTrace_height tr t hpow
  rw [ZkFormal.Air.Expr.eval]
  induction e with
  | const n => rfl
  | col c nx =>
    cases nx with
    | false => rfl
    | true =>
      simp only [ZkFormal.Air.Expr.evalWith]
      show tr.cell t ((r + 1) % (toZTrace tr).height t) c = tr.cell t ((r + 1) % tr.height t) c
      rw [hH]
  | pub i => rfl
  | isFirst =>
    show (if r = 0 then (1 : F) else 0) = (if r == 0 then (1 : F) else 0)
    simp
  | isLast =>
    show (if r + 1 = (toZTrace tr).height t then (1 : F) else 0) = (if r + 1 == tr.height t then 1 else 0)
    rw [hH]; simp
  | isTransition =>
    show (if r + 1 = (toZTrace tr).height t then (0 : F) else 1) = (if r + 1 == tr.height t then 0 else 1)
    rw [hH]; simp
  | add a b iha ihb =>
    show (ZkFormal.Air.rowEnv (toZTrace tr) t r pub).add _ _ = _ + _
    rw [iha, ihb]
    rfl
  | mul a b iha ihb =>
    show (ZkFormal.Air.rowEnv (toZTrace tr) t r pub).mul _ _ = _ * _
    rw [iha, ihb]
    rfl
  | neg a ih =>
    show (ZkFormal.Air.rowEnv (toZTrace tr) t r pub).neg _ = _
    rw [ih]
    exact WasmBase.Chips.neg_eq_zero_sub _

/-- **A power-of-two `WasmBase` trace of the SHA table satisfies every classical constraint.** -/
theorem sha_constr_of_holds {A : Air} {pub : List F} {tr : Trace} {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = table)
    (h : Holds A pub tr) (hpow : tr.height t = 2 ^ Nat.log2 (tr.height t))
    (r : Nat) (hr : r < tr.height t) (e : ZkFormal.Air.Expr)
    (he : e ∈ ZkFormal.Sha.Table.constraints) :
    e.eval (toZTrace tr) t r pub = 0 := by
  have hmem : toW e ∈ constraints := by
    simp only [constraints]
    exact List.mem_append_left _ (List.mem_map_of_mem he)
  have hc := h.constr t ht r hr (toW e) (by rw [hT]; exact hmem)
  rw [eval_z tr pub t r hpow]
  exact hc

/-- One row of the PQ SHA table satisfies every classical constraint (the `ShaLocal` hypothesis of
the classical soundness theorems).  `hge`/`hle` are the classical height bounds `1 ≤ log ≤ 22`. -/
theorem sha_local {A : Air} {pub : List F} {tr : Trace} {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = table)
    (h : Holds A pub tr) (hpow : tr.height t = 2 ^ Nat.log2 (tr.height t))
    (hge : 1 ≤ Nat.log2 (tr.height t)) (hle : Nat.log2 (tr.height t) ≤ 22) :
    ZkFormal.Sha.ShaLocal (toZTrace tr) t pub where
  log_ge := hge
  log_le := by simpa [ZkFormal.Sha.Table.maxLog, toZTrace] using hle
  constr := by
    intro r hr e he
    have hH : (toZTrace tr).height t = tr.height t := toZTrace_height tr t hpow
    exact sha_constr_of_holds ht hT h hpow r (by rwa [hH] at hr) e he

/-- **The AIR's digest is the spec's hash.**  Any digest row of a legal PQ SHA table holds the
SHA-256 of the message the table lays out before it.  The function is `ArenaCore.sha256`, which
`NearSpecV3.Wasm.Crypto.sha256` is defined to be, i.e. the function the NEAR `sha256` host call
applies.

Proof: the classical soundness theorem (`sha_bus_sound_closed`), with `sha_local` supplying its
hypothesis.  No new SHA proof, no new axiom. -/
theorem sha_digest_is_spec {A : Air} {pub : List F} {tr : Trace} {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = table)
    (h : Holds A pub tr) (hpow : tr.height t = 2 ^ Nat.log2 (tr.height t))
    (hge : 1 ≤ Nat.log2 (tr.height t)) (hle : Nat.log2 (tr.height t) ≤ 22) :
    ∀ p ∈ ZkFormal.Sha.View.digests (toZTrace tr) t,
      p.2 = ArenaCore.sha256 p.1 :=
  ZkFormal.Sha.sha_bus_sound_closed (sha_local ht hT h hpow hge hle)

/-- **The spec-level hash is the AIR's hash.**  `NearSpecV3.Wasm.Crypto.sha256` — the function the
NEAR `sha256` host call applies (`Host.lean:629`) — is by definition
`⟨(ArenaCore.sha256 m.toList).toArray⟩` (`Crypto.lean:16`), i.e. the very function
`sha_digest_is_spec` reads off the AIR.  So a digest row's bytes are the spec's `sha256` of the
register bytes the call read, with no second hash implementation anywhere. -/
theorem crypto_sha256_eq (m : ByteArray) :
    NearSpecV3.Wasm.Crypto.sha256 m =
      (⟨(ArenaCore.sha256 m.toList).toArray⟩ : ByteArray) := rfl

end Sha
end Chips
end WasmBase

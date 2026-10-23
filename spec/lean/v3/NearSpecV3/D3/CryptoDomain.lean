import NearSpecV3.Wasm.Exec
import NearSpecV3.Wasm.CryptoHost

/-!
# `D3γ`: the crypto-enabled successor domain (ecrecover / p256_verify)

**This module does not change `checkD3`, `RelD3` or the signed `near-chunk-v3` statement.** It
records what the `D3α` exclusion guard (`Wasm.Exec.curveHosts`, rows `L0-W-015` and the 14
`L0-host-*` rows of `docs/research/lean-chunk-coverage.json`) actually excludes, and states the
obligations a successor relation has to discharge for each host it enables.

## What the guard is, precisely

`D3α` has two independent curve-host tests:

1. `Exec.runCall … (real := none)` — the harness/mock-`External` path — rejects a module that
   merely *imports* one of the 14 names (`Exec.lean:462-464`, line
   `out-of-domain curve host function`).
2. `Wasm.Host.hostCall` has no arm for any of them, so under the chunk path
   (`real := some _`, `D3.functionCall`) *calling* one yields `unmodeled host function … not
   modelled in D3α` (`Exec.lean:77-80`), which `D3.functionCall` converts to
   `out of domain (e.wasm-α)` (`D3/FunctionCall.lean:365-368`). Importing one is in domain
   (`spec/near-chunk-validation-d3.md` §10.0a P3).

`hostCall_no_arm` below kernel-checks (2) for all 14 names: the first fact a "we implemented the
curve hosts" claim has to overturn, and the reason a row cannot be marked `implemented` on the
strength of a compile.

## Obligations for enabling a host (per name)

A successor relation `RelD3γ` that admits a call to host `h` must, for that `h`:

* **codec** — the exact `(len, ptr)`/register argument reading of `logic.rs`, in the same order
  (gas is paid before bounds checks);
* **semantics** — the bytes actually transformed, in Lean (not a `Bool` hypothesis, not an oracle
  verdict);
* **gas** — `wasm_<h>_base`/`_element`/`_byte` from `core/parameters/res/runtime_configs/
  parameters.snap` at PV86, plus the `base`/`*_memory_*`/`*_register_*` charges of the reads and
  the register write;
* **return/error split** — which malformed inputs are `HostError`s and which are a `0` return
  (`ecrecover` differs from `p256_verify` on nearly every one);
* **whole-chunk** — one valid and one invalid chunk whose witness nearcore accepts, with the
  host result committed by the chunk's post-state root.

`ecrecover` discharges the first four here (see `Secp256k1.lean`, `Wasm/CryptoHost.lean` and
`nearspec-v3-test-crypto`); it does **not** discharge the fifth, because enabling it inside
`Wasm.runCall` would require threading a second host table through `Exec.step`/`callFunc` and
repairing the `Logged` commutation proofs, which is not an additive change to the signed closure.
Its inventory row therefore stays `partial`.
-/

namespace NearSpecV3.Wasm

/-- The `D3α` exclusion list (`Exec.curveHosts`, 14 names) and the successor table's name list
are the same set: `D3γ` enables exactly the hosts `D3α` excludes, and nothing else. -/
theorem cryptoHosts_iff_curveHosts (n : String) :
    cryptoHosts.contains n = curveHosts.contains n := by
  simp [cryptoHosts, curveHosts]

/-- **The guard, kernel-checked**: `D3α`'s host table has no arm for any name in `curveHosts`.
Hence `Exec.callHost` reports `unmodeled …` for it, and `D3.functionCall` maps that to
`out of domain (e.wasm-α)` whenever a chunk calls one. -/
theorem hostCall_no_arm :
    hostCall "alt_bn128_g1_multiexp" = none ∧ hostCall "alt_bn128_g1_sum" = none ∧
    hostCall "alt_bn128_pairing_check" = none ∧ hostCall "bls12381_p1_sum" = none ∧
    hostCall "bls12381_p2_sum" = none ∧ hostCall "bls12381_g1_multiexp" = none ∧
    hostCall "bls12381_g2_multiexp" = none ∧ hostCall "bls12381_map_fp_to_g1" = none ∧
    hostCall "bls12381_map_fp2_to_g2" = none ∧ hostCall "bls12381_pairing_check" = none ∧
    hostCall "bls12381_p1_decompress" = none ∧ hostCall "bls12381_p2_decompress" = none ∧
    hostCall "ecrecover" = none ∧ hostCall "p256_verify" = none := by
  decide

/-- `ed25519_verify` is *not* in the exclusion list: `D3α` models it (`Host.lean:1024-1033`).
This is why the `ed25519_verify` row is L4's `implemented` row and not one of L3's 15. -/
theorem ed25519_not_excluded : curveHosts.contains "ed25519_verify" = false := by decide

/-- ... and it does have an arm. -/
theorem ed25519_has_arm : (hostCall "ed25519_verify").isSome = true := by decide

end NearSpecV3.Wasm

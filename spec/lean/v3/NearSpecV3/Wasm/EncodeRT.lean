import NearSpec.ClaimCodec
import NearSpecV3.Wasm.Segment

/-!
# `readU64` inverts `u64`: the corollary the state encoder needs

**Most of this already existed, and this file exists to point at it rather than duplicate it.**
`NearSpec/ClaimCodec.lean` proves the general little-endian round-trip machinery:

| lemma | statement |
|---|---|
| `leN_length` | `(leN w x).length = w` |
| `leNat_leN` | `leNat (leN w x) = x` for `x < 256^w` |
| `takeN_append` | `takeN a.length (a ++ b) = some (a, b)` |
| `readLE_append` | `readLE w (leN w x ++ rest) = some (x, rest)` for `x < 256^w` |
| `readBorshBytes_append` | same for borsh byte strings |

So the hard work was already done, in a **stronger** form than a naive `% 256^w` statement
(the hypothesis `x < 256^w` recovers `x` exactly rather than modulo). What was missing is the
`Nat`-level corollary with an empty remainder, which is what the structure encoders in
`Wasm/StEncode.lean` will consume:

* `readU64_u64` — `readU64 (u64 n) = some (n, [])` for `n < 2^64`

This is a two-line consequence of `readLE_append`; it is written out because it is the exact
shape needed and because `Wasm/` should not have to depend on claim-codec internals to state it.

**Note on provenance.** An earlier draft of this file re-proved `leNat_leN` from scratch and
failed to build, because `NearSpec.lean`'s import of `ClaimCodec` already provides the name.
That duplication was found by the build, not by inspection; the search should have come first.
-/

namespace NearSpec

/-- `readU64` inverts `u64` on the `u64` range, consuming everything. -/
theorem readU64_u64 (n : Nat) (h : n < 2^64) : readU64 (u64 n) = some (n, []) := by
  have h256 : (256 : Nat)^8 = 2^64 := by decide
  have h' : n < 256^8 := by rw [h256]; exact h
  have := readLE_append 8 n [] h'
  simpa [readU64, u64] using this

end NearSpec

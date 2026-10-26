import NearSpecV3.MlDsa65
import NearSpecV3.Examples.MlDsaAcvp
import NearSpecV3.Examples.MlDsaCrate

/-!
# `MlDsa65.verify` pinned against NIST ACVP and the pinned crate

Built in the default target, so a regression in any part of FIPS 204 verification (SHAKE, NTT,
`ExpandA`, `SampleInBall`, `UseHint`, `w1Encode`, hint unpacking, the norm bound, the domain
prefix) fails the build.

* `MlDsaAcvp.vectors`: 45 NIST ACVP sigVer tests of ML-DSA-65 (9 accept, 36 reject): the pure
  external interface with non-empty context strings (`verifyCtx`), the internal interface
  (`verifyInternal`) and the external-μ interface (`verifyMu`). Each rejected test modifies the
  message, `c̃`, `z` or the hint.
* `MlDsaCrate.cases`: 74 verdicts of `near_crypto::Signature::verify` (12 accept, 62 reject) on
  the inputs nearcore produces: 32-byte messages, empty context, two keys. Beyond wrong key / wrong
  message / field flips they cover every malformed-hint class of FIPS 204 Algorithm 21:
  indices out of order inside a polynomial (`hint-unordered` keeps the same hint *set*, so only
  the ordering check rejects it), duplicates, a count above `ω` or equal to 255, a decreasing
  count, a non-zero unused slot (`hint-padding-nonzero`, again the same set), and two
  well-formed-but-wrong hints; plus `z` packed at `±γ1` and all-zero / all-`0xFF` signatures.

The checks run in the compiled evaluator (`#guard`); about 0.45 s per verification in the
interpreter. The checker binary runs one in about 2 ms (see the evidence README).
-/

namespace NearSpecV3.Examples.MlDsaVectors

open NearSpecV3.MlDsa65

def hexNib (c : Char) : UInt8 :=
  UInt8.ofNat (if c.toNat ≤ 57 then c.toNat - 48 else if c.toNat ≤ 70 then c.toNat - 55 else c.toNat - 87)

def unhex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (hexNib cs[2 * i]! * 16 + hexNib cs[2 * i + 1]!)
  out

def acvpOk (v : String × Nat × Bool × String × String × String × String × String) : Bool :=
  let (kind, _, expect, pk, msg, ctx, mu, sig) := v
  let got :=
    if kind == "ext" then verifyCtx (unhex pk) (unhex msg) (unhex sig) (unhex ctx)
    else if kind == "mu" then verifyMu (unhex pk) (unhex mu) (unhex sig)
    else verifyInternal (unhex pk) (unhex msg) (unhex sig)
  got == expect

/-- The ACVP test ids `MlDsa65` disagrees on; must be empty. -/
def acvpFailures : List Nat :=
  (MlDsaAcvp.vectors.toList.filter (fun v => !acvpOk v)).map (·.2.1)

def crateSig (sigIdx : Nat) (patch : List (Nat × Nat)) : List UInt8 :=
  let base := (unhex MlDsaCrate.sigs[sigIdx]!).toList
  patch.foldl (fun s (o, b) => s.set o b.toUInt8) base

def crateOk (c : String × Nat × String × Nat × List (Nat × Nat) × Bool) : Bool :=
  let (_, key, msg, sigIdx, patch, expect) := c
  verify (unhex MlDsaCrate.keys[key]!).toList (crateSig sigIdx patch) (unhex msg).toList == expect

/-- The crate cases `MlDsa65.verify` (nearcore's entry point) disagrees on; must be empty. -/
def crateFailures : List String :=
  (MlDsaCrate.cases.toList.filter (fun c => !crateOk c)).map (·.1)

#guard MlDsaAcvp.vectors.size == 45
#guard (MlDsaAcvp.vectors.toList.filter (·.2.2.1)).length == 9
#guard acvpFailures == []

#guard MlDsaCrate.cases.size == 74
#guard (MlDsaCrate.cases.toList.filter (·.2.2.2.2.2)).length == 12
#guard crateFailures == []

/-! Wrong-length inputs are rejected before decoding (nearcore's Borsh fixes both lengths, so these
are defensive: `verify` is total on any byte list). -/
#guard verify [] [] [] == false
#guard verify (unhex MlDsaCrate.keys[0]!).toList ((unhex MlDsaCrate.sigs[0]!).toList.take 3308)
    (List.replicate 32 0) == false

end NearSpecV3.Examples.MlDsaVectors

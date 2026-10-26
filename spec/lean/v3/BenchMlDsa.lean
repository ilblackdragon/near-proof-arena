import NearSpecV3.Examples.MlDsaVectors

/-! `nearspec-v3-bench-mldsa`: wall time of `MlDsa65.verify` in compiled code over the 74 crate cases
(nearcore-shaped: 32-byte message, empty context), repeated `N` times (argument, default 10). Exits
non-zero on any disagreement with the recorded crate verdict. -/

open NearSpecV3.Examples.MlDsaVectors NearSpecV3.Examples NearSpecV3.MlDsa65

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 10
  let inputs := MlDsaCrate.cases.toList.map fun (_, key, msg, sigIdx, patch, expect) =>
    ((unhex MlDsaCrate.keys[key]!).toList, crateSig sigIdx patch, (unhex msg).toList, expect)
  let t0 ← IO.monoNanosNow
  let mut bad := 0
  for _ in [0:n] do
    for (pk, sig, msg, expect) in inputs do
      if verify pk sig msg != expect then bad := bad + 1
  let t1 ← IO.monoNanosNow
  let total := n * inputs.length
  IO.println s!"verifications {total} mismatches {bad} total_ms {(t1 - t0) / 1000000} per_verify_us {(t1 - t0) / 1000 / total}"
  return (if bad == 0 then 0 else 1)

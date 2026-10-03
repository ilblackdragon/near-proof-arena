# toy-arith-reference

Reference candidate for the DEMO challenge `demo-toy-arithmetic`
(`c = a*b mod 2^64`). Not NEAR, not cryptographic: the "proof" is the claim
plus a keyed FNV-1a checksum over the judge-run `prepare` output, so the
verifier rejects truncated, bit-flipped, extended, swapped or foreign proofs
but proves nothing beyond what it recomputes. Used by the arena e2e test.

# Outer commitment feasibility — 2026-10-24

**Five-limb hash component: 158,654 bytes, 2.13–2.17 s warm.** This misses the
2 s ceiling before adding NEAR execution or history composition. The parameter
screen is stronger than the previous three-limb experiment; it is still not a
composed PQ128 security claim. The investigation changes the next action from
simply integrating the fast component to resolving soundness and reducing work.

## What was screened

The [author's description](https://www.osdnk.me/blog/labinius) explicitly targets
100-bit security in its example benchmarks. We must not promote those numbers to
128-bit quantum security. Its explanation describes extraction by rewinding;
that is not itself a concrete QROM composition argument.

The implementation has several distinct commitments. Strengthening LaBRADOR's
internal reductions did not change the Rust bridge keys Y/u/R or the ring-648
main commitment. The existing bridge setup applies `168 * sqrt(cap)` and a
legacy rank rule. For the measured three-limb template, the scalar model yields:

| Bridge | Old rank | Direct 2× bound | Existing 168× factor |
|---|---:|---:|---:|
| Y | 11 | 193.98 bits | 95.93 bits |
| u | 4 | 466.40 bits | 120.31 bits |
| R | 9 | 225.25 bits | 101.495 bits |

These factors answer different questions. Neither column is automatically the
security of the recursive protocol. The port conservatively retains the existing
168× factor and selects ranks that pass the 128-bit scalar floor: for five limbs,
Y/u/R are 15/5/11, modeled at 131.44/164.30/134.885 bits. This is a sizing experiment,
not an independent proof that the factor suffices.

For the ring-648 commitment, the enforced fold norm cap is
`108 * 1024 * 648 * 1024`. Applying the upstream notebook's extraction factor
`8 * 12 * sqrt(3)` gives the following diagnostic scalar estimates:

| Moduli | Scalar modeled quantum bits |
|---|---:|
| 3889, 2917, 4861 | 79.235 |
| previous + 9721 | 125.61 |
| previous + 12637 | 176.49 |

We used the enforced cap, not the notebook's expected-norm sample output.
The notebook's saved classical/module-BKZ outputs are preserved explicitly as
**not rerun**. The generalized scalar model omits module/CRT attacks and
coefficient/canonical embedding effects; its high estimate does not certify a
structured composite-modulus ring. Four *different* larger supported primes may
also be worth testing, but the table is only the stated modulus sequence.

## Protocol and transcript obligations

The signed short challenge uses a weight-28 subset of 162 positions. Signs are
a deterministic public function of that subset; they add no independent entropy.
Thus one challenge's support is at most `C(162,28)`, about 2^103.997, before the
norm rejection filter. This is **not** the soundness of a vector of challenges or
a demonstrated forgery. The exact extraction error and quantum Fiat–Shamir loss
must be derived; neither increasing the modulus nor widening a hash output
establishes that result. The C backend's 16-byte transcript and the binary
frontend's field challenges are additional composition obligations.

## Implemented experiment

The five-limb template retains the same 3,088 slots / 7,296 SHA blocks, public
root, seed policy and original workloads. Bridge key selection now calls the
same scalar floor used by the isolated backend. C reduction bounds, prediction
headroom and canonical coefficient packing remain as in SIS_POLICY_EXPERIMENT.

The first five-limb proof was rejected by the integer no-wrap guard. All announced
norms were within their caps, but the worst static equation bound was
145,208,829,488,150.72, exceeding `(2^48−59)/2 = 140,737,488,355,298.5`.
The guard was **not removed**. The verifier now uses the tighter announced bounds
for nonbinary vectors: they are absorbed into the transcript and enforced by the
same rebuilt LaBRADOR statement using `max(norm,1)`. Binary vectors retain their
static caps because their statements enforce bitness, not the announced norm.
The fixed layout, support restrictions, cap checks and all integer no-wrap checks
remain. Statement construction does not read the changed layout caps, so prover
and verifier still reconstruct identical constraints. This reasoning requires
independent review before a production soundness claim; existing floating-point
bound evaluation also remains unaudited for strict numerical soundness.

The already-exported large packet and its regenerated counterpart are identical;
the acceptance change comes from using the bound actually enforced by the
statement, not modifying the witness or weakening the threshold.

Final measured readiness includes batch read, witness construction, proving and
serialization/write: **2.1657 / 2.1275 s** for large/small workloads. Cold circuit
and setup add **13.02 s**. Twelve wrong-root/tape/norm checks reject. Both packets
are 158,654 bytes (backend 109,488), substantially below 300,000. Backend-only
screen minimum is 144.69 bits; all 44 finite estimates match the independent C
excerpt. These remain two observations on one CPU core, not p95 or a GPU result.
Fresh-process verifier outcomes are pinned in the manifest and logs.

## Reproduction and next decision

[evidence/outer-security](evidence/outer-security) contains source, patches,
failed and successful runs, parameter screens and hashes. Apply the preceding
SIS-policy backend patch first, append the C policy export, then apply the Rust
outer-policy patch. Build `near-hash-template-five` against that isolated backend;
the decoder's fixed expected shape is now left=5 polx, right=11 polx, 36 norms.
It remains restricted to trusted local exports.

Next priority: derive protocol-specific extraction/transcript security and test
whether one shared authenticated event relation can absorb receipt/hash work
without duplicating the terminal proof. The present data does not justify a
full-NEAR timing estimate or claiming a PQ recursive tail has been achieved.

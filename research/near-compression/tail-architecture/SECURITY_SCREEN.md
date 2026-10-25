# Concrete security screen — 2026-10-24

The 165,950-byte / 1.67–1.73 s hash proof is a performance baseline, **not a
qualified PQ128 candidate**. All ten screened backend obligations pass the
legacy gate but fall below 128 bits in the selected scalar quantum cost model:
92.485–117.925 bits. This is diagnostic model evidence, not a demonstrated attack.

## Reproducible evidence

[sis_screen.py](sis_screen.py) parses the actual exported backend and applies the
measured verifier's legacy inner/outer collision bounds. The selected scalar
Euclidean SIS model is transcribed from
[greyhound-reference labrador.c](https://github.com/LayerZero-Labs/greyhound-reference/blob/672e74100496f6ef698ba35e241cf7593e3d57af/labrador.c).
Five regression checks pass. A directly extracted C implementation independently
matches all ten finite estimates, including BKZ block size and lattice dimension.
This crosscheck verifies transcription, not the model's cryptanalytic validity.

[Machine-readable results](evidence/security/backend-screen.json) pin the input
hash. Source excerpt and upstream license/notice are adjacent. Reproduce:

```sh
cc -O2 evidence/security/reference_model.c -lm -o /tmp/reference-sis-model
python3 sis_screen.py /path/to/00-h10035-s3.backend \
  --reference-model /tmp/reference-sis-model --output /tmp/backend-screen.json
```

Run from this document's directory. Input is the backend export documented in
[EXPORT_CODEC.md](EXPORT_CODEC.md). Ring degree 64; modulus 2^48−59. The legacy
rank gate uses log2(1.00444), without a width argument. The diagnostic model uses
actual scalar dimensions and quantum sieve cost 0.265 times BKZ block size.

## What this does not establish

- Legacy collision bounds themselves need justification. The reference fork
  uses revised inner bounds; replacing only its cost estimator is insufficient.
- Initial Dachshund commitment and outer LaBinius PCS are not included.
- Structured ring/module/CRT attacks, Fiat–Shamir/QROM losses and recursive
  composition are not covered by this scalar model.
- The backend uses 16-byte transcript state, SHAKE128 and AES128-CTR. Public PRG
  seeds do not justify a blanket secret-key-search attack claim. Their exact
  protocol roles and required quantum security must be analyzed.
- A hypothetical rank increase changes recursive witnesses, norms and schedules.
  Fixed-bound rank sensitivity cannot predict a corrected proof's size or time.

## Follow-up

The [policy experiment](SIS_POLICY_EXPERIMENT.md) regenerates proofs with revised
bounds, stronger rank selection and canonical serialization. Its backend model
checks pass; the whole-system security obligations above remain open.

## Decision at this screen

Do not integrate the measured backend as a security-qualified endpoint. Evaluate
parameter selection with justified collision bounds and a concrete security
policy first, then regenerate and benchmark real proofs. The independent
Greyhound reference fork supplies useful prior art for policies, codecs and
bounded parsing; it is not a reviewed drop-in replacement or a security certificate.
Its README marks old benchmarks as predating a later correctness change; do not
combine those old performance numbers with current security claims.

Maintain separate obligations for execution correctness, cross-component binding,
PCS binding, lattice compression, transcript soundness and recursive history.
None is discharged by another component's fast benchmark.

# The D3 pipeline, actually run: chunk → prepare → prove → verify

Lane `pq-prepare-link`.  Date 2026-10-23.  Base `8e4ac3616`.

This is the executable-path evidence for the "end to end" requirement: not a description of the
decomposition, but the shipped binaries driven on a real fixture, with exit codes.

## The run

Fixture: `oracle/fixtures/v3/public-d2/d2/00-h10003-s0` (a real D2 chunk from the public corpus).
Params: `oracle/fixtures/v3/public-chunk-v3/params.bin`.
Binaries: `examples/reexec-v3-d3/out/{prepare,prove,verify}`, the shipped artifacts whose soundness
`ReexecV3D3.ArtifactSound.artifact_sound_decoded` is proved against (`deployed_eq` by `rfl`).

```
$ ./out/prepare --params .../params.bin --out $T/pub
RC=0    # -> $T/pub/public.bin

$ ./out/prove --public $T/pub --request .../claim.bin --witness .../witness.bin \
              --claim-out $T/claim.out --proof-out $T/proof.out
RC=0    # -> claim.out 6419 B, proof.out 5438 B

$ ./out/verify --public $T/pub --claim $T/claim.out --proof $T/proof.out
RC=0    # accepted
```

All three stages run and the verifier accepts.  The proof is 5438 B for a 6419 B claim — this is the
witness-re-execution reference tier (`D3a`), which carries the recorded-store bytes rather than a
succinct proof, exactly as `examples/reexec-v3-d3/README.md` states.  "Toward the recursive step" is
honest here: this pipeline is per-chunk and does *not* aggregate.  The aggregation path is
`ZkFormal.PQ.Aggregation` (see below), which is a separate executable surface that this fixture run
does not exercise.

## What each stage's proof obligation is, and where it stands

| stage | obligation | artifact | class |
|---|---|---|---|
| chunk → prepare | prepared module for the executed code | `runCall_done_prepare_ok` | **[K]** |
| prepare → prove | logged checker equals frozen D3 checker | `Logged.API.checkD3Reads_eq` | **[K]** |
| prove → verify | acceptance implies `RelD3` | `ArtifactSound.artifact_sound_decoded` | **[K]** |
| verify → accept | acceptance implies literal normality | `ReadCanon.check_normal` | **[K]** |
| verify → accept | acceptance decomposes into `RelD3` ∧ canonicality | `ReadCanonSplit.check_iff` | **[K]** |
| toward recursion | tree run = flattened leaf run; certified root | `Aggregation.Tree.certified_root`, `d3Stmt_tree_sound` | **[K]** |
| toward recursion | per-node QROM extraction, error independence | not proved — `[O]`, named in the obligations log |

So every stage the pipeline actually runs has a kernel-checked obligation behind it.  The two
`[O]` rows are both on the *recursion* side, not on this run's path.

## Why this matters for the join question

The pipeline's acceptance predicate is `Read.check`, and `check_iff` proves it is
`RelD3 cb w ∧ encodeReads cb w (d3Reads cb w) = w`.  That is why the join must be stated on `check`
rather than on `compose_pv86`'s `hstate`: the former consumes canonicality that `RelD3` alone does
not supply, while the latter's premise collapses to its conclusion under `hagree`.

The run above is the executable counterpart: `verify` accepts only when the supplied proof bytes are
exactly the re-encoding of the logged read set.  That binding is testable on the shipped binary, and
it holds under mutation — 11 for 11 rejected (`[M]`, differential on the deployed artifact):

| mutation | result |
|---|---|
| proof byte flipped at offset 0, 100, 1000, 2719, 4000, 5437 (6 runs) | RC=1 each |
| proof truncated to 3000 B | RC=1 |
| claim byte flipped at offset 0, 500, 3000, 6418 (4 runs) | RC=1 each |
| s0's claim verified against s1's proof | RC=1 |

Together with the accepted baseline (RC=0), acceptance is *not* satisfied by arbitrary proof bytes:
the `==` on `encodeReads` is load-bearing, which is exactly the conjunct `check_iff` isolates and
`RelD3` lacks.  This is the differential evidence for the non-vacuity claim.

**What it still does not establish.**  These mutations reject, but none of them is *known* to satisfy
`RelD3` while failing canonicality — a byte flip destroys the relation too.  So "strictly stronger" is
still structural (a conjunct absent from `RelD3`'s statement) rather than separated by a witness that
satisfies one and not the other.  Finding such a witness needs a chunk whose logged read set does not
re-encode to its own witness bytes; that search is **[O]**.

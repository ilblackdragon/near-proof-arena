# v3 D3a reference (`examples/reexec-v3-d3`) — local results, challenge `near-chunk-v3` (unsigned draft)

Not signed, not registered, not run on the live judge. Draft `challenges/drafts/near-chunk-v3.draft.json`
(id `chl_c441fe20f35b22232e0bd757864402e5` while unsigned; `arena-admin check`: OK), declared tier D3a.

| item | value |
|---|---|
| freeze commit (trusted tree) | `8926b43179ec2bfd2fe75132107efd45945332df`, TreeDigest(spec/lean formal-core) `sha256:03fb64fd…` (`arena-admin freeze-trusted --expect` into a scratch store: OK) |
| package | `sha256:41fbd099…` (check-local), `out/verify` `sha256:f6cbb20f…`, `out/prove` `sha256:019cebb1…`, `out/prepare` `sha256:8341e9de…` (two builds identical) |
| certificate | `ReexecV3D3.certificate : ArenaExpectedInst.expectedType` against the local emulation of `ExpectedChunkV3.native-lean.lean.template` (declared tier `.d3a`); axioms `propext`, `Classical.choice`, `Quot.sound`; also `proveW_normal`, `check_proveW`, `check_normal`, `statementSound` (via `sound_lift`) |
| `arena check-local` (`check-local.txt`) | PKG_WELLFORMED, BUILD_REPRODUCIBLE, CONFORMANCE_DIFFERENTIAL, PROVER_RELIABILITY, ADVERSARIAL_PROOFS, RESOURCE_LIMITS PASS on `oracle/fixtures/v3/public-chunk-v3` (formal gates not run locally) |
| public set (`public-prove-verify.txt`) | 407/407 positives proved and accepted (78 d0, 75 d1, 82 d2, 172 d3, incl. 61 nearcore-accepted mutants), 0/244 rejections accepted; every accepted proof is canonical (`canonW p = p`, the escape never taken) |
| held-out set (`heldout-summary.txt`, ids withheld) | 208/208 positives proved and accepted, 0/64 rejections accepted |
| witness-freedom mutants (`freedom-mutants.txt`, helper `FreedomMutants.lean.txt`) | 4 916/4 916 rejected: values / entries / implicit reorder, duplicate, junk; `height_included`, signature, block hash; code reorder, duplicate, junk, empty; value ↔ code moves |
| hostile `near-v3-d3-lenient-codes` (`hostile-lenient-codes.txt`) | its verifier accepts 615 code-blob mutants of its own proofs (reorder 60, duplicate 125, junk 172, empty 172, code→value 114) — the reference rejects all of them |
| timings (one case, 6 parallel jobs, CPUs 8-15,24-31) | prove median 0.01–0.13 s per class, max 2.4 s; verify median 0.04–0.37 s, max 3.1 s; proof ≤ 182 KB |
| D3 public corpus (`d3-public-corpus-difftest.txt`) | fresh corpus seed 4402 (6 chains × 120 blocks, 3 at min gas price 1e8) with the fixed `c.no_resharding` classifier: 16 219 cases, Lean `checkD3` vs nearcore 0 disagreements |

The escape clause of the normal form, the residual freedom (reachable but unread values) and what
is proved vs tested: `examples/reexec-v3-d3/README.md`.

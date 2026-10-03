# reexec-witness: reference candidate (baseline)

This is the reference candidate for `near/pv86/receipt-transfer-batch/v0`,
backend family **re-execution witness**. The proof carries the authenticated
witness itself. The verifier decodes the claim and the proof and re-executes
the NEAR relation `NearSpec.TransferV1.NearRelation`: it hashes the trie paths,
applies the transfers, generates the refunds, computes the outcome root and
checks the commitments. It accepts only if the claim's outputs match.

## Layout

| path | what |
|---|---|
| `source/src/` | Rust prover (`prepare`, `prove`) and `rxcheck`, a Rust re-checker used for tests only |
| `source/vendor/` | vendored crates (`sha2` and its dependencies), built `--locked --offline` |
| `source/lean-vendor/` | verbatim copies of the judge-trusted Lean packages (`ArenaCore`, `NearSpec`'s trusted modules), used to compile `out/verify` offline. Refresh them with `source/verifier/sync-vendor.sh`; their digests are pinned in `dependency-locks/lean-vendor.sha256` |
| `source/verifier/` | dev Lake project (certificate against `judge-local/`), the judge's `main` wrapper template (verbatim), and `sync-vendor.sh` |
| `source/src/bin/leanorder.rs` | build helper: the judge's module link order (`topo` in runners/formal-checker) |
| `formal/ReexecWitness/` | Lean: proof codec, verifier model, obligations, certificate |
| `judge-local/` | **local emulation** of the judge-generated `ArenaExpected` / `ArenaExpectedInst` modules (native-lean route), for development only |
| `build-recipe/build.sh` | offline reproducible build of `out/{prepare,prove,verify}` |

## Proof format `reexec-witness-v1`

```
proof = u32 n ‖ Receipt × n      nearcore borsh, byte-identical to the request (= encodeReceipts)
        ‖ node                   partial pre-state trie
node  = 0 ‖ hash32 | 1 ‖ key ‖ u32 len ‖ value ‖ u64 mem | 2 ‖ key ‖ u32 len ‖ hash32 ‖ u64 mem
      | 3 ‖ key ‖ node ‖ u64 mem | 4 ‖ u16 bits ‖ node* ‖ u64 mem
      | 5 ‖ u32 len ‖ value ‖ u16 bits ‖ node* ‖ u64 mem | 6 ‖ u32 len ‖ hash32 ‖ u16 bits ‖ node* ‖ u64 mem
key   = u32 k ‖ nibbles packed two per byte
```

The normative definition is `formal/ReexecWitness/ProofCodec.lean`
(`encodeProof`). The prover reveals exactly the nodes that nearcore's
`TrieRecorder` recorded for the receivers' `Account` keys (the same partial trie
as `NearSpec.Codec.build`). The proof is at most
`4 + 347·n + revealedBytes + 33 ≤ 3 088 869` bytes; the public fixtures produce
0.6–67 KB.

## Verifier and implementation connection

The deployed verifier is the Lean function `ReexecWitness.Model.verifier`
(`formal/ReexecWitness/Model.lean`):

```lean
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => match decodeProof pb with
    | none => false
    | some w => decide (NearRelation c.1 w)
```

Route **`native-lean`** (`[entry] verify_route`): the **judge** compiles
`formal.verifier_model` with the governed Lean compiler and its own `main`
wrapper. `build.sh` replicates that build step for step: `lean -c` on every
trusted module in the judge's topological order and on the model's import
closure, the judge's `main` wrapper verbatim, `leanc -c -O3 -DNDEBUG` per C
file, and one `leanc -o` link in the same order. The result is that
`out/verify` is **byte-identical to the judge's build**: sha256 `3931ac6f…`
from both the real checker and `build.sh`. A judge that also compares the
shipped binary therefore passes `ARTIFACT_BINDING`. The
implementation-connection edge (binary ↔ model) is **trusted**, not checked:
the Lean compiler and runtime are in the TCB (`VerifierImpl.status =
.trusted`).

The Rust prover (`source/src/engine.rs`) is not in any trust path. It must emit
a claim equal to the oracle's and a proof the model accepts. `rxcheck` is an
independent Rust re-checker used only as a test oracle.

## Formal certificate

`ReexecWitness.certificate : ArenaExpectedInst.expectedType`, where the type is
`AdmissionStatement params { publicDigest, impl := .nativeTrusted binDigest
toolchainId ReexecWitness.Model.verifier }`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`. There is no `sorry`, `native_decide`,
`implemented_by`, `extern`, `partial` or `unsafe`.

| obligation | how it is discharged |
|---|---|
| (P) public digest | `public.bin` = approved `params.bin` verbatim (`ReexecWitness.publicBin`), `sha256` checked by `decide +kernel` |
| `FORMAL_IMPL_CONNECTION` | `rfl`: the model in the statement *is* `ReexecWitness.Model.verifier`; the edge is trusted (native-lean) |
| `FORMAL_SEMANTIC_SOUNDNESS` / `COMPLETENESS` | backend `Aux := Witness`, `B := Rel` |
| verifier completeness | `decodeProof (encodeProof w) = some w` for every witness of an in-domain true claim (`Roundtrip.lean`: mutual structural induction over `PTrie`/`Kids`, receipt codec), plus the size bound `Size.lean` (≤ 3 088 869 ≤ `maxProofBytes` = 8 MiB) |
| `FORMAL_CRYPTO_SOUNDNESS` | **`DeterministicSound`** (ε = 0, no assumption): acceptance ⇒ `decide (NearRelation c w) = true` for the decoded claim and witness |

Why no collision assumption is needed: `NearRelation` is stated over
`ArenaCore.sha256` *values*. "The trie hashes to `pre_state_root`" is literally
`w.trie.hashOf = c.preStateRoot`, and the commitments are equalities of hashes.
The verifier recomputes exactly those values from an explicit witness. Nothing
is opened against a commitment whose binding would need collision resistance,
so acceptance implies the relation itself. Collision resistance is what makes
the relation *meaningful* about the real chain state (spec §4). It is not a
soundness gap between the verifier and the relation.

`Obligations.lean` proves the statement for **every** profile, fuel and
reduction budget, and every `maxProofBytes ≥ 3 088 869`. Only the public digest
ties the certificate to the artifacts. The binary digest is universally
quantified because the edge is trusted.

## Real formal checker (runners/formal-checker, dev bwrap sandbox)

`formal-check --challenge challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json
--challenge-config runners/formal-checker/challenges/near-transfer-receipt-v1.json
--native-model ReexecWitness.Model.verifier@ReexecWitness.Model
--candidate-native-binary out/verify --certificate ReexecWitness.certificate`
on a clean export of `formal-core` and `spec/lean` gives:

`FORMAL_SEMANTIC_SOUNDNESS`, `FORMAL_SEMANTIC_COMPLETENESS`,
`FORMAL_CRYPTO_SOUNDNESS`, `FORMAL_IMPL_CONNECTION`, `AXIOM_AUDIT` and
`ARTIFACT_BINDING` are all **PASS**. The rechecks (leanchecker and nanoda) are
accepted. The judge-built verifier is `sha256:3931ac6f2c1eba795424c3a2b65cd84538f10dbf7e25376bff1380378270ac94`.
Because the result was produced with the dev sandbox, it is tier-capped at
`demo`.

## Measured locally

* Claims are byte-identical to the oracle on all 20 public fixtures and on 600
  freshly generated in-domain cases (seed 777). All 140 generated out-of-domain
  cases and all 14 rejection fixtures are refused.
* The Lean `verify` accepts every honest proof and rejects mutated proofs,
  mutated claims and swapped proofs.

## Limitations

* The implementation connection is **trusted** (native-lean: the Lean compiler
  and runtime are in the TCB). The checked route (a), with NPAI bytecode, is
  not achieved. `examples/npai-ir` has the proven-correct IR → NPAI compiler
  layer and a sizing of the remaining work.
* `judge-local/` is only an emulation of the judge's Expected modules for local
  `lake build`. The real checker renders its own
  (`spec/lean/judge/Expected.native-lean.lean.template`).
* The Lean verifier is slow: it uses `List UInt8` and a `Nat`-based SHA-256.
  It takes about 0.3 s on batch-256 workloads and 0.7 s for a 66 KB proof,
  against `max_verify_ms` = 10 s. A worst-case 3 MB witness has not been
  measured. Verify time is not scored.
* The proof is not succinct: it carries the full witness (the backend family is
  re-execution).

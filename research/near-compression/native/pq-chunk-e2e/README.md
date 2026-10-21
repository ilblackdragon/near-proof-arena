# D0a chunk recursion driver

This connects the **25-table D0a NEAR fixture AIR** to the SHA-384 recursive verifier.
It replaces the Fibonacci input used by the G2 experiment with the actual D0a
base proof and preserves both its public values and its cached TAPE commitment.
It does not implement the D3 state/Wasm join, prove a live mainnet chunk, establish
the research protocol's soundness, or add zero-knowledge witness masking.

## Reproduce

From this directory:

```sh
./setup.sh
./build.sh
./run.sh /data/illia/nearproof-deps/pq-chunk-e2e/runs/my-d0a-run
```

`NEARPROOF_PQ_DEPS` selects an isolated dependency/build directory. Setup applies
and checks the repository's pinned recursion and CPU backend patches. The driver
uses the checked-in Cargo lockfile. The scripts default to eight Rayon threads,
CPUs `8-15,24-31`, and the repository's heavy-work wrapper. Proving defaults to a
32 GiB memory budget. These are expensive CPU runs.

`run.sh OUT [CASE]` defaults to `oracle/fixtures/v3/public-d0a/d0/00-h10004-s3`.
Only chunk shapes fitting the selected BabyBear extended domain are supported;
larger shapes fail explicitly. It executes the witness, independently prepares public inputs from claim + hint,
checks that the preparations agree, proves and verifies the base proof, rebuilds
and checks its key from the AIR and public TAPE, runs
bound recursion, and invokes the final verifier in a separate process. Logs and
intermediate artifacts remain in OUT. A failed stage exits nonzero. The script
also exits nonzero if the verified packet is not strictly below **300,000 bytes**.

All recursion layers retain the first layer's ALU domain height, as required by
program binding. Tight-height compression handles unused common-main rows;
later layers use a smaller program capacity and the compact G2 WHIR profile. Recursion must converge under program binding
before a final artifact is accepted. The base uses the same compact WHIR
settings with a stacking width derived from the chunk trace shape. Cached TAPE
and program commitments always retain full heights. No final-verifier program check is skipped.
Saved verifying keys explicitly preserve the extended-domain factor omitted by
the upstream key serializer. The run tests rejection of a changed TAPE root and a changed pinned program.

## Packet and verification boundary

`FINAL.bundle` is eight magic/version bytes, an eight-byte little-endian hint
length, the complete hint, then the encoded final proof. `RESULT.json` reports
proof and total packet sizes separately. The external statement is `claim.bin`.
The verifier derives its public values and canonical TAPE commitment from that
claim and the transmitted hint, without reading witness traces or the base proof.

`SETUP.json` contains the final verifying key, program, level, base commitment
parameters, and AIR hash. **It is trusted, shape/run-specific setup, not part of
an untrusted proof packet.** Its hash must be provisioned independently by the
operator; accepting a hash supplied by the prover defeats the pin. This experiment
does not establish a single reusable setup for all chunk shapes. Setup size is
not counted toward the packet target. The run script's automatically generated
pin is only an integration test of a locally trusted proving run.

To verify with an already trusted pin:

```sh
D=/data/illia/nearproof-deps/pq-chunk-e2e
"$D/target/release/nearproof-chunk-e2e" verify \
  AIR.json claim.bin "$D/target-classical/release/examples/statepublic" \
  SETUP.json TRUSTED_SHA256 FINAL.bundle
```

The AIR and `statepublic` executable are trusted verifier inputs. A successful
verification reports `INDEPENDENT_VERIFY_OK`; this validates the implemented
research protocol and statement binding, not an independently established
cryptographic security or zero-knowledge theorem.

Each completed recursion level saves its proof, verifying key, and local circuit
state. To resume after level N, run the driver's `chain AIR PUBLIC OUT CERTS
EXCLUSIONS N` command with the same trusted inputs and profile. Checkpoints are
trusted prover state, not transferable verifier setup. A resumed proof is
reverified and its statement checked before proceeding.

## Profiling (enabled for every run)

Every `run.sh` stage saves `profiles/STAGE/`: CPU samples with DWARF call stacks
(`perf.data`, 19 Hz user-space cycles), hardware counters, five-second CPU/RSS/I/O
samples, timestamped phase events, executable identity, and a function hotspot report.
The executable is copied and cached by build ID so later rebuilds do not lose symbols. Raw stacks remain
available for later call-graph analysis. Perf uses noninteractive sudo if ordinary
access is restricted; it never changes global kernel settings. If neither access
path works, the profile metadata explicitly records the failure and resource
sampling continues. Short stages can finish before perf attaches. Profiles add
some overhead, so performance comparisons must use the same profiling settings.

For an existing run: `python3 profile.py attach PID NEW_PROFILE_DIRECTORY`.
An attached profile covers only the period after attachment, not earlier stages.

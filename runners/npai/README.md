# arena-npai — the judge-owned NPAI v1 interpreter

The interpreter route (`verify_route = "npai-v1"`, `ArtifactDescription.impl
= .interp bytecodeDigest`) works like this. The candidate ships verifier
**bytecode**. The judge runs that exact image on its own interpreter. The
candidate's Lean certificate is about `ArenaCore.Interp` on the image whose
SHA-256 is pinned in the admission statement. So the interpreter must match
the Lean definition exactly, and it is in the TCB.

| file | role | TCB? |
|---|---|---|
| `src/interp.rs` | decoder + executor, a transcription of `formal-core/ArenaCore/Interp.lean` (`decode`, `cost`, `exec1`, `step`, `runWith deployedRO`, `run`, `runOut`, `interpVerify`). ~600 lines including docs (~490 non-comment); `#![forbid(unsafe_code)]`; its only dependency is `sha2`; all `off + len` bounds use `u128` | **yes** |
| `src/bin/npai-verify.rs` | the `verify` entry point the worker runs for this route (file I/O + exit codes) | **yes** (thin) |
| `src/asm.rs`, `src/bin/npai-asm.rs` | assembler / disassembler / digest helper for backend authors | no |
| `src/lib.rs` (`report`) | hex + JSON in the exact format of `arena-interp-ref` | no (diagnostics only) |
| `src/bin/npai-difftest.rs` | differential tester against the Lean reference executable | no (evidence) |
| `src/bin/npai-bench.rs` | speed comparison against the Lean reference | no |
| `tests/vectors.rs` | the committed Lean vectors (`formal-core/vectors/npai-v1.json`), byte-for-byte, plus `npai-verify` exit codes | — |
| `fuzz/` | `cargo-fuzz` targets `decode` and `exec` (no panics; canonical re-encoding) | — |

The normative semantics is `formal-core/ArenaCore/Interp.lean`, restated in
`docs/INTERP_SPEC.md`. Where they disagree, Lean wins. The only domain
restriction is that `fuel` is a `u64` here, where Lean uses a `Nat`.
`--fuel` above `2^64-1` is a usage error and is never silently truncated.

## npai-verify

```
npai-verify --image <verifier.npai> --public <public.bin | public_dir>
            --claim <claim.bin> --proof <proof.bin> --fuel <N>
            [--expect-digest <64 hex>]
```

It computes `interpVerify image fuel pub claim proof`, which returns a
`Bool`, and maps the result onto CONTRACTS §4:

| exit | meaning |
|---|---|
| 0 | accept: `HALT` on a nonzero register |
| 1 | reject. This covers `HALT` on zero, **trap, out of fuel, undecodable image, and any tape of 2^32 bytes or more**. Lean `run`/`interpVerify` treats all of these as "not accepted". |
| 2 | usage or I/O error (no verdict, never acceptance) |
| 3 | `--expect-digest` mismatch (binding failure, no verdict) |

When `--public` is a directory, the public tape is `<dir>/public.bin`, which
is what `prepare` produces for this route. stdout gets one JSON line, for
example `{"route":"npai-v1","image_sha256":"…","outcome":"trap","fuel_used":17}`.
It is a diagnostic only; the exit code is the verdict.

Resource bounds hold for any image. Memory is at most 16 MiB plus the image
and the three tapes. `OUT` bytes are not retained in verify mode. Time is
linear in `fuel`, because bulk ops cost `1 + len/64`. A tape is never read
when the file is 2^32 bytes or more, and an image larger than the largest
decodable image (13 + 2^24 + 4 + 8·2^16 bytes) is not read.

### How the worker runs it

When the candidate's ArtifactDescription uses `.interp d`, the worker's
`run_verify` (`runners/worker/src/stages/common.rs`) keeps the same verify
sandbox and file layout. It swaps two things:

1. **Executable.** It runs the judge's `npai-verify`, a pinned binary from
   the worker image, mounted read-only. It never runs the candidate's
   `out/verify`.
2. **Arguments.**
   `--image @in/verifier.npai --public @in/public --claim @in/claim.bin --proof @in/proof.bin --fuel <ChallengeParams.verifyFuel> --expect-digest <hex d>`.
   `verifier.npai` is the file named by `[entry] verifier_bytecode`, taken
   from the judge's *reproducible build* output (`BUILD_REPRODUCIBLE`). The
   worker re-hashes it from the store like every other artifact.

The digest binding works in three steps:

* The judge generates `Judge/Expected.lean` with
  `impl := .interp [d₀, …, d₃₁]`, where `d = sha256(out/verifier.npai)` of
  that same build output (`npai-asm --digest` prints the Lean list form).
  The kernel then checks `sha256 code = d` for the `code` the certificate
  exhibits (`FORMAL_INTERFACE.md` §4a).
* `ARTIFACT_BINDING` compares `sha256(verifier.npai)` with `d` once.
* `npai-verify --expect-digest d` checks it again on every call, as
  defense in depth: exit 3 means the bytes being executed are not the bytes
  the certificate is about. Treat exit 3 as `ARTIFACT_BINDING_FAILED`/infra,
  never as reject. The exit-code mapping in `run_verify` (0 → Accept,
  1 → Reject, anything else → Error) already never turns it into an
  acceptance.

`fuel` must be the challenge's `verifyFuel`, the same number that appears in
`Judge.params`. A different fuel is a different verifier.

## npai-asm

```
npai-asm prog.s -o prog.npai      # prints sha256 (= bytecodeDigest)
npai-asm --disasm prog.npai       # exact decoder; re-assembles to the same bytes
npai-asm --digest prog.npai       # hex + Lean byte-list literal
```

```asm
.mem 64                ; memSize (default: data length)
.equ N 10              ; constant
.dlabel msg            ; msg := current data offset
.ascii "abc"           ; also: .data <hex>, .zero <n>
    const r1, N
loop:                  ; label = instruction index
    addi r1, r1, 0xffffffff
    ...
    sha256 r10, r8, r9 ; dst, src, len registers
    out 1, r10, r11    ; out k, addr, len
    halt r4            ; accept iff r4 != 0
```

The mnemonics follow `docs/INTERP_SPEC.md` §2: `halt const mov add sub mul
and or xor shl shr eq ltu addi jmp jz jnz tlen tload tcopy ld8 st8 sha256
rohash memeq out`. Tapes are `pub|claim|proof`. Immediates are `u32`
(decimal, `0x…`, a label or an `.equ` name).

## Differential testing

```sh
(cd formal-core && lake build arena-interp-ref)
cargo test -j 8 -p arena-npai                         # vectors + exit codes + asm
cargo build -j 8 --release -p arena-npai
./target/release/npai-difftest --ref formal-core/.lake/build/bin/arena-interp-ref \
    --cases 200000 --seed 42 --jobs 24 --shard-size 2000
./target/release/npai-bench --ref formal-core/.lake/build/bin/arena-interp-ref
cd runners/npai && cargo +nightly fuzz run decode -- -max_total_time=150 -fork=8
```

`npai-difftest` generates cases with a deterministic PRNG, so a seed
reproduces a run. It writes them in the `arena-interp-ref batch` line format
(`code,public,claim,proof,fuel` in hex). It runs the Lean reference on shards
in parallel and compares every result with the Rust result **as strings,
byte for byte**: outcome, `fuel_used`, `out0`, `out1`, or `decode_error`.
Any disagreement is written to `<work>/mismatch-<i>.txt` as a replayable
batch line. The case families are:

* **garbage**: random bytes, half of them with a valid `NPAI\x01` prefix.
* **raw-words**: valid header plus instruction words whose fields sit near
  the canonicality rules (unused fields 0/1/255, register 15/16, tape 2/3,
  unknown opcodes 0x0E/0x13/0x43/0x51/0xFF, …).
* **mutated**: a structured image with bit flips, truncation, trailing
  bytes, insertions, memSize at `2^24`/`2^24+1`/`u32::MAX`, `dataLen ± 1`,
  `codeLen ± 1`/`2^16`/`2^16+1`, and perturbed instruction fields.
* **structured**: a prologue loads "interesting" 64-bit values into
  registers. These are 0, 1, 63, 64, 65, `memSize±1`, `memSize−32`, tape
  length `±1`, `2^32−1`, `2^32`, `2^63`, `2^64−1`, `2^64−32`, `2^64−memSize+1`
  and random values, so `src+len` overflows 64 bits often. Then comes a
  random body with jumps that are in range, at `codeLen`, past it or random.
  Half the programs use forward-only jumps. "Bulk templates" put registers
  near the valid ranges before `TCOPY/SHA256/ROHASH/MEMEQ/OUT`. Tapes are
  random, and fuel ranges over 0–3, 0–63, 0–5000 and `2^64−1`. Fuel is
  capped at 20k for programs that do not halt.
* **structured-big**: memory of 64 KiB–1 MiB and 4 KiB tapes, so hashing
  and copies are large.
* **fuel-boundary**: for a third of the valid programs, the same case is
  re-run with fuel `used−1`, `used` and `used+1`.
* **fixed**: memSize = 2^24 with SHA256/ROHASH over 1 MiB and over
  `2^24−32` bytes; memSize `2^24+1`; codeLen = `2^16` (a jump chain through
  the whole program, both completing and running out of fuel) and
  `2^16+1`; 64 KiB `TCOPY` + `MEMEQ`.

### Results (2026-10-03, Lean v4.34.1, 32 cores)

| run | cases | disagreements |
|---|---|---|
| committed Lean vectors (`tests/vectors.rs`) | 45 | 0 |
| `npai-difftest --seed 42` (incl. the fixed max-size cases) | 200 001 | **0** |
| `npai-difftest --seed 2026 --no-fixed` | 1 000 000 | **0** |
| `cargo fuzz` `decode`, 150 s × 8 forks | ~300 M execs | 0 crashes |
| `cargo fuzz` `exec`, 150 s × 8 forks | ~30 M execs | 0 crashes |

Every outcome was covered. Seed 42: accept 33 351, reject 7 325,
trap 70 892, out_of_fuel 50 223, decode_error 38 210. Seed 2026: accept
166 301, reject 37 833, trap 354 308, out_of_fuel 250 151, decode_error
191 408. Wall time was 112 s and 4 min respectively on 28 worker
processes. Rust took 2.3 s and 13 s of that, including generation. The
seed-42 wall time is dominated by one 109 s shard, the one holding the 16 MiB
SHA-256 fixed cases.

**Generator sensitivity (mutation testing).** Each row is one deliberate
bug planted in `interp.rs`, followed by `npai-difftest --cases 10000
--seed 7`. Every one must be caught.

| planted bug | caught by |
|---|---|
| bounds `off+len <= lim` → `<` | 1 492 disagreements |
| bounds in wrapping `u64` instead of `u128` | panic (slice out of range) |
| TCOPY cost `len/64` → `len/65` | 280 |
| OUT cost always 1 | 1 648 |
| SHR `x >> (y mod 64)` → `0` for `y ≥ 64` | 166 |
| out-of-fuel when `fuel == cost > 1` | 395 |
| MEMEQ decoder accepts `d = 16` | panic (register 16) |
| ROHASH tag `NPAI-RO-v2` | 44 |
| JZ to target 0 falls through | 761 |
| decoder ignores trailing bytes | 62 |
| tape pre-check at 250 bytes instead of 2^32 | 1 971 |
| SHA256 dst bound `dst+31` | panic |
| SHA256 corrupts a digest byte iff `len = 64` | 9 |
| data segment loses its last byte | 1 221 |
| OUT drops writes at address 0 | 1 218 |

The first generator version missed 4 of these 15: SHR, MEMEQ `d = 16`,
JZ→0 and SHA256 at `len = 64`. Registers were rarely observable and
boundary operand encodings were rare. The register/memory dump epilogue
and the `alu`, `bulk` and near-canonical raw-word families were added to
close those gaps. The run is reproducible: plant the bug in
`src/interp.rs`, then `npai-difftest --cases 10000 --no-fixed --seed 7`.

## TCB status: TESTED, not CHECKED

`FORMAL_IMPL_CONNECTION` for the interpreter route has two parts:

1. *The certificate is about `Interp.interpVerify code fuel` with
   `sha256 code = d`.* This is **CHECKED** by the Lean kernel.
2. *`npai-verify` computes `Interp.interpVerify`.* This is **TESTED** only.
   The evidence is the vectors, about 1.2 million differential cases against the
   compiled Lean definition with 0 disagreements, the mutation-sensitivity
   table above, and fuzzing for robustness. It is not a proof. A bug outside
   what the generator reaches would sit in a trusted edge. The evidence
   graph should render this edge as `tested` (or `trusted` with this
   evidence attached), never as `checked`.

What would make edge 2 CHECKED, from cheapest to strongest:

* **Run the compiled Lean definition itself in production** (evaluated
  below). This removes the hand-written Rust. The edge then rests on the
  Lean compiler, runtime and code generator (`implemented_by`/`extern`
  overrides of `List`/`Nat`/`UInt8`) instead of on ~500 lines of Rust. That
  is a different trust assumption, not a proof: the kernel never checks
  compiled code.
* **Extract Rust to Lean and prove equivalence.** Aeneas (Rust → LLBC →
  Lean) or hax could translate `interp.rs` into a Lean model. One would
  then prove `extracted.run = Interp.runFull` for all inputs. `interp.rs`
  was written to make this tractable: no traits, no unsafe, no
  interior mutability, plain loops and slices. The trusted parts left are
  then the extractor and rustc/LLVM. The rustc part could be removed by
  running the extracted code in a verified-compilation setting.
* **Write a fast interpreter in Lean** using `ByteArray`/`Array`/`UInt64`
  instead of `List`/closures. Prove it equal to `Interp.exec` in Lean, then
  compile it. Speed would then be close to Rust, and the trusted part
  shrinks to "the Lean compiler compiles this proved-equivalent program
  correctly". This is the most practical way to retire the hand-written
  interpreter.

### Should the compiled Lean reference *be* the production interpreter?

`npai-bench` results (same machine, Lean process start-up subtracted,
outputs identical in every row):

| workload | fuel | Rust | Lean ref | Lean / Rust |
|---|---|---|---|---|
| ALU loop, 10k iterations | 30 004 | 70 µs | 2.33 s | 3.3·10^4 |
| ALU loop, 40k iterations | 120 004 | 278 µs | 31.6 s | 1.1·10^5 |
| SHA-256 chain, 1000 × 32 B | 3 006 | 46 µs | 94 ms | 2.0·10^3 |
| SHA-256 chain, 4000 × 32 B | 12 006 | 197 µs | 0.98 s | 5.0·10^3 |
| SHA-256 over 16 KiB | 520 | 7 µs | 0.18 s | 2.5·10^4 |
| SHA-256 over 64 KiB | 2 056 | 34 µs | 4.7 s | 1.4·10^5 |
| LD8/ST8 loop over 4 KiB | 24 647 | 30 µs | 1.47 s | 5.0·10^4 |
| LD8/ST8 loop over 16 KiB | 98 567 | 222 µs | 25.1 s | 1.1·10^5 |
| all 9 fixed difftest cases (incl. SHA256/ROHASH over 1 MiB and 16 MiB − 32 B, 2^16-instruction jump chain) | — | 46 ms | 88 s | ~2·10^3 |

Lean process start-up is about 9 ms. The Lean time is **super-linear**: 4×
the work costs 13–26× the time. Registers and memory are closure chains, so
a read of a value that was written long ago walks the whole chain, and code
fetch is `List` indexing. A verifier that runs 10^6–10^7 steps, which is
normal for hash-based proof verification, would take an hour or more in the
reference, extrapolating the measured quadratic trend. It takes milliseconds in Rust.

Recommendation: **keep the Rust interpreter as the production
interpreter. Use `arena-interp-ref` as a second, independent opinion on
small inputs, and invest in the "fast Lean interpreter + equivalence proof"
item above.**

* The reference is a *specification*, not an engine. Memory is a closure
  chain (`writeMem` adds a layer and every read walks the layers), code is a
  `List`, and SHA-256 runs on `List UInt8`. It is 10^3–10^5× slower than
  Rust, and the gap grows with memory traffic (see the table). One
  honest-sized verifier run (SHA-256 over a few MiB) takes minutes. That
  cannot meet `max_verify_ms`, and it would make the benchmark measure the
  reference rather than the candidate.
* Running it in production would move trust from about 500 reviewed lines of
  Rust to the Lean compiler, its C backend and runtime, plus `clang`. That
  base is larger, though better exercised. It is also not "checked": the
  kernel never sees the compiled code.
* A cheap hardening option needs no new code. In `ADVERSARIAL_PROOFS`
  and `CONFORMANCE_DIFFERENTIAL`, run each (image, tapes, fuel) on **both**
  `npai-verify` and `arena-interp-ref` whenever the tapes are small, for
  example ≤ 64 KiB with a step budget of ≤ 10^5. Fail the job with
  `INFRA_ERROR` on any disagreement. This turns every honest and hostile
  proof the arena sees into an additional differential test case, at no
  risk to timing.

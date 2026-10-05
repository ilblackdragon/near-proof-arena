# np-udr-stark: candidate package (skeleton)

The candidate package for the provable STARK backend `np-udr-stark-v1`
(`docs/zk-formal/DESIGN.md` §4 protocol, §7 verifier connection) on challenge
`chl_3be93793610370275ae40f36a475f01f` (near-transfer-receipt-v1-2,
`validity-classical-128`). It follows the two admitted references:
`examples/reexec-witness` for the native-lean verifier route, and
`examples/stark-plonky3` for the vendored Plonky3 Rust build.

## Status

| piece | state |
|---|---|
| `out/prepare` | done. Writes `public.bin` = approved `params.bin` verbatim (the reexec-witness convention; the AIR and the parameters are fixed by the Lean model). |
| `out/prove` | **stub.** It checks the CLI and inputs, then exits 2 with `not yet implemented: NEAR AIR pending (L6)`. The protocol engine in `source/src/` (lane L8) works on toy AIRs (`npudr` dev CLI). |
| `out/verify` | built from `formal/NpUdrStark/Model.lean`. That file is a **reject-all placeholder**, to be replaced by lanes L4/L7. |
| certificate | none. `NpUdrStark.certificate` is the planned name (lane L7). |

The judge cannot admit this package yet. The real formal checker reports
`CERTIFICATE_MISSING`.

## Layout

| path | what |
|---|---|
| `candidate.toml` | `verify_route = "native-lean"`. `[formal]` names `NpUdrStark.Model.verifier` in module `NpUdrStark.Model`. |
| `source/` | Rust crate (`npudr` library, the `npudr` dev CLI, and the judge bins `prepare`/`prove`). Plonky3 is pinned to rev `3acc8b7`. |
| `source/src/bin/leanorder.rs` | Build helper. It prints the judge's module orders: trusted modules in `topo` order, and the model closure in `stage_candidate` order filtered to the closure. It also enforces the import rule for model modules. |
| `source/vendor/` | **Not in git.** Every crate, written by `build-recipe/vendor.sh` (needs network). The digest is pinned in `dependency-locks/vendor-digest.txt`. |
| `source/lean-vendor/` | Judge-trusted Lean sources, verbatim at the pinned commit `4f5c19d` (`allowed_packages`): `formal-core/ArenaCore{,.lean}` plus the 9 trusted `NearSpec` modules. They exist only so that `build.sh` can replicate the judge build offline. Pinned in `dependency-locks/lean-vendor.sha256`, which is identical to reexec-witness's. |
| `source/verifier/` | The judge's `main` wrapper (`ARENACORE_MAIN_TEMPLATE`, verbatim) and `lean-toolchain`. |
| `formal/NpUdrStark/` | The verifier model and, later, the certificate (L4/L7). |
| `formal/ZkFormal{,.lean}` | **Not in git.** A copy of `zk-formal/` (lanes L1–L3) made by `build-recipe/sync-lean.sh`, pinned in `dependency-locks/zk-formal.sha256`. It is candidate code, not trusted code. The judge stages only `formal/`, and model modules may import only trusted modules, other `formal/` modules and `Init` (`native_build`). So ZkFormal must ship inside `formal/`: it cannot be a Lake `require`, and it cannot live in `lean-vendor`. |
| `build-recipe/build.sh` | The judge build (offline): `out/{prepare,prove,verify}`. |
| `build-recipe/vendor.sh`, `sync-lean.sh` | Packager steps. |

## Building

```sh
# packager, once (network; repo checkout):
bash build-recipe/vendor.sh        # source/vendor + dependency-locks/{Cargo.lock,vendor-digest.txt}
bash build-recipe/sync-lean.sh     # source/lean-vendor + formal/ZkFormal + their digests
# judge build (offline, fresh HOME; Rust 1.96.0 and Lean v4.34.1 via elan):
SOURCE_DATE_EPOCH=0 bash build-recipe/build.sh   # SKIP_LEAN=1: Rust only
```

`build.sh` writes the cargo source replacement (crates-io and the Plonky3 git
source go to `source/vendor`) into the fresh `$CARGO_HOME`, not into
`source/.cargo`. Development builds in `source/` therefore still resolve
normally. The Rust flags are those of stark-plonky3: `--remap-path-prefix`,
`-C strip=symbols`, and `x86-64-v3` + SHA/AES.

The Lean step compiles the trusted modules, then the model's import closure
(for example `ZkFormal.Params`, `NpUdrStark.Model`), then the wrapper, with
`lean -c` / `leanc -c -O3 -DNDEBUG` / one `leanc -o`. This is the same as
`native_build`. The model can be overridden with `MODEL_MODULE`/`MODEL_DECL`.
By default both are read from `candidate.toml`.

## Verified (2026-10-03, placeholder model)

Three clean builds from two different paths with fresh `HOME`s, one of them
under `unshare -rn` (no network), give bit-identical outputs:

```
6ba6ebb62c8e65b4ef1ac0c6bb70362b44fd75a610febe9aa8b4a92d33af4db4  out/prepare
d5b01fc8eed52b7a093b66343839789e7c8a25bb1866fcc0a6da0388a85c8c36  out/prove
c0849794f12253759d7bcd2fc6ba718db57bc0beba621ce48bc85ceeb123a71a  out/verify
```

The real `formal-check --native-model NpUdrStark.Model.verifier@NpUdrStark.Model`
(dev bwrap sandbox) built the same verifier: `sha256:c0849794…`. These hashes
change whenever `source/src`, the model, or ZkFormal changes.

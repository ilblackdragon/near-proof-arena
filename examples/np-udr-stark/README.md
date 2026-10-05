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
| `out/prepare` | done. Writes `public.bin` = approved `params.bin` verbatim (= `NpUdrStark.publicBin`). |
| `out/prove` | **stub** (exits 2). The NEAR prove path is lane L8's: AIR export + witness→trace (`REQUESTS.md` R-L7-7). |
| `out/verify` | the judge's native-lean build of `NpUdrStark.Model.verifier` = claim guard ∘ `ZkFormal.Stark.verifier Fp Fp8 nearAir default` (`model_eq : … = NearAssembly.nearModel nearAir`, `rfl`). |
| certificate | `NpUdrStark.certificate_of` (`formal/NpUdrStark/Assembly.lean`, axioms propext/Classical.choice/Quot.sound) proves the judge's statement for every validity-classical-128 literal from L6's `RenderStmt` and `NearMinHeightStmt` (R-L7-6). Once those land, `NpUdrStark.certificate` is `certificate_of <render> <minHeight> _ … rfl (by decide) (by decide) (by decide +kernel)`. |
| challenge | the unsigned draft `near-transfer-receipt-v1-zk` (`chl_bdbfc808…`; ArenaCore/NearSpec @ `e4088761`, i.e. formal-core with `sha256Fast`). The id changes when it is signed with the new checker identity. |

## Layout

| path | what |
|---|---|
| `candidate.toml` | `verify_route = "native-lean"`. `[formal]` names `NpUdrStark.Model.verifier` in module `NpUdrStark.Model`. |
| `source/` | Rust crate (`npudr` library, the `npudr` dev CLI, and the judge bins `prepare`/`prove`). Plonky3 is pinned to rev `3acc8b7`. |
| `source/src/bin/leanorder.rs` | Build helper. It prints the judge's module orders: trusted modules in `topo` order, and the model closure in `stage_candidate` order filtered to the closure. It also enforces the import rule for model modules. |
| `source/vendor/` | **Not in git.** Every crate, written by `build-recipe/vendor.sh` (needs network). The digest is pinned in `dependency-locks/vendor-digest.txt`. |
| `source/lean-vendor/` | Judge-trusted Lean sources, verbatim at the pinned commit `e4088761` (the v1-zk challenge's `allowed_packages`): `formal-core/ArenaCore{,.lean}` (including `SHA256Fast`) plus the 9 trusted `NearSpec` modules. They exist only so that `build.sh` can replicate the judge build offline. Pinned in `dependency-locks/lean-vendor.sha256`. |
| `source/verifier/` | The judge's `main` wrapper (`ARENACORE_MAIN_TEMPLATE`, verbatim) and `lean-toolchain`. |
| `formal/NpUdrStark/` | The verifier model and, later, the certificate (L4/L7). |
| `formal/ZkFormal{,.lean}` | **Not in git.** The import closure of `formal/NpUdrStark/*.lean` within `zk-formal/` (369 modules), copied by `build-recipe/sync-lean.sh`, pinned in `dependency-locks/zk-formal.sha256`. It is candidate code, not trusted code. The judge stages only `formal/`, and model modules may import only trusted modules, other `formal/` modules and `Init` (`native_build`). So ZkFormal must ship inside `formal/`: it cannot be a Lake `require`, and it cannot live in `lean-vendor`. |
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

## Verified (2026-10-05, real model `nearModel nearAir`)

Two clean builds (fresh `HOME`, `env -i`, `SOURCE_DATE_EPOCH=0`) from separate copies give bit-identical outputs:

```
eefd2add15097d15bd485e2098bbe3a2006bea3acae5276435fa105f0cb2ae3f  out/prepare
9dad00e9e8eb40db8baf335e13edb30a8df488771ea101d3bc3626ef414b7312  out/prove   (stub)
c82117cb46db768c5eb158bcdf6e30508e8aadc2590510464ff3a40280e22472  out/verify
```

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

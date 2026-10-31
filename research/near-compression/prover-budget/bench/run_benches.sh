#!/bin/bash
# CPU microbenchmarks for the prover-budget model (single core, pinned). Results: RESULTS.md.
# Usage: P3=/data/illia/nearproof-deps/Plonky3 OUT=/some/target/dir bash run_benches.sh
# Needs: cargo (offline registry), openssl, taskset. Takes ~25 minutes.
set -u
P3=${P3:-/data/illia/nearproof-deps/Plonky3}
OUT=${OUT:-$PWD/p3target}
CPU=${CPU:-8}
export CARGO_TARGET_DIR="$OUT" RUSTFLAGS="-C target-cpu=native" RAYON_NUM_THREADS=1

echo "== host"; uptime; lscpu | grep -E "Model name"
echo "== Plonky3 $(git -C "$P3" rev-parse HEAD)"
(cd "$P3" && cargo bench --offline -p p3-poseidon2 -p p3-dft -p p3-binary-field -p p3-whir --no-run) >/dev/null 2>&1

bench() {  # crate-dir bench-name filter...
  local dir=$1 name=$2; shift 2
  local exe
  exe=$(ls -t "$OUT"/release/deps/"$name"-* | grep -v '\.d$' | head -1)
  (cd "$P3/$dir" && taskset -c "$CPU" "$exe" --bench --warm-up-time 1 --measurement-time 3 "$@" 2>&1 | grep -E "^[a-z_]+.*/|time:|proof size")
}

echo "== SHA-2/SHA-3 (openssl, 3 s each)"
for h in sha512 sha256 sha3-256; do taskset -c "$CPU" openssl speed -seconds 3 -evp "$h" 2>&1 | tail -1; done

echo "== Poseidon2 permutations (AVX-512 packed)"
bench poseidon2 poseidon2

echo "== DFT (256 columns)"
bench dft fft 'fft/MontyField31<BabyBearParameters>/Radix2Dit<MontyField31<BabyBearParameters>>/ncols=256/65536'
bench dft fft 'fft/MontyField31<BabyBearParameters>/Radix2Dit<MontyField31<BabyBearParameters>>/ncols=256/1048576'
bench dft fft 'fft/Goldilocks/Radix2Dit<Goldilocks>/ncols=256/1048576'
bench dft fft 'coset_lde/MontyField31<BabyBearParameters>/Radix2Dit<MontyField31<BabyBearParameters>>/ncols=256/1048576'

echo "== binary-field multiplication throughput (1000 mults per iteration)"
bench binary-field arithmetic throughput

echo "== HVZK-WHIR vs plain WHIR (eprint 2026/391)"
bench whir zk_overhead

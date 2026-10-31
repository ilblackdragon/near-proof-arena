#!/usr/bin/env python3
"""Prover-budget feasibility model: a 128-bit PQ, zero-knowledge proof of NEAR chunk validation
(up to 1 Pgas) within 3 s of the last receipt on <= 8 H200 GPUs, verify < 200 ms, proof <= 300,000 B.

Research model only (no checker/spec change). Companion: README.md (verdict + cost models), WORKLOAD.md,
HARDWARE.md, bench/ (CPU microbenchmarks run on this host).

Every parameter carries a provenance label:
  M   measured on this host for this study (bench/RESULTS.md)
  MR  measured earlier in this repo (file cited)
  C   cited publication / vendor figure (URL + date in HARDWARE.md)
  D   derived by arithmetic from other entries (formula in the note)
  A   ASSUMPTION (owner can vary; listed in the sensitivity table)

Builds on docs/zk-formal/V3-PERF-DESIGN.md (tools/perf-design/model.py): its measured chip
layouts are copied below with their labels, and `--prior` re-runs that design at 8 GPUs.

Usage:
  python3 model.py              full report
  python3 model.py --json       machine-readable results
  python3 model.py --set eff=0.5 --set zk_bytes=15000   override any parameter
  python3 model.py --prior      also evaluate the V3-PERF-DESIGN shared-transcript design at 8 GPUs
"""
import json
import math
import sys
from copy import deepcopy

# =============================================================================================
# 1. PARAMETERS (the one table). name: (value, label, note)
# =============================================================================================
P = {
    # ---- target ---------------------------------------------------------------------------
    "gas": (1e15, "spec", "chunk gas (1 Pgas = PV86 max_gas_burnt and mainnet chunk gas limit)"),
    "n_gpu": (8, "owner", "H200 SXM GPUs, one HGX node"),
    "budget_s": (3.0, "owner", "proof ready <= budget after the chunk's last receipt is applied"),
    "verify_budget_s": (0.200, "owner", "verifier wall time on a CPU"),
    "size_cap": (300_000, "owner", "proof bytes"),
    # ---- execution / streaming --------------------------------------------------------------
    "exec_s_per_pgas": (1.0, "A", "native execution 1 Tgas ~ 1 ms (NEAR gas calibration target)"),
    "exec_slowdown": (1.2, "A", "native run with checkpoint/trace recording (V3-PERF-DESIGN P)"),
    "stream_util": (0.9, "A", "fraction of GPU time usable for segment proving while execution runs"),
    "sync_s": (0.03, "A", "per tree level: transcript/root exchange, kernel launch, PCIe/NVLink hop"),
    "seg_log_rows": (22, "A", "rows per segment proof (2^k); the last segment is on the critical path"),
    "fan_in": (8, "A", "children per aggregation node"),
    "pre_wrap": (0, "design", "1 = insert a 1-child compression layer at lb_node before the wrap"),
    "seg_width": (160, "A", "committed cells per trace row of a segment (sets segment count)"),
    "row_width": (40, "A", "main cells per chip row (for per-row aux/quotient columns, arch a)"),
    # ---- workload (PV86 gas from nearcore snapshot ..._85.json.snap; see WORKLOAD.md) ---------
    "regular_op": (822_756, "spec", "wasm regular_op_cost (PV86)"),
    "code_bytes": (64 * 2**20, "spec/MR", "distinct cold code per chunk <= 64 MiB contract-code response (size-limit fixtures)"),
    "witness_bytes": (64 * 2**20, "spec", "decoded state witness <= 64 MiB (48 MiB encoded); hashed + parsed in-circuit"),
    "witness_scales": (1, "A", "below 1 Pgas the adversarial witness scales with gas (floor 4 MiB = storage-proof soft limit)"),
    "witness_parse_m": (16, "A", "main cells per witness byte for borsh/trie-node parsing (PREP decoder class)"),
    "witness_parse_f": (3, "A", "bus fractions per witness byte"),
    "wasm_share_real": (0.034, "MR", "WASM-operator share of function-call gas, corpora (V3-PERF-DESIGN P)"),
    "real_gas": (18.45e12, "M", "shard-13 mainnet p99 chunk gas, 1,223 chunks (bench/RESULTS.md; max 115 Tgas)"),
    # ---- field / IOP ----------------------------------------------------------------------
    "E_a": (10, "D", "extension degree, arch (a): |K| >= 2^290 for 260-bit rbr rounds (V3-D3A-STUDY 11.2)"),
    "E_b": (8, "MR", "extension degree, arch (b): the main PQ stack runs BabyBear^8 (Ext8 layouts)"),
    "d_quot": (2, "D", "quotient chunks at constraint degree 3 (arch a)"),
    "constraints_per_cell": (0.7, "MR/A", "constraint terms per committed cell (V3-PERF-DESIGN)"),
    "rbr_bits": (260, "D", "per-round PQ target for proven bounds (t^2 eps loss, t = 2^64; V3-D3A-STUDY 11.2)"),
    "z_grind": (32, "U-10", "grinding bits per query phase (Grover: buys z/2)"),
    "proven": (1, "U-6", "1 = Johnson-regime proven bits/query (0.5 lb - 0.1); 0 = capacity conjecture (lb)"),
    "lb_base": (1, "design", "base segment rate 2^-lb (rate 1/2)"),
    "lb_node": (4, "design", "aggregation-node rate 2^-lb (rate 1/16); main stack nodes run lb 6"),
    "lb_wrap": (6, "MR", "final ZK wrap rate (main stack final layer lb 6, 143 queries)"),
    "whir_q_anchor": (143, "MR", "WHIR queries of a production node at lb 6 (pq-agg depth law, [46,41,31,25])"),
    "whir_comps_anchor": (4956, "MR", "in-circuit SHA-384 compressions to verify one such child (9,911 per 2-child node, L3_0)"),
    "pcs_a": ("whir", "design", "arch (a) PCS: 'whir' (univariate WHIR) or 'fri'"),
    "fri_factor": (2.0, "D", "FRI/WHIR ratio of verifier hashing and proof bytes (V3-D3A-STUDY 11.4: 0.71-0.88 MB vs 0.3-0.5 MB)"),
    "path_share": (0.6, "A", "share of wrap proof bytes that are Merkle digests (for the Poseidon2 alternative)"),
    # ---- GPU (H200 SXM; HARDWARE.md) --------------------------------------------------------
    "sm": (132, "C", "H200 SXM SMs (GH100, same die config as H100 SXM)"),
    "clk_ghz": (1.98, "C", "boost clock GHz"),
    "int32_per_sm_clk": (64, "C", "CUDA C++ Programming Guide throughput table, cc 9.0: 32-bit IMAD/IADD/LOP3 = 64/clk/SM"),
    "hbm_gb": (141, "C", "HBM3e capacity per GPU"),
    "hbm_tbs": (4.8, "C", "HBM bandwidth TB/s"),
    "nvlink_gbs": (450, "C", "NVLink 4 per direction GB/s (900 GB/s bidirectional)"),
    "eff": (0.35, "A", "sustained fraction of INT32 peak over all prover kernels (V3-PERF-DESIGN baseline)"),
    "sha512_ops": (3127, "D/C", "INT32 ops per SHA-512 compression = peak / hashcat H100 SHA2-512 5.35 GH/s"),
    "sha256_ops": (1045, "D/C", "INT32 ops per SHA-256 compression = peak / hashcat H100 SHA2-256 16.0 GH/s"),
    "p2_ops": (5800, "D", "INT32 ops per Poseidon2-BabyBear-16 permutation (772 Montgomery muls x6 + 1,184 adds)"),
    "hash": ("sha384", "U-7", "'sha384' (decided, U-7); 'poseidon2' or 'hybrid' (SHA-384 base, Poseidon2 recursion) need an owner decision"),
    "mont_ops": (6, "D", "INT32 ops per 31-bit Montgomery multiplication (IMAD lo/hi, m, m*p hi, sub, select)"),
    "bfly_ops": (10, "D", "INT32 ops per radix-2 NTT butterfly (1 Montgomery mul + add/sub with reduction)"),
    "gf128_ops": (300, "A", "INT32 ops per GF(2^128) multiplication on GPU (no carry-less multiply; tower over GF(2^16) tables). CPU: reference/CLMUL = 94x (M)"),
    "bin_and_gf128": (29, "D/M", "GF(2^128)-mult equivalents per AND constraint in the Binius64 PIOP: 0.53 us/AND (MR, LaBinius stages) / 18.2 ns per GF(2^128) mul (M)"),
    "bin_words_per_and": (1.79, "MR", "committed 64-bit words per AND constraint (Wasm ladder 5.35M words / 2.99M AND)"),
    "bin_ntt_ops_word": (200, "A", "additive-NTT INT32 ops per committed 64-bit word at rate 1/2 (bitsliced GF(2^8) stages)"),
    "bin_wasm_and": (1452, "MR", "AND constraints per Wasm step (NPMWASM02 slice, WASM_LADDER.md)"),
    "bin_wasm_worst": (1.5, "A", "worst-op factor over the slice mean (i64 mul/div via MUL constraints; div not in slice)"),
    "bin_mul_and": (8, "A", "AND-equivalents per Binius64 64x64 MUL constraint"),
    "bin_sha512_and": (900, "D", "AND constraints per SHA-512 compression (1 per 64-bit add, Ch, Maj; 80 rounds + schedule)"),
    # ---- recursion circuits ---------------------------------------------------------------
    "rec_cells_per_comp": (29_049, "MR", "node committed cells per in-circuit SHA-384 compression (L2_0: 254,084,224 / 8,747)"),
    "rec_fracs_per_comp": (9_958, "MR", "node interactions per compression (L2_0: 87,097,600 / 8,747)"),
    "p2_perms_per_comp": (1.75, "A", "Poseidon2 permutations replacing one SHA-384 compression in a verifier (path node = 1, 128-B leaf = 4)"),
    "p2_rec_cells": (600, "A", "committed cells per in-circuit Poseidon2-16 permutation (Plonky3 poseidon2-air class)"),
    "rec_field_overhead": (0.10, "A", "in-circuit field/sumcheck/DEEP work on top of hashing in a verifier circuit"),
    # ---- final ZK wrap ----------------------------------------------------------------------
    "wrap_bytes": (299_967, "MR", "non-ZK final layer verifying one 2^20 child (D0a packet, opt-baseline-8)"),
    "zk_bytes": (92_900, "D/M", "ZK additive bytes: HVZK-WHIR +72.6 KB at 100-bit (M, Plonky3 zk_overhead) x 128/100"),
    "zk_time_factor": (1.5, "M", "HVZK-WHIR / plain prover time 1.28-1.72x (M, 2^16-2^18)"),
    "wrap_gpus": (8, "A", "GPUs that share the final wrap (NVLink within the node)"),
    "wrap_split_eff": (0.6, "A", "parallel efficiency of splitting one proof across wrap_gpus"),
    # ---- verifier (CPU) -------------------------------------------------------------------
    "cpu_sha512_ns": (134, "M", "SHA-512 compression on one Zen 5 core (openssl 953 MB/s)"),
    "cpu_ext_mul_ns": (7.9, "MR", "Plonky3 BabyBear^8 multiplication (V3-PERF-DESIGN clean.log)"),
    "verify_ext_mults": (3e5, "A", "extension multiplications in the wrap verifier (OOD constraint eval, sumcheck, WHIR folds)"),
    "verify_impl_s": (1.46, "MR", "measured verify of the 299,967 B packet, 32 threads (7.65 s on 1 core)"),
}


def v(p, k):
    return p[k][0]


# =============================================================================================
# 2. MEASURED CHIP LAYOUTS (copied from tools/perf-design/model.py; labels kept)
#    (main cells per row, bus fractions per row)
# =============================================================================================
CHIP = {
    "ld_gen": (32, 19, "M spike4: unaligned i32.load (worst WASM op per gas)"),
    "st_gen": (37, 24, "M spike4"),
    "mul_TTL": (44, 29, "D from M mul[TLL]"),
    "divrem": (60, 37, "D from M divu"),
    "callret": (30, 12, "M spike4"),
    "memcpy16": (39, 27, "M spike4: 16 B per row"),
}
SHA384_ROWS = [(449, 3, 41), (98, 8, 80), (98, 1, 1)]   # M: one 128-B SHA-512-family block
SHA256_ROWS = [(225, 3, 33), (50, 8, 64), (50, 1, 1)]   # M: one 64-B block
PREP_PER_BYTE = (16 + 50 * 0.5 + 20 * 0.2, 3 + 14 * 0.5 + 2 * 0.2)   # D: decoder + validator/translator + code rows
KECCAK_CELLS = 2633 * 24     # C: Plonky3 keccak-air NUM_KECCAK_COLS x 24 rounds (63,192 cells/perm)
RIPEMD_CELLS = 1608 * 80     # MR: RIPEMD row AIR 128,640 cells/block (HANDOVER)


def rows_mf(rows):
    return (sum(m * n for m, f, n in rows), sum(f * n for m, f, n in rows))


SHA256_MF = rows_mf(SHA256_ROWS)   # (10,675 main, 612 fractions)
SHA384_MF = rows_mf(SHA384_ROWS)   # (26,347 main, 764 fractions)


def nn_mul(bits):
    """Non-native field multiplication chip sketch (31-bit AIR, 16-bit limbs): a,b,c,q limbs +
    2L carries; range lookups on c, q and carries + 3 wiring fractions. Constraint degree 2."""
    L = math.ceil(bits / 16)
    return (6 * L, 4 * L + 3)


def bin_nn_mul(p, bits):
    """Binius64: 64-bit limbs, schoolbook + quotient product via MUL constraints, carries via AND."""
    L = math.ceil(bits / 64)
    return 2 * L * L * v(p, "bin_mul_and") + 4 * L * L


# =============================================================================================
# 3. HOST / WORKLOAD TABLE (PV86 gas). unit cost: (main cells, fractions) and binary AND-eq.
#    gas_per_unit is the cheapest legal way to buy one unit (long inputs amortise the base fee).
# =============================================================================================
def host_table(p):
    ro = v(p, "regular_op")
    fp256, fp381 = nn_mul(256), nn_mul(381)
    b256, b381 = bin_nn_mul(p, 256), bin_nn_mul(p, 381)
    keccak_bin = 24 * 25 + 24          # chi: 25 AND per round + iota/control
    sha256_bin = 600                   # D: 1 AND per 32-bit add/Ch/Maj, 64 rounds + schedule
    T = []

    def add(name, gas, mf, and_eq, n_mults=None, max_units=None, src=""):
        T.append({"name": name, "gas": gas, "m": mf[0], "f": mf[1], "and": and_eq,
                  "max_units": max_units, "src": src})

    def k(mf, n):
        return (mf[0] * n, mf[1] * n)

    add("wasm op: unaligned i32.load chain", ro, CHIP["ld_gen"][:2], v(p, "bin_wasm_and") * v(p, "bin_wasm_worst"), src="M spike4 / MR slice")
    add("wasm op: i64.div_u chain (2 ops/row)", ro, (CHIP["divrem"][0] / 2, CHIP["divrem"][1] / 2), v(p, "bin_wasm_and") * v(p, "bin_wasm_worst"), src="D from M")
    add("wasm op: i64.mul chain (2 ops/row)", ro, (CHIP["mul_TTL"][0] / 2, CHIP["mul_TTL"][1] / 2), v(p, "bin_wasm_and") * v(p, "bin_wasm_worst"), src="D from M")
    add("wasm op: call of empty function", ro, CHIP["callret"][:2], v(p, "bin_wasm_and"), src="M spike4")
    add("memory.copy byte (linear op unit)", ro, (CHIP["memcpy16"][0] / 16, CHIP["memcpy16"][1] / 16), 4, src="M bulk16")
    add("read_register->memory byte", 98_562 + 2_723_772, (CHIP["memcpy16"][0] / 16, CHIP["memcpy16"][1] / 16), 4, src="M bulk16")
    add("sha256 block (64 B)", 64 * 24_117_351, SHA256_MF, sha256_bin, src="M L5 layout")
    add("keccak256 block (136 B)", 136 * 21_471_105, (KECCAK_CELLS, 0), keccak_bin, src="C Plonky3 keccak-air")
    add("keccak512 block (72 B)", 72 * 36_649_701, (KECCAK_CELLS, 0), keccak_bin, src="C Plonky3 keccak-air")
    add("ripemd160 block (64 B), measured AIR", 680_107_584, (RIPEMD_CELLS, 160), 960, src="MR row AIR (unoptimised)")
    add("ed25519_verify (5,800 Fp255 mul + SHA-512)", 210e9 + 64 * 9e6, (5800 * fp256[0] + 2 * SHA384_MF[0], 5800 * fp256[1] + 2 * SHA384_MF[1]), 5800 * b256 + 2 * v(p, "bin_sha512_and"), src="D sketch")
    add("ecrecover (6,500 Fp256 mul)", 278_821_988_457, k(fp256, 6500), 6500 * b256, src="D sketch")
    add("p256_verify (6,500 Fp256 mul)", 1.3e12 + 32 * 13e6, k(fp256, 6500), 6500 * b256, src="D sketch")
    add("alt_bn128 g1_multiexp element (3,175 mul)", 320e9, k(fp256, 3175), 3175 * b256, src="D sketch")
    add("alt_bn128 pairing element (10,000 mul)", 5.102e12, k(fp256, 10000), 10000 * b256, src="D sketch")
    add("alt_bn128 g1_sum element (11 mul)", 5e9, k(fp256, 11), 11 * b256, src="D sketch")
    add("bls12381 p1_sum element (12 mul)", 6e9, k(fp381, 12), 12 * b381, src="D sketch")
    add("bls12381 p2_sum element (36 mul)", 15e9, k(fp381, 36), 36 * b381, src="D sketch")
    add("bls12381 g1_multiexp element (3,100 mul)", 930e9, k(fp381, 3100), 3100 * b381, src="D sketch")
    add("bls12381 g2_multiexp element (9,300 mul)", 1.995e12, k(fp381, 9300), 9300 * b381, src="D sketch")
    add("bls12381 map_fp_to_g1 element (1,700 mul)", 252e9, k(fp381, 1700), 1700 * b381, src="D sketch")
    add("bls12381 map_fp2_to_g2 element (16,000 mul)", 900e9, k(fp381, 16000), 16000 * b381, src="D sketch")
    add("bls12381 pairing element (5,000 mul)", 2.13e12, k(fp381, 5000), 5000 * b381, src="D sketch")
    add("bls12381 p1_decompress element (600 mul)", 81e9, k(fp381, 600), 600 * b381, src="D sketch")
    add("bls12381 p2_decompress element (2,000 mul)", 165e9, k(fp381, 2000), 2000 * b381, src="D sketch")
    # trie: per touched node (2.28 Ggas), old node (<= 9 SHA-256 blocks) verified + new node hashed
    add("storage_write: touched trie node (18 blocks)", 2.28e9, k(SHA256_MF, 18), 18 * sha256_bin, src="D (PV86 touching_trie_node)")
    add("storage_read: touched trie node (9 blocks)", 2.28e9, k(SHA256_MF, 9), 9 * sha256_bin, src="D")
    add("storage_write value byte (hashed)", 31_018_539, (SHA256_MF[0] / 64, SHA256_MF[1] / 64), sha256_bin / 64, src="D")
    add("log byte (hashed into outcome)", 13_198_791, (SHA256_MF[0] / 64, SHA256_MF[1] / 64), sha256_bin / 64, src="D")
    # ML-DSA-65 verify (tx/action key; transaction_costs.ml_dsa_65_verification_cost): ~175 Keccak-f + ~22k mod-q mults
    add("ML-DSA-65 verify (175 Keccak-f + 22k mod-q mul)", 100e9, (175 * KECCAK_CELLS + 22000 * 5, 22000 * 3), 175 * keccak_bin + 22000 * (v(p, "bin_mul_and") + 2), src="D sketch")
    add("contract loading byte (SHA-256 + PREP)", 1_089_295, (SHA256_MF[0] / 64 + PREP_PER_BYTE[0], SHA256_MF[1] / 64 + PREP_PER_BYTE[1]), sha256_bin / 64 + 40, max_units=v(p, "code_bytes"), src="M SHA + D PREP")
    add("promise/receipt creation (5 SHA blocks + 50 rows)", 108_059_500_000 + 200e9, (5 * SHA256_MF[0] + 50 * 40, 5 * SHA256_MF[1] + 50 * 15), 5 * sha256_bin + 500, src="D")
    return T


# =============================================================================================
# 4. HARDWARE-DERIVED RATES
# =============================================================================================
def peak_int32(p):
    return v(p, "sm") * v(p, "int32_per_sm_clk") * v(p, "clk_ghz") * 1e9


def R(p):
    """sustained INT32 ops/s per GPU"""
    return peak_int32(p) * v(p, "eff")


def hw_report(p):
    pk = peak_int32(p)
    gold_ops = 18
    return {
        "int32_peak_ops_s": pk,
        "mont31_mul_s": pk / v(p, "mont_ops"),
        "goldilocks_mul_s": pk / gold_ops,
        "gf128_mul_s": pk / v(p, "gf128_ops"),
        "sha512_comp_s": pk / v(p, "sha512_ops"),
        "sha256_comp_s": pk / v(p, "sha256_ops"),
        "poseidon2_16_s": pk / v(p, "p2_ops"),
        "ntt_elem_s_2^24_compute": pk / (12 * v(p, "bfly_ops")),
        "ntt_elem_s_2^24_bw": v(p, "hbm_tbs") * 1e12 / (3 * 8),   # 3 passes x (4 B read + 4 B write)
    }


# =============================================================================================
# 5. ARCHITECTURE COST PRIMITIVES (INT32 ops)
# =============================================================================================
def ext_mul_ops(p, E):
    return E * E * v(p, "mont_ops") * 0.75     # D: schoolbook with ~25 % Karatsuba saving


def layer_hash(p, layer):
    """'sha384' | 'poseidon2' per layer: hash='hybrid' keeps SHA-384 for base segments and uses
    Poseidon2 for recursion layers (needs an owner decision, as does 'poseidon2')."""
    h = v(p, "hash")
    if h == "hybrid":
        return "sha384" if layer == "base" else "poseidon2"
    return h


def hash_ops_per_value(p, h=None):
    """ops to Merkle-hash one 4-byte base-field codeword value (leaf bytes + ~5 % for nodes)."""
    h = layer_hash(p, "base") if h is None else h
    if h == "poseidon2":
        return v(p, "p2_ops") / 8 * 1.05       # rate-8 sponge over 31-bit elements
    return 4 / 128 * v(p, "sha512_ops") * 1.05


def ntt_ops(p, logn):
    return logn / 2 * v(p, "bfly_ops")


def cell_ops(p, E, lb, logn, multilinear=False, h=None):
    """(ops per committed base cell, of which commitment (streamable) part)."""
    B = 2 ** lb
    ntt = ntt_ops(p, logn) + B * ntt_ops(p, logn + lb)       # iDFT n + coset DFT B*n
    hsh = B * hash_ops_per_value(p, h)
    commit = ntt + hsh
    if multilinear:
        # zerocheck: first round in the base field on (d+1) points, later rounds in K (halving);
        # WHIR folding sumcheck ~2 base*ext products per cell
        zc = 2 * (3 + 1) * v(p, "constraints_per_cell") * (E * v(p, "mont_ops") + 4)
        fold = 2 * E * v(p, "mont_ops")
        return commit + zc + fold, commit
    deep = B * E * v(p, "mont_ops")
    ev = 2 * v(p, "constraints_per_cell") * (E * v(p, "mont_ops") + 10)
    return commit + deep + ev, commit


def frac_ops(p, E, gkr):
    fp = 7 * E * v(p, "mont_ops")                          # fingerprint (base x ext products)
    if gkr:
        return fp + 28 * ext_mul_ops(p, E)               # LogUp-GKR layers (Papini-Haboeck)
    return fp + 3 * ext_mul_ops(p, E) + 2 * (fp + 2 * ext_mul_ops(p, E))   # committed logUp


ARCHS = {
    "a": "univariate AIR + FRI/WHIR (Plonky3-style), BabyBear^10, committed logUp",
    "b": "multilinear zerocheck + LogUp-GKR + stacked WHIR (main PQ stack shape), BabyBear^8",
    "c": "binary field (Binius64-style AND/MUL constraints) + FRI-Binius/WHIR",
}


def ops_mf(p, arch, m, f, lb, logn, h=None):
    """INT32 ops and committed cells for m main cells + f fractions (31-bit archs)."""
    if arch == "a":
        E = v(p, "E_a")
        c, c_commit = cell_ops(p, E, lb, logn, h=h)
        rows = m / v(p, "row_width")                    # chip rows carrying these cells
        cells = m + E * (f / 2 + rows) + E * v(p, "d_quot") * rows
        return cells * c + f * frac_ops(p, E, False), cells, cells * c_commit
    E = v(p, "E_b")
    c, c_commit = cell_ops(p, E, lb, logn, multilinear=True, h=h)
    return m * c + f * frac_ops(p, E, True), m, m * c_commit


def ops_and(p, n_and, lb, h=None):
    """INT32 ops for n AND constraints (arch c)."""
    h = layer_hash(p, "base") if h is None else h
    words = n_and * v(p, "bin_words_per_and")
    B = 2 ** lb
    if h == "poseidon2":
        h = 8 * B / 4 * v(p, "p2_ops") / 8 * 1.05
    else:
        h = 8 * B / 128 * v(p, "sha512_ops") * 1.05
    commit = words * (v(p, "bin_ntt_ops_word") * (1 + B) / 3 + h)
    piop = n_and * v(p, "bin_and_gf128") * v(p, "gf128_ops")
    return commit + piop, words, commit


def unit_cost(p, arch, row, lb=None, logn=None):
    lb = v(p, "lb_base") if lb is None else lb
    logn = v(p, "seg_log_rows") if logn is None else logn
    if arch == "c":
        return ops_and(p, row["and"], lb)
    return ops_mf(p, arch, row["m"], row["f"], lb, logn)


# =============================================================================================
# 6. WORKLOADS
# =============================================================================================
def witness_extra(p, arch):
    """gas-free work bounded by the witness: SHA-256 of every witness byte + parsing."""
    wb = v(p, "witness_bytes")
    blocks = wb / 64
    if arch == "c":
        o, cells, com = ops_and(p, blocks * 600 + wb * 4, v(p, "lb_base"))
        return o, cells, com
    m = blocks * SHA256_MF[0] + wb * v(p, "witness_parse_m")
    f = blocks * SHA256_MF[1] + wb * v(p, "witness_parse_f")
    return ops_mf(p, arch, m, f, v(p, "lb_base"), v(p, "seg_log_rows"))


def adversarial(p, arch, gas=None):
    """Max-prover-work chunk: fill witness-bounded free work, buy capped high-ratio units, then
    spend the remaining gas on the highest ops/gas unit."""
    gas = v(p, "gas") if gas is None else gas
    T = host_table(p)
    for r in T:
        r["ops"], r["cells"], r["commit"] = unit_cost(p, arch, r)
        r["ops_per_gas"] = r["ops"] / r["gas"]
    T.sort(key=lambda r: -r["ops_per_gas"])
    left = gas
    plan = []
    q = p
    if v(p, "witness_scales") and gas < v(p, "gas"):
        q = dict(p)
        q["witness_bytes"] = (max(4 * 2**20, v(p, "witness_bytes") * gas / v(p, "gas")), "D", "")
    wo, wc, wcm = witness_extra(q, arch)
    ops, cells, commit = wo, wc, wcm
    plan.append((f"witness hashing + parsing (gas-free, {v(q, 'witness_bytes') / 2**20:.0f} MiB)", 0.0, wo))
    for r in T:
        if left <= 0:
            break
        n = left / r["gas"]
        if r["max_units"] is not None:
            n = min(n, r["max_units"])
        if n <= 0:
            continue
        left -= n * r["gas"]
        ops += n * r["ops"]
        cells += n * r["cells"]
        commit += n * r["commit"]
        plan.append((r["name"], n * r["gas"], n * r["ops"]))
    return {"ops": ops, "cells": cells, "commit_ops": commit, "plan": plan, "table": T}


def realistic(p, arch, gas=None):
    """Measured mix: 3.4 % of gas in WASM ops (mainnet-like ld/st/alu mix ~ 0.55x worst op),
    the rest host-weighted at the storage-node ratio; plus a witness proportional to gas."""
    gas = v(p, "real_gas") if gas is None else gas
    T = {r["name"]: r for r in host_table(p)}
    w = T["wasm op: unaligned i32.load chain"]
    s = T["storage_read: touched trie node (9 blocks)"]
    ow, cw, mw = unit_cost(p, arch, w)
    os_, cs, ms = unit_cost(p, arch, s)
    units = gas * v(p, "wasm_share_real") / v(p, "regular_op")
    hg = gas * (1 - v(p, "wasm_share_real")) * 0.3     # A: 30 % of host gas touches trie nodes
    ops = units * ow * 0.55 + hg / s["gas"] * os_
    cells = units * cw * 0.55 + hg / s["gas"] * cs
    com = units * mw * 0.55 + hg / s["gas"] * ms
    q = deepcopy(p)
    q["witness_bytes"] = (min(v(p, "witness_bytes"), 8e6 * gas / 1e15 + 2e6), "D", "")
    wo, wc, wcm = witness_extra(q, arch)
    return {"ops": ops + wo, "cells": cells + wc, "commit_ops": com + wcm}


# =============================================================================================
# 7. RECURSION, WRAP, SIZE, VERIFY
# =============================================================================================
def bits_per_query(p, lb):
    return (0.5 * lb - 0.1) if v(p, "proven") else lb


def queries(p, lb):
    return math.ceil((v(p, "rbr_bits") - v(p, "z_grind") / 2) / bits_per_query(p, lb))


def comps_per_child(p, lb_child, logn_child, arch):
    """in-circuit hash invocations to verify one child proof. WHIR anchored on the measured
    production node (143 queries at lb 6 -> 4,956 comps) and scaled by query count and depth."""
    q = queries(p, lb_child)
    q6 = queries(p, 6)
    depth_scale = (logn_child + lb_child) / (21 + 6)
    base = v(p, "whir_comps_anchor") * (q / q6) * depth_scale
    if arch == "a" and v(p, "pcs_a") == "fri":
        base *= v(p, "fri_factor")
    return base


def rec_unit(p, arch, child_h):
    """(main cells, fractions) or AND-eq per in-circuit hash invocation of the child's hash."""
    if child_h == "poseidon2":
        n = v(p, "p2_perms_per_comp")
        return {"m": n * v(p, "p2_rec_cells"), "f": n * 20, "and": n * 40000}
    if arch == "a":
        return {"m": SHA384_MF[0], "f": SHA384_MF[1], "and": v(p, "bin_sha512_and")}
    return {"m": v(p, "rec_cells_per_comp"), "f": v(p, "rec_fracs_per_comp"), "and": v(p, "bin_sha512_and")}


def node(p, arch, n_children, lb_child, logn_child, lb_self, child_h, self_h):
    comps = n_children * comps_per_child(p, lb_child, logn_child, arch)
    u = rec_unit(p, arch, child_h)
    k = 1 + v(p, "rec_field_overhead")
    if arch == "c":
        n_and = comps * u["and"] * k
        ops, cells, _ = ops_and(p, n_and, lb_self, self_h)
        logn = math.ceil(math.log2(max(2, cells)))
    else:
        m, f = comps * u["m"] * k, comps * u["f"] * k
        logn = max(16, math.ceil(math.log2(max(2, m / 200))))
        ops, cells, _ = ops_mf(p, arch, m, f, lb_self, logn, self_h)
    return {"comps": comps, "ops": ops, "cells": cells, "logn": logn}


def mem_per_gpu_gb(p, arch, seg_cells):
    lb = v(p, "lb_base")
    per = 4 + 4 * 2 ** lb + (16 if arch != "a" else 0)   # trace + LDE (+ GKR layer) bytes per cell
    return seg_cells * per * 2 / 1e9                        # two segments in flight per GPU


def evaluate(p, arch, work):
    """Streaming timeline: segments are proved as execution produces them, then a fan-in-k tree,
    then the ZK wrap. Returns latency after the last receipt and its parts."""
    n_gpu = v(p, "n_gpu")
    Rg = R(p)
    gas = work.get("gas", v(p, "gas"))
    t_exec = v(p, "exec_s_per_pgas") * gas / 1e15 * v(p, "exec_slowdown")
    # segment geometry: committed cells per segment ~ 2^seg_log_rows x width (width ~ 160 cells/row)
    width = v(p, "seg_width") if arch != "c" else v(p, "seg_width") / 2
    seg_cells = 2 ** v(p, "seg_log_rows") * width
    n_seg = max(1, math.ceil(work["cells"] / seg_cells))
    seg_ops = work["ops"] / n_seg
    t_seg = seg_ops / Rg                                   # the last segment, one GPU
    lb_b, lb_n, lb_w = v(p, "lb_base"), v(p, "lb_node"), v(p, "lb_wrap")
    k = v(p, "fan_in")
    depth = max(1, math.ceil(math.log(n_seg, k))) if n_seg > 1 else 0
    nodes = []
    cnt = n_seg
    child_lb, child_logn = lb_b, v(p, "seg_log_rows")
    agg_ops = 0.0
    ch, rh = layer_hash(p, "base"), layer_hash(p, "rec")
    for lvl in range(depth):
        nn = math.ceil(cnt / k)
        nd = node(p, arch, min(k, cnt), child_lb, child_logn, lb_n, ch, rh)
        ch = rh
        nodes.append((lvl + 1, nn, nd))
        agg_ops += nn * nd["ops"]
        cnt = nn
        child_lb, child_logn = lb_n, nd["logn"]
    if v(p, "pre_wrap") and child_lb < lb_n:
        # one 1-child compression layer at lb_node so the wrap verifies a low-query child
        nd = node(p, arch, 1, child_lb, child_logn, lb_n, ch, rh)
        ch = rh
        nodes.append((len(nodes) + 1, 1, nd))
        agg_ops += nd["ops"]
        child_lb, child_logn = lb_n, nd["logn"]
    split = v(p, "wrap_split_eff")
    t_nodes = []
    for (_, nn, nd) in nodes:
        g = max(1.0, (n_gpu // nn) * split) if nn < n_gpu else 1.0   # idle GPUs share the last node
        t_nodes.append(nd["ops"] / (Rg * g) + v(p, "sync_s"))
    wrap = node(p, arch, 1, child_lb, child_logn, lb_w, ch, rh)   # ZK wrap (same field; size anchored on WHIR-SHA384)
    wrap_ops = wrap["ops"] * v(p, "zk_time_factor")
    t_wrap = wrap_ops / (Rg * max(1, v(p, "wrap_gpus") * split)) + v(p, "sync_s")
    crit = t_seg + sum(t_nodes) + t_wrap
    total_ops = work["ops"] + agg_ops + wrap_ops
    gpu_s = total_ops / Rg
    # throughput bound: GPU-seconds available = n_gpu x (stream_util x t_exec + latency)
    backlog = max(0.0, gpu_s - n_gpu * v(p, "stream_util") * t_exec) / n_gpu
    latency = max(crit, backlog + (t_nodes[-1] if t_nodes else 0) + t_wrap)
    size = v(p, "wrap_bytes") + v(p, "zk_bytes")
    if layer_hash(p, "rec") == "poseidon2":
        shrink = 1 - v(p, "path_share") * (1 - 32 / 42)        # 8 x 31-bit digest = 31 B vs 42 B
        size = size * shrink
    if not v(p, "proven"):
        size = size * 0.55                                 # capacity-bound queries ~ half
    vt = verify_time(p, wrap["comps"])
    return {
        "arch": arch, "gas": gas, "ops": work["ops"], "cells": work["cells"], "gpu_s": gpu_s,
        "base_gpu_s": work["ops"] / Rg, "agg_gpu_s": agg_ops / Rg, "wrap_gpu_s": wrap_ops / Rg,
        "t_exec": t_exec, "n_seg": n_seg, "t_seg": t_seg, "depth": depth, "t_nodes": t_nodes,
        "node_comps": [nd["comps"] for (_, _, nd) in nodes], "t_wrap": t_wrap, "crit": crit,
        "backlog": backlog, "latency": latency, "size": size, "verify_s": vt,
        "mem_gb": mem_per_gpu_gb(p, arch, seg_cells), "seg_cells": seg_cells,
        "design": {k_: v(p, k_) for k_ in DESIGN_KEYS},
        "q_base": queries(p, lb_b), "q_node": queries(p, lb_n), "q_wrap": queries(p, lb_w),
    }


DESIGN_KEYS = ("seg_log_rows", "lb_base", "lb_node", "fan_in", "pre_wrap")
GRID = {"seg_log_rows": range(18, 27), "lb_base": (1, 2, 3), "lb_node": (2, 3, 4, 5, 6),
        "fan_in": (2, 4, 8, 16), "pre_wrap": (0, 1)}


def best_design(p, arch, kind="adv", gas=None):
    """grid-search the design knobs (segment size, rates, fan-in, pre-wrap layer) for minimum
    latency subject to HBM capacity; returns (params, result)."""
    import itertools
    best = None
    for combo in itertools.product(*GRID.values()):
        q = dict(p)
        for k_, val in zip(GRID, combo):
            q[k_] = (val, "opt", p[k_][2])
        r = run(q, arch, kind, gas)
        if r["mem_gb"] > v(p, "hbm_gb") * 0.9:
            continue
        if best is None or r["latency"] < best[1]["latency"]:
            best = (q, r)
    return best


def verify_time(p, comps):
    return comps * v(p, "cpu_sha512_ns") * 1e-9 + v(p, "verify_ext_mults") * v(p, "cpu_ext_mul_ns") * 1e-9 + 0.002


def run(p, arch, kind="adv", gas=None):
    if kind == "adv":
        w = adversarial(p, arch, gas)
        w["gas"] = v(p, "gas") if gas is None else gas
    else:
        w = realistic(p, arch, gas)
        w["gas"] = v(p, "real_gas") if gas is None else gas
    return evaluate(p, arch, w)


def lat(p, arch, kind="adv", gas=None, opt=True):
    if opt:
        return best_design(p, arch, kind, gas)[1]["latency"]
    return run(p, arch, kind, gas)["latency"]


def max_gas(p, arch, kind="adv", opt=True):
    """largest chunk gas (worst case of that size) whose latency fits the budget."""
    lo, hi = 1e11, 1e15
    if lat(p, arch, kind, hi, opt) <= v(p, "budget_s"):
        return hi
    if lat(p, arch, kind, lo, opt) > v(p, "budget_s"):
        return 0.0
    for _ in range(14):
        mid = math.sqrt(lo * hi)
        if lat(p, arch, kind, mid, opt) <= v(p, "budget_s"):
            lo = mid
        else:
            hi = mid
    return lo


def required_eff(p, arch, kind="adv", opt=True):
    lo, hi = 0.01, 5.0
    for _ in range(12):
        mid = (lo + hi) / 2
        q = deepcopy(p)
        q["eff"] = (mid, "solve", "")
        if lat(q, arch, kind, None, opt) <= v(p, "budget_s"):
            hi = mid
        else:
            lo = mid
    return hi


SENS = [  # (param, low, high); design knobs (DESIGN_KEYS) are re-optimised, not varied
    ("eff", 0.20, 0.60), ("exec_s_per_pgas", 0.5, 2.0), ("E_a", 8, 12), ("E_b", 6, 10),
    ("bfly_ops", 7, 14), ("sha512_ops", 2500, 4500), ("constraints_per_cell", 0.4, 1.2),
    ("rbr_bits", 200, 290), ("rec_cells_per_comp", 15000, 45000), ("rec_field_overhead", 0.0, 0.5),
    ("witness_bytes", 16 * 2**20, 64 * 2**20), ("code_bytes", 0, 64 * 2**20), ("stream_util", 0.6, 1.0),
    ("zk_time_factor", 1.2, 2.0), ("wrap_split_eff", 0.3, 0.9), ("seg_width", 80, 320),
    ("gf128_ops", 60, 1200), ("bin_and_gf128", 10, 40), ("hbm_gb", 80, 282),
    ("hash", "sha384", "hybrid"), ("proven", 1, 0),
]


def sensitivity(p, arch, metric="latency"):
    """one-at-a-time swings; the design knobs are re-optimised at every point (except when the
    knob itself is the parameter being varied)."""
    def f(q, fixed):
        if fixed in DESIGN_KEYS:
            g = dict(GRID)
            GRID[fixed] = (v(q, fixed),)
            try:
                return best_design(q, arch)[1][metric]
            finally:
                GRID.clear()
                GRID.update(g)
        return best_design(q, arch)[1][metric]
    base = best_design(p, arch)[1][metric]
    rows = []
    for name, lo, hi in SENS:
        res = []
        for val in (lo, hi):
            q = deepcopy(p)
            q[name] = (val, "sens", "")
            res.append(f(q, name))
        rows.append((abs(res[1] - res[0]), name, lo, hi, res))
    rows.sort(key=lambda r: -r[0])
    return base, rows


# =============================================================================================
# 8. REPORT
# =============================================================================================
def fmt(x, d=3):
    if x == 0:
        return "0"
    if abs(x) >= 1e4 or abs(x) < 1e-2:
        return f"{x:.{d - 1}e}"
    return f"{x:.{d}g}"


def report(p, prior=False):
    out = {}
    print("== H200 SXM derived rates (100 % of INT32 peak; multiply by eff for sustained) ==")
    hw = hw_report(p)
    for k_, x in hw.items():
        print(f"  {k_:28s} {fmt(x)} /s")
    print(f"  sustained INT32 at eff={v(p, 'eff')}: {fmt(R(p))} ops/s/GPU")
    for arch in ("a", "b"):
        E = v(p, f"E_{arch}")
        c, cm = cell_ops(p, E, v(p, "lb_base"), v(p, "seg_log_rows"), arch == "b")
        print(f"  arch {arch}: ops/committed cell {c:.0f} (commit part {cm:.0f}); ops/fraction {frac_ops(p, E, arch == 'b'):.0f}")
    print(f"  arch c: ops/AND {ops_and(p, 1, v(p, 'lb_base'))[0]:.0f}")

    print("\n== Workload: per-unit cost and cost per gas (arch a units: work INT32 ops) ==")
    T = adversarial(p, "a")["table"]
    ld = [r for r in T if r["name"].startswith("wasm op: unaligned")][0]
    print(f"  {'unit':52s} {'gas/unit':>10s} {'max/Pgas':>9s} {'main':>9s} {'frac':>8s} {'AND-eq':>8s} {'ops/gas a':>9s} {'vs wasm':>7s}")
    for r in T:
        print(f"  {r['name'][:52]:52s} {r['gas']:10.3g} {1e15 / r['gas']:9.3g} {r['m']:9.3g} {r['f']:8.3g} {r['and']:8.3g} {r['ops_per_gas']:9.3g} {r['ops_per_gas'] / ld['ops_per_gas']:7.2f}")
    for arch in ("a", "b", "c"):
        w = adversarial(p, arch)
        print(f"\n  adversarial plan, arch {arch}: total {fmt(w['ops'])} INT32 ops ({fmt(w['ops'] / R(p))} GPU-s at eff)")
        for name, g, o in w["plan"]:
            print(f"    {name[:58]:58s} gas {g / 1e12:8.1f} Tgas  ops {fmt(o)}")

    print("\n== Verdict table (latency after last receipt; budget %.1f s on %d H200) ==" % (v(p, "budget_s"), v(p, "n_gpu")))
    hdr = f"  {'arch':4s} {'case':5s} {'Tgas':>6s} {'GPU-s':>7s} {'base':>6s} {'agg':>5s} {'wrap':>5s} {'segs':>6s} {'depth':>5s} {'t_seg':>6s} {'nodes':>14s} {'t_wrap':>6s} {'crit':>6s} {'backlog':>7s} {'LAT':>6s} {'GB/GPU':>6s} {'size B':>8s} {'verify':>7s}"
    print(hdr)
    res = []
    for arch in ("a", "b", "c"):
        for kind in ("adv", "real"):
            r = best_design(p, arch, kind)[1]
            res.append(r)
            print(f"  {arch:4s} {kind:5s} {r['gas'] / 1e12:6.1f} {r['gpu_s']:7.2f} {r['base_gpu_s']:6.2f} {r['agg_gpu_s']:5.2f} {r['wrap_gpu_s']:5.2f} {r['n_seg']:6d} {r['depth']:5d} {r['t_seg']:6.3f} {'/'.join(f'{t:.2f}' for t in r['t_nodes']):>14s} {r['t_wrap']:6.3f} {r['crit']:6.2f} {r['backlog']:7.2f} {r['latency']:6.2f} {r['mem_gb']:6.0f} {r['size']:8.0f} {r['verify_s'] * 1e3:6.1f}ms")
    print("  designs chosen (grid search, HBM <= 90 %):")
    for r in res:
        print(f"    {r['arch']} {r['gas'] / 1e12:6.1f} Tgas: {r['design']}  node comps {[round(c) for c in r['node_comps']]}")
    out["verdict"] = res
    print("\n== Feasibility frontier ==")
    fr = {}
    for arch in ("a", "b", "c"):
        g_adv = max_gas(p, arch, "adv")
        g_real = max_gas(p, arch, "real")
        e_adv = required_eff(p, arch, "adv")
        fr[arch] = {"max_gas_adv": g_adv, "max_gas_real": g_real, "eff_needed_1pgas_adv": e_adv}
        print(f"  arch {arch}: worst-case chunk feasible up to {g_adv / 1e12:7.1f} Tgas; realistic-mix up to {g_real / 1e12:7.1f} Tgas; "
              f"1 Pgas worst case needs eff >= {e_adv:.2f}{" (search ceiling)" if e_adv > 4.9 else ""} of INT32 peak{" -- impossible" if e_adv > 1 else ""}")
    out["frontier"] = fr
    print("  worst-case Tgas feasible in budget, by efficiency and GPU count (archs a / b):")
    for n in (8, 16, 32):
        cells = []
        for e in (0.2, 0.35, 0.6):
            q = deepcopy(p)
            q["eff"] = (e, "grid", "")
            q["n_gpu"] = (n, "grid", "")
            cells.append(f"eff {e:.2f}: {max_gas(q, 'a') / 1e12:6.1f} / {max_gas(q, 'b') / 1e12:6.1f}")
        print(f"    {n:2d} H200  " + "   ".join(cells))
    print(f"  proof: {res[0]['size']:.0f} B vs cap {v(p, 'size_cap')} (non-ZK wrap {v(p, 'wrap_bytes')} + ZK {v(p, 'zk_bytes')})")
    print(f"  verify (protocol model): {res[0]['verify_s'] * 1e3:.1f} ms; measured implementation {v(p, 'verify_impl_s')} s (32 threads)")
    print(f"  queries per round (proven={v(p, 'proven')}): " + ", ".join(f"lb{lb} {queries(p, lb)}" for lb in range(1, 8)))
    print(f"  ZK: wrap prover x{v(p, 'zk_time_factor')}, +{v(p, 'zk_bytes')} B; alternatives: salted-leaf masking ~15 KB (A), "
          f"Poseidon2 recursion digests -> {v(p, 'wrap_bytes') * (1 - v(p, 'path_share') * (1 - 32 / 42)) + v(p, 'zk_bytes') * (1 - v(p, 'path_share') * (1 - 32 / 42)):.0f} B")
    need = v(p, "wrap_bytes") + v(p, "zk_bytes") - v(p, "size_cap")
    print(f"  bytes to remove to meet the cap with SHA-384 + HVZK-WHIR: {need:.0f} B ({100 * need / (v(p, 'wrap_bytes') + v(p, 'zk_bytes')):.1f} %)")

    print("\n== Main-stack node on GPU (MR geometry: 254.1 M cells, 87.1 M interactions, lb 6, 2^21) ==")
    o, _, _ = ops_mf(p, "b", 254_084_224, 87_097_600, 6, 21)
    print(f"  {fmt(o)} ops -> {o / R(p):.2f} s on one H200 at eff {v(p, 'eff')} (CPU measured 700.5-903.5 s); "
          f"depth-8 binary tree critical path {8 * (o / R(p) + v(p, 'sync_s')):.1f} s")
    o4, _, _ = ops_mf(p, "b", 254_084_224, 87_097_600, 4, 21)
    print(f"  same node at lb 4 (rate 1/16): {o4 / R(p):.2f} s")

    for arch in ("a", "b", "c"):
        base, rows = sensitivity(p, arch)
        print(f"\n== Sensitivity, arch {arch}, 1 Pgas adversarial latency (base {base:.2f} s) ==")
        for sw, name, lo, hi, rr in rows[:12]:
            print(f"  {name:22s} {str(lo):>10s} -> {rr[0]:6.2f} s | {str(hi):>10s} -> {rr[1]:6.2f} s | swing {sw:5.2f}")
        out[f"sens_{arch}"] = [(name, lo, hi, rr) for sw, name, lo, hi, rr in rows]
    if prior:
        print("\n== V3-PERF-DESIGN shared-transcript design (tools/perf-design/model.py) at 8 GPUs ==")
        sys.path.insert(0, __file__.rsplit("/research/", 1)[0] + "/tools/perf-design")
        import model as pm   # noqa: E402
        for n in (8, 32):
            q = deepcopy(pm.P)
            q["sha512_int_ops"] = (v(p, "sha512_ops"), "C")
            r = pm.scenario(q, "adversarial", "U-logUp", n)
            print(f"  {n:2d} H200: GPU-s {r['gpu_s']:.1f}, after execution {r['after_exec']:.2f} s, memory {r['mem_gb_per_gpu']:.0f} GB/GPU (HBM {v(p, 'hbm_gb')} GB), proof {r['proof_bytes'] / 1e3:.0f} KB (FRI)")
            out[f"prior_{n}"] = {"gpu_s": r["gpu_s"], "after_exec": r["after_exec"], "mem": r["mem_gb_per_gpu"]}
        for budget in (3.0,):
            e, cps, r = pm.required(pm.P, "U-logUp", 8, budget)
            print(f"  8 H200, <= {budget} s after execution: eff >= {e:.2f} (memory {r['mem_gb_per_gpu']:.0f} GB/GPU)")
    print("\n== Parameters ==")
    for k_, (val, lab, note) in p.items():
        print(f"  {k_:22s} {str(val):>14s}  [{lab}] {note}")
    return out


def parse_overrides(argv, p):
    q = deepcopy(p)
    for i, a in enumerate(argv):
        if a == "--set":
            k_, val = argv[i + 1].split("=", 1)
            try:
                val = float(val)
            except ValueError:
                pass
            q[k_] = (val, "override", q[k_][2] if k_ in q else "")
    return q


if __name__ == "__main__":
    pp = parse_overrides(sys.argv, P)
    if "--json" in sys.argv:
        res = {a: {k_: run(pp, a, k_) for k_ in ("adv", "real")} for a in ("a", "b", "c")}
        print(json.dumps(res, indent=1, default=str))
    else:
        report(pp, prior="--prior" in sys.argv)

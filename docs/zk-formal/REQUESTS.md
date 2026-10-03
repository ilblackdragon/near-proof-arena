# Interface requests between lanes

## L8 → L4: wire-level choices implemented by the Rust prover (proposal for FORMATS.md)

Status: implemented in `examples/np-udr-stark/source` (branch `lane/zk-L8`),
self-consistent with the Rust reference verifier (`src/verifier.rs`, written
to be ported line by line). Everything below that L4's FORMATS.md fixes
differently will be changed on the Rust side; this list exists so that the
two sides do not diverge silently. Items marked ✓ already agree with L4's
in-progress `Air/Basic.lean`, `Air/Export.lean`, `Stark/Field.lean`.

1. ✓ AIR import: `np-air-v1` JSON exactly as `Air.exportJson`; table
   `constraints` = `allConstraints` (α_c order). Selectors are the exact 0/1
   Lagrange interpolants; at `z`: `Z = z^T − 1`, `isFirst = Z/(T(z−1))`,
   `isLast = h·Z/(T(z−h))` with `h = ω_T^{-1}`, `isTransition = 1 − isLast`.
   Public input `i` = `cb[i]` as a field element, 0 if `i ≥ |cb|`.
2. ✓ `decodeChal`, `decodeOod`, `bitrev`, `domPoint` as in `Stark/Field.lean`
   (ω_27 = 31^15 = 0x1a427a41, Plonky3's generator; shift 31).
3. Oracle: `H(m) = sha256("NPAI-RO-v1" ‖ m)`. `WH(tag, m) = H(tag‖0x01‖m) ‖ H(tag‖0x02‖m)`.
   Tags: INIT 0x01, ABS 0x02, CHAL 0x03, QUERY 0x04, LEAF 0x05, NODE 0x06.
4. Transcript:
   * `d₀ = WH(INIT, "np-udr-stark-v1"(15 B) ‖ pubDigest(32 B) ‖ header ‖ u32le(|cb|) ‖ cb)`,
     `header = u32le(version=1) ‖ u32le(numTables) ‖ u8(h_t) per table` (the same
     bytes as the proof header). `pubDigest` is currently a caller-supplied
     32-byte value (proposal: `ArenaCore.sha256 pub`).
   * Every challenge is preceded by exactly one absorbed message `m`
     (possibly empty): `d ← WH(ABS, d ‖ m)`, `c = decodeChal(H(CHAL ‖ d))`
     (`decodeOod` for `z`). Messages are raw concatenations (no length
     prefix; lengths are fixed by the schedule).
   * Rounds: `root_main`→α_fp; ε→γ_mul; `root_aux ‖ finals(K…)`→α_c;
     `root_quot`→z; `ood values (K…)`→first batching challenge, ε→each further
     batching challenge (class layers ascending, `⌈log₂ m_k⌉` per class); FRI
     for `k = 0..L−1`: (`root_k` if layer k committed, else ε)→β_k, then if
     `k+1` is a class layer, ε→γ_{k+1}; finally `d_fin = WH(ABS, d ‖ c0 ‖ c1)`
     (final polynomial) with no challenge.
   * Query chunk `j < 24`: `A_j = H(QUERY ‖ d_fin ‖ u8(j))`; with `N` the
     big-endian integer of `A_j`, positions `(N >> 26·i) mod 2^26 mod n0`,
     `i = 0..8` (chunk-major order, duplicates kept).
5. Domains: table `t`, height `2^{h_t}` (`1 ≤ h_t ≤ maxLog`), LDE size
   `2^{l_t}`, `l_t = h_t + 4`, `l0 = max l_t`, class `k_t = l0 − l_t`, LDE coset
   `31^{2^{k_t}}·⟨ω_{l_t}⟩`; all evaluation vectors in bit-reversed order
   (`domPoint l0 (l0−k) j`). FRI: `L = max h_t − 1` folds, final layer has
   32 points, `f_L = c0 + c1·y`.
6. Quotient: per table, `C = Σ_i α_c^i·C_i` (i over `allConstraints`,
   restarting at `α_c^0` for each table), `nq = max(1, d−1)` chunks with
   `d = max(1, max degree)`, `Q = Σ_j x^{jT}·Q_j`, `deg Q_j < T`. Check at `z`:
   `C(v) = Z_H(z)·Σ_j z^{jT}·Q_j(z)`.
7. OOD values (message after `root_quot`), per table in table order:
   main columns at `z`, main at `g_t·z`, aux at `z`, aux at `g_t·z`, quotient
   chunks at `z`, each a `K` element (32 bytes). Aux columns are `K`-valued.
8. DEEP batch of class layer `k`: the concatenation of the OOD lists of the
   tables of class `k` (table order), term `i`: `(f_i(x) − v_i)/(x − ζ_i)`,
   coefficient `∏_j r_{k,j}^{bit_j(i)}` (bit 0 ↔ first challenge).
   `G_0` is FRI layer 0; at class layer `k > 0`: `f_k = fold(f_{k−1}) + γ_k·G_k`.
9. Fold: positions `2j, 2j+1` of layer k (points `±x`, `x = domPoint` of `2j`)
   → position `j`: `(a+b)/2 + β_k·(a−b)/(2x)`.
10. Committed FRI layers: `k₀ = 0`, `k_{i+1} = min(k_i + 3, next class layer > k_i, L)`;
    stop when it reaches `L` (layer L is never committed; the final
    polynomial replaces it; if `L = 0` nothing is committed). Arity of layer
    `k_i` is `2^{k_{i+1} − k_i}`; leaf `j` holds positions `j·arity … j·arity+arity−1`
    as K elements (8 limbs each). Query check at a committed layer: the
    opened leaf value at `pos mod arity` must equal the running value, then
    fold within the leaf.
11. MMCS (each of main/aux/quot over all tables; each FRI layer separately):
    `N_0[j] = WH(LEAF, rows_0(j))`;
    `N_k[j] = WH(NODE, u8(k) ‖ N_{k−1}[2j] ‖ N_{k−1}[2j+1] [‖ WH(LEAF, rows_k(j))])`,
    the bracket present iff some matrix (even of width 0) has height
    `H0/2^k`; `rows_k(j)` = concatenation over those matrices (table order) of
    row `j` (bit-reversed position), base elements as u32le, K elements as
    8 limbs. Aux/quot matrices exist for every table (width `8·#aux`,
    `8·nq`).
12. Multiproof: `S_0 = sort∘dedup(J)`, `S_k = dedup(S_{k−1} >> 1)`; rows: per
    matrix, per `j ∈ S_{k_m}` ascending; siblings: for k = 1..L, j ∈ S_k
    ascending, c ∈ [2j, 2j+1], `N_{k−1}[c]` if `c ∉ S_{k−1}`.
13. Proof bytes (context-free parse, counts as u32le):
    `u32 version, u32 numTables, u8 h_t…, root_main(64), root_aux(64),
    u32 n, K×n (finals), root_quot(64), u32 n, K×n (ood), u32 n, 64×n (FRI roots),
    K, K (final poly), openings main, aux, quot, fri_0..`; opening =
    `u32 nMats, (u32 nVals, F×nVals)×nMats, u32 nSib, 64×nSib`. Reject > 8 MiB
    before parsing, non-canonical field elements, and trailing bytes.

Open (needs L4/L3): the aux (grand-product) column layout for buses with
bit-list multiplicities (`auxGroup`), the `finals` message, and the bus
balance check at `z`. The Rust side currently rejects AIRs with interactions.

# Lane `lane/v3-p2` — P2: `auxGroup ∈ {1,2,3}` for `np-udr-stark-v2`: status

Design: `V3-D0-DESIGN.md` §5.3 (P2) and §10–§11. Lead decision: run P2 now.

v1 is unchanged byte for byte. No existing definition or proof was edited (v1 or v2). The only
change to an existing file is the root `zk-formal/ZkFormal.lean`, which now also imports the new
modules.
Everything new is in two places:
* `zk-formal/ZkFormal/V2/G/` (soundness and size; 3.2 k lines);
* `zk-formal/ZkFormal/V2/PG/` (prover model and completeness; 5.8 k lines, mostly mechanical copies).

Rules: no `sorry`, `axiom` or `native_decide`. Every theorem below was checked with
`#print axioms` and uses only `propext`, `Classical.choice` and `Quot.sound` (std3).
`decide +kernel` is used only for numerics on concrete AIRs.

## Parameters

* `V2.G.pg g := {Params.default with auxGroup := g}`. Every other field is v1's, so all
  numerics reduce by `rfl`. `pg 1 = Params.default` holds by `rfl`.
* `V2.G.NpOkG A prm` is v1's `NpOk` with `prm = Params.default` replaced by
  `∃ g, prm = pg g ∧ 1 ≤ g ∧ g ≤ 3`. The constraint-count and bus-count bounds are unchanged.
* `V2.G.NpOkPg AP prm := NpOkG AP.toAir prm ∧ AP.wf (2^prm.logBlowup)`.
  `npOkPg_of_npOkP : NpOkP → NpOkPg`.
* The table-degree side condition `Table.degree t g ≤ 2^logBlowup` needs no extra
  hypothesis. It is already part of v1's `headerOk`, which the verifier checks
  (`headerOk_facts`).

## Statements

| deliverable | statement | file | state |
|---|---|---|---|
| P2 defs | `pg`, `NpOkG`, `NpOkPg`, `MsgAtPg`/`ChalAtPg`/`QueryStmtPg`, `chunksOf_flatten`/`_length`/`_map`/`_le`, `chunksOf_go_sub`, `numGroups_le` | `V2/G/Defs.lean` | proved |
| L3 aux chain | `grpsOf`, `auxC_semG`, `table_fins` (final of group `j` = `∏_{i∈grp j} Φ_t(i)`), `table_side`, `TabOk`/`tabOk_of`, `finsOf_length`, `no_localFail`, `gp_tables`, `table_sides` | `V2/G/Groups.lean` | proved |
| L3 degrees | `table_deg` (from `degree g ≤ 16`), `gc_rep`, `auxC_rep`, `csAt_rep` (all constraints `Dg T 128`), `csAt_length` (`numGroups ≤ n`) | `V2/G/Deg.lean` | proved |
| L3 v1 lemmas at `pg g` | `LayOk`, `deep_ok`, `layOk_of`, `tl_mem`, `tl_dec`, `colAt_zero`, `ali_of_global`, `lay_facts`, `queryLog_le`, `eRad_two`, `bound_budget`, `eRad_step`, `Bridge6` lemmas, `busTagsOk_of` | `V2/G/V1.lean` | proved (generated copies) |
| L3 rounds | `chal1P chal3P` (`G/Bus`), `msg0P msg2P msg6P chal5P chal7P` (`G/Early`), `msg4P` (`G/Msg4`), `msg8P` (`G/Msg8`), `msgLateP chalLateP` (`G/Late`), `queryP` (`G/Query`), all under `NpOkPg` | `V2/G/*.lean` | proved |
| **L3** | **`ZkFormal.V2.G.rbrWithPg`** `(AP) (prm) (hok : NpOkPg AP prm) : RbrWith (VnpP AP prm) (AirLangP AP) Fp8.all badBudget (agreeUdr prm.logBlowup) (DoomedP AP prm)`; `rbrFactsPg`; `rbrWithPg_of` | `V2/G/Main.lean` | proved |
| **L2** | **`ZkFormal.V2.stark_romSound_fullPg`**: `stark_romSound_fullP` with `hok : NpOkPg AP prm` (ROM soundness at `2^-128`, `num·2^128 ≤ den`) | `V2/G/RomFull.lean` | proved |
| L7 prover model | `Prover.Np.G.*`: copy of `Prover/Np*` with `dp := pg AuxG.g` (`class AuxG` with `g` and `1 ≤ g`). New proofs: `groupsOf_length`, `degree_facts` (per group `2 + Σ phiDegree ≤ degree g`), `foldl_pd`/`phiF_pd`, `csX_poly`, `groups_eq`, `prodF_chunks`, `prod_phiG_send/recv`, `numSide_eq` | `V2/PG/Np*.lean` | proved |
| L7 | `Prover.Np.G.npIopComplete'` (v1 statement at `dp = pg g`), `Prover.Np.G.npIopCompleteP` | `V2/PG/NpLocalMain.lean`, `V2/PG/V2Prover.lean` | proved |
| **L7** | **`ZkFormal.V2.G.npIopCompletePg`** `(g) (hg : 1 ≤ g) (AP cb tr) : AP.tables.length < 2^32 → HoldsP AP (pubOf cb) tr → (verifierP AP (pg g)).headerOk (trHdr AP tr) → ∃ pr, pr.hdr = … ∧ ProverWf … ∧ IopComplete (Iop.verifierP Fp Fp8 AP (pg g)) pr cb` | `V2/PG/V2Prover.lean` | proved |
| **L7** | **`ZkFormal.V2.G.np_proverCompletePg`** `(g) (hg : 1 ≤ g)`: `V2.np_proverCompleteP` at `pg g` | `V2/PG/Admission.lean` | proved |
| **assembly** | `Prover.Np.G.admission_v2` (for any `[AuxG]`); **`ZkFormal.V2.G.admission_v2_pg`** `(g) (hg : 1 ≤ g)`. The verifier is `guardTree claimOk (hintTree split prep (verifierP Fp Fp8 AP (pg g)))` (`npVerifierP_pg`, `rfl`). The `hok : NpOkPg AP (pg g)` hypothesis restricts to `g ≤ 3`. | `V2/PG/Admission.lean` | proved |
| toy at g = 3 | **`ZkFormal.V2.Toy.G3.toyP_admission_g3`**: closed `AdmissionStatement` for the v2 toy against `verifierP … toyAirP (pg 3)`. Includes `toy_npOkPg`, `toy_NVuP`, `toy_sizeMaxSchedP` and `toy_headerP` at `pg 3`, all by `decide +kernel`. | `V2/PG/Toy3.lean` | proved |
| size | `near_sizeMaxSched_g2 = 5 347 055`, `near_sizeMaxSched_g3 = 5 353 423`, `near_friSchedMax_g3 = 12 928`, `near_size_sched_g2/g3`, `nearAir_npOkG3`, `nearAir_deg3` | `V2/G/SizeNear.lean` | proved (`decide +kernel`) |

`admission_v2` is instantiable at g ∈ {1,2,3}:
* `admission_v2_pg g hg` for `g = 1, 2, 3`;
* `toyP_admission_g3` closes every hypothesis at `g = 3`;
* `nearAir_npOkG3` and `nearAir_deg3` discharge the static P2 side conditions for `nearAir` at `g = 3`.

## Size: deliverable 3 (kernel numbers, `nearAir`)

| `g` | per-table `degree g` | Σ aux (K cols) | Σ quot (K cols) | `sizeMaxSched` (B) | delta vs `g = 1` |
|---|---|---|---|---|---|
| 1 (`Params.default`) | 4 ×7 | 66 | 21 | 5 473 967 | — |
| 2 | 6 ×6, 4 | 36 | 33 | **5 347 055** | **−126 912** |
| 3 | 8 ×5, 6, 4 | 27 | 43 | **5 353 423** | **−120 544** |

`friSchedMax` is unchanged (12 928 B per query) because the FRI part depends only on the LDE
sizes. The toy AIR has no interactions, so its bound is 2 832 681 B at every `g`.

**Finding (design §5.3 / D-6):** the "−0.46 MB at g = 3" estimate counts only the removed aux
columns (−66 × 32 B × 216). It misses that grouping raises `Table.degree`: every `nearAir` bus
factor has `phiDegree = 2`, so a group of 3 has degree `2 + 6 = 8`. The number of quotient
chunks (`degree − 1`) then grows from 3 to 7 per table.
* On `nearAir` the net saving is 0.12 MB (−39 aux, +22 quot columns).
* `g = 2` is marginally better than `g = 3`.

The actual proof bytes change by the same per-query amount: every query opens all
main/aux/quotient rows, plus the OOD delta. For the v3 AIR, measure with `sizeMaxSched` at
`pg 2` and `pg 3` once `nearAirV3` exists. The best `g` depends on the AIR's `phiDegree`
profile.

## Rust: deliverable 4 (documented delta, no test)

The Rust prover does **not** take `auxGroup` as a parameter, and there is nothing to test a
`g = 3` v2 proof against:
* `examples/np-udr-stark/source/src/aux.rs` has `pub const AUX_GROUP: usize = 1`. It is used in
  `AuxLayout::new` (grouping) and `aux_degree` (`table_degree`, hence `quot`). The rest of the
  prover and the reference verifier are already group-generic: `lay.groups`, the group products
  `phi = Π phis[i]` in `aux_constraints`, `prover_ref.rs` `gphi`, and `verifier.rs`
  `send_groups`.
* The Rust crate implements only `np-udr-stark-v1`. It has no public segments, no
  `Π_pub`, no `np-air-v2` export reader, and no `verifierP`.
* There is no compiled Lean v2 verifier executable either: no `lean_exe` for `V2.verifierP`.

Rust delta for a v2 `g = 3` proof (new protocol id only; v1 bytes unchanged):
1. Replace `AUX_GROUP` with a `group: usize` field of a protocol-parameter struct that defaults
   to 1 for v1. Thread it through `AuxLayout::new(t, g)`, `aux_degree(t, g)`,
   `table_degree(t, g)`, `Schedule` (aux/quot counts, finals count) and both provers.
   `AuxLayout` already chunks with `idx.chunks(g)`, which is `chunksOf g`.
2. Implement v2 (`STATUS-V3-BUS` / `FORMATS.md` §8):
   * parse `np-air-v2` (`pubSegs`, `maxPub`, `numPub`);
   * add the public messages `Π_pub(s)` to the bus check;
   * check `pubFit`.

   The prover's proof bytes are v1's for the same parameters.
3. Add a Lean `lean_exe` for `V2.verifierP Fp Fp8 AP (pg g)` (BCS-compiled, as for v1) and a
   conformance test (toy, `g = 3`). For the v2 toy, the `g = 3` proof bytes equal the `g = 1`
   ones because `toyAirP` has no interactions. A byte-level test that distinguishes `g` needs an AIR with
   ≥ 2 interactions on some side. One example is a v1 AIR with buses lifted to v2 with no
   segments (`holdsP_iff_holds`).

## Proof notes

* **Soundness.** The only mathematical change is in the aux round (`Msg4`), the degree round
  (`Chal7`) and the constraint count (`Chal5`). Everything else is v1 or v2 text at `pg g`.
  * The other rounds and the query phase use `Params.default` only through fields that `pg g`
    shares, so they are generated copies with `Params.default ↦ pg g`.
  * `g ≤ 3` is used in exactly one place, `Chal7`. A group product of `≤ 3` factors, each of
    degree `≤ 32·T` (v1's crude bound), keeps every constraint below `128·T`. The root count
    `128·2^22 + P ≤ 2^36` still fits the per-round budget.
  * Completeness needs only `1 ≤ g`.
* **Completeness.** v1's honest prover was already written group-generically
  (`groupsOf = chunksOf (max dp.auxGroup 1) …`). Only the following lemmas specialised it to `g = 1`
  (through `chunksOf_one` or `numGroups n 1 = n`):
  * `groupsOf_length` and `groups_eq`;
  * `prod_phiG_send/recv` and `numSide_eq`;
  * `auxDegree_ge`, `degree_facts`, `chunks_evP` and `csX_poly`.

  They are re-proved for any `g ≥ 1`, using `chunksOf_flatten` (the groups partition each side)
  and a per-group degree bound.
* **Name resolution.** The prover copies live in `ZkFormal.Prover.Np.G`, nested in v1's
  namespace, with the group size as an instance `[AuxG]`. Inside them every v1 name resolves
  exactly as in v1, and every copied name shadows its v1 version. Call sites needed no edits.
  The soundness copies live in `ZkFormal.V2.G`, which opens `ZkFormal.V2.Np`.
* `dp_decide` (in `V2/PG/NpDefs.lean`) replaces `decide` on goals that mention `dp`, whose
  instance is a free variable.

## Elaboration times

`lake env lean <file>` per file, CPUs 8–15/24–31, warm cache. Each figure includes about 1 s
of import loading.
* All 52 new files: 170 s in total.
* Largest: `G/SizeNear` 42 s (kernel evaluation of `sizeMaxSched` on `nearAir` at `g = 2, 3`,
  plus `nearAir_npOkG3`), `G/Query` 16 s, `PG/NpGlobal2` 9 s, `G/Groups` 9 s, `G/Late` 7 s,
  `PG/NpAux` 7 s.
* Every other file takes ≤ 6 s.
* Full root `lake build`: 645 jobs, successful.

## Open

* Rust: see deliverable 4 above. Not started; it needs v2 in Rust first.
* The copies are about 9 k lines. A later refactor could make v1's L3 and L7 generic in
  `prm`/`AuxG` and recover v1 as `g = 1`. That would mean editing v1 proofs, which this lane
  avoided by rule.
* `nearAirV3` (the v3 AIR) does not exist yet. Re-run `sizeMaxSched` at `pg 2`/`pg 3` on it to
  choose `g`.

## Commits (`lane/v3-p2`)

`6d75d8b`, `d6ad2d1`, `7c2d763` (soundness); `f690410`, `787a079`, `274041a` (completeness,
admission, toy); `9b8b79b` (size, root imports); this status file.

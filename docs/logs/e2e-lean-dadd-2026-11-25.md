# E2E lane E (Lean join): integrator decisions D-a – D-d, (H2), 2026-11-25

Plan: [`docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md`](../zk-formal/E2E-GENERAL-CHUNK-PLAN.md) §3.5
("Lane E D-a – D-d"). Previous logs: [`e2e-lean-m12-2026-11-25.md`](e2e-lean-m12-2026-11-25.md),
lane B's [`e2e-bt2-state-2026-11-25.md`](e2e-bt2-state-2026-11-25.md). Branch base: main
`3930da629` (lane B's B-T2 merged).

`S`, `claimDigest` and the checker are unchanged (no stop): every change is view data or a new
lemma; `nearspec-v3-check-successor` does not import `E2E/`. Standard axioms only; no `sorry`,
`native_decide` or `axiom`.

## D-a: the boundary at `start` commits lane B's `R_0` (own commit `369767b3b`)

* `View.lean`: `EngSt.ovl0 : Option Ovl` (the overlay at `start`); `ovl0Of I` (`some (Ovl.ofTrie
  I.tMain)` at `start`, `none` elsewhere); **`stOfI κ I c`** is the view's state component
  (`split`), `stOfI_of_ne` (= `stOfK (κ I) c` away from `start`), `stOfI_start`,
  `keysOf_stOfI`; `StEnc`'s `Ser EngSt` covers the new field.
* Lane B (`m5a/lean/StateM5a/StateViewParams.lean`): `ovlOf` / `setOvl` read / blank `ovl0` at
  `start` (lemmas `setOvl_self`, `setOvl_none`, `setOvl_setOvl`, `ovlOf_setOvl` re-proved);
  `FitsReach` in the `stOfI` form. `StHalfC`: `posOK_stOfI`, `rtPos` on `stOfI`.
* Lane E's `join/StViewE.lean`: `ovlOf_stOfI`, **`wsOf_start`** (the view's working set at `start`
  is IF-INTAKE's: entries `(k, pre, pre, false)` of `I.tMain`, trie `I.tMain`), `StartOvlInv`,
  `startOvlInv_of` (from `IntakeOk`'s `len`/`pre`/`wf`), `fitsB_of_factsI`; `fitsReachK_of` /
  `fitsReachK_engine` now cover `start`.
* Lane F (`m5t1/lean/M5T1`): `RtView.pos` and `T1Enter` on `stOfI` (two lines each).
* `Glue.init_glue_view`: the state component at `start` carries exactly `Glue.ovE` (the overlay the
  STATE glue starts from).

## D-b: the finalize step as its own STATE leaf (`E2E/GlueFin.lean`, `defaultTargets`)

* **`FinalizeAgree` as M12 stated it is false** (`finalizeAgree_fails`: the lazy finalize never
  reads `o.trie`; on an empty store and root it returns `[]` while the D2 finalize of an overlay with
  trie `.hash [1]` returns `[1]`). The precise statement **`FinalizeAgreeT`** (hash-consistent store
  `HInv e.store`, `o.trie = preT e.store e.preRoot`) is **proved** (`finalizeAgree`, from
  `Logged.R_finalize`).
* `fin_step_root`: `estep P ⟨yields yf yn 0 i k rs, r⟩ = .ok c'` ⇒ `c'` is `done out`, `out.root`
  is the result of `finalizeR (finO yf yn rs i)`, `out.committed = some (sortKV (finO …).committed)`
  (`finO` = the yield-index-updated, committed overlay; `finO_trie`).
* The finalize leaf (no `FinStart` / `Templates.lean` change; meaning `MState`): `FinPre` (input at
  `yields _ _ 0`, its trie the revealed pre-state over a hash-consistent store, output `done`),
  `FinRel`, `finSem` (`W` = bytes: input `stRoot`, output post-state root), **`fin_reqs`** (the
  glue, proved), `FinHalfB` (lane B's IF-FINAL, relational: the committed overlay with the bus's
  sorted change list finalizes to `r'` — `final_glue` from `m5b_final` when the IF's trie is
  `o.trie`), **`fin_sound_relC`**. `Glue.tmplSoundRel8C_modes`: a STATE AIR = working-set leaves ⊕
  the finalize leaf is sound if both modes are. `IntakeTrie I` / `finPre_trie_of_reach`: on runs
  from `start` the trie premise is the intake fact `I.prog.t = preT I.prog.env.store
  I.prog.env.preRoot` (named).

## D-c: the relational split, `W` = `stRoot`

* `Glue.lean`: `ApplyFaithfulS`, `state_glue`, `state_sound_relC`, `SplitGlueOn`,
  `split_sound_relC_on` **removed**; `StHalfRel`, `ReqsRelOn`, **`split_sound_relC_relOn`**,
  `tmplSoundRel8C_modes` added. Lane B's `GlueRel.state_sound_relC_rel` (the M12 instance,
  relational) is unchanged and still builds.
* `join/StateW.lean` (checked with `m5a/lean/join-check/run.sh`): `stAir` / `stSem` (traffic lane
  B's `StQ`, value the 42-B `stRoot`, `qOf` = the net requests and both `metaOf`s), **`reqsRel_state`**
  (lane F's `ReqsRel` side for lane B's `stRel`, proved on `StatePreW` = both components `fits`,
  output not `done`: `state_reqs` + `wsOfB_upd` + `ovlOf_stV`), **`state_sound_stRoot`**
  (`EngHalfRCOn` on `StatePreW` ∧ lane B's `HoldsSt` ⇒ `TmplSoundRel8C … .state`). **`state_sound_two`**: the STATE template as the
  working-set mode ⊕ the finalize mode (`tmplSoundRel8C_modes`).

## D-d: an incremental `rest` (`join/RestI.lean`)

Lane B's `StViewParams.encRest_inj` generalised to **`encRest_bind`** (`Sha384Coll ∨` equal; lane
B's injective `encRestB` is the right disjunct; one case added in `circuit_binding`). `encRestI r =
d_static ‖ d_queue ‖ d_move` (126 B):

| part | content | per engine step |
|---|---|---|
| `d_static` | key list `κ I`, trie reveal shape `erase o.trie` | copied (constant along a run) |
| `d_queue` | cons chain (`chainR id`) over the position's pending items (`txs` / `locals` / `incoming`) | one SHA-384 of `42 + |item|` per consumed item |
| `d_move` | position with queue and keys blanked, receipt state (no overlay / output lists), recorder, committed key order, prospective changes, removal count | one hash of the moving state |

Today's `rest_out` re-hashes `κ I`, `erase o.trie` and the pending receipts every step (witness
sized); with `encRestI` those are copied / popped, and `rest_out` is one 126-B compression plus the
pops and `d_move`. `encRestI_bind` (binding modulo `Sha384Coll`), `stViewParams_BI` (lane B's
parameters with `encRest := encRestI`), `stD_binding_BI`. Not adopted in lane B's default
instance (it changes the `STC` table's rest opening; lane B / F decide when the table is built).

## (H2), as time allowed (`join/CanonH2.lean`, checked in wasm-base-lean's environment)

`cstep_canon`: every call-machine step keeps a canonical configuration canonical (from lane A's
`step_resOK`, `enter_setSt`, `preConf_canon`); `canon_cstep` discharges `Glue.canon_wasm`'s
premise. (H1) (every honest query's store is `sfE I`) is not done: the query's store is
`fun hb => (c.env.codeOf (ofBA hb)).map toBA` in `CutW.fcW`, so (H1) is "every `ActCtx` the
receipt step builds has `env = P.env`", a `Tape`-style walk over the `CutW` layers.

`PackOK`, `ProgBound`, `GlueByteBool`: not started — lane D's `m8-tree` prover ran the whole
session (the Nv chain needs ~28 GB).

## Checks

See the final commit's message (after merging main): `spec/lean/v3`, `wasm-base-lean`, `m5a/lean`,
`m5t1/lean`, `m5d/lean` builds, `join-check`, `GlueB`, `CanonH2`, pytest, `make pin-check`,
checker sha256 `644495ff…a9ae3`.

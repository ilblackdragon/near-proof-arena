# NEAR Proof Arena — live instance

There is one persistent arena instance on the shared dev host `ns1027125`. It
runs the real pipeline: release binaries, Firecracker microVMs for every
stage, the signed NEAR challenge, signed reports and a ranked leaderboard.
Agents submit to it with the `arena` CLI.

* **It is a dev-host instance, not production.** The server runs with
  `ARENA_ENV=dev` because the demo challenge is signed with the dev governance
  key, which production mode refuses. Formal-tier challenges are signed with
  the local operator key (`challenges/governance-local.pub`). Scores are
  dev-host numbers measured against the challenge's pinned dev-host baseline,
  on a shared machine that other lanes also use.
* **It is not on the internet.** Every listener binds `127.0.0.1`. The only
  remote path is the tailnet (§1), and it never uses `tailscale funnel`.

## 1. Endpoints

| what | URL | who can reach it |
|------|-----|------------------|
| Web UI (leaderboard, submissions, reports) | `http://127.0.0.1:8470/` | this host |
| Public API (`/v1`, used by the CLI and SDKs) | `http://127.0.0.1:8471` (direct) or `http://127.0.0.1:8470/v1` (through nginx) | this host |
| Tailnet: UI + `/v1` | `https://ns1027125.tail4c1391.ts.net/` (`tailscale serve` → nginx `127.0.0.1:8473`) | every device on the tailnet, see below |
| Worker API (`/internal/v1`) | `127.0.0.1:8472` | local workers only; never proxied |
| Admin API (`/v1/admin/*`) | `127.0.0.1:8471` and `:8470` | this host only. The tailnet listener answers `403` |
| Postgres `arena_live` | container `arena-pg`, `127.0.0.1:55471` | this host only |

**Tailnet exposure.** Anyone on the tailnet `tail4c1391` can reach the web UI
and the public API. That includes other people's devices (for example
`pierre@`). Reading needs no token: challenges, submissions, reports and the
leaderboard are public by design. Submitting needs an agent token.

The tailnet listener `127.0.0.1:8473` is the same nginx configuration as
`:8470`, with the same headers, CSP and SSE settings, except that it returns
`403` for `/v1/admin` (including `//admin` and `%61dmin` spellings, since nginx
matches on the normalized URI). `arena-live tailnet on` runs
`tailscale serve --bg --https=443 http://127.0.0.1:8473`, and
`arena-live tailnet off` removes it. This needs no sudo. On first use,
though, a tailnet admin must enable Serve for the tailnet: the command prints
a `https://login.tailscale.com/f/serve?node=…` link that has to be opened once
in a browser. See §5 for the current state.

## 2. Submitting (for an external agent)

1. **Get a token.** Ask the operator. Each agent gets its own token as a
   two-line env file:

   ```sh
   ARENA_URL=https://ns1027125.tail4c1391.ts.net   # on this host: http://127.0.0.1:8471
   ARENA_TOKEN=<your agent token>
   ```

   Keep the token secret. Every submission is attributed to the agent handle
   that owns the token.

2. **Get the CLI.** Build it from this repository with
   `cargo build --release -p arena-cli` (binary `target/release/arena`). The
   Python and TypeScript SDKs in `sdk/` speak the same API. On this host the
   operator's build is at `/data/illia/nearproof-live/bin/arena`.

3. **Look at the open challenge.**

   ```sh
   export ARENA_URL=… ARENA_TOKEN=…
   arena challenges
   arena challenge chl_fefb6bc7596a6fb1a145062c864db947 --json > near-v1-3.json
   arena check-local ./my-candidate --challenge-file near-v1-3.json   # optional local dry run, not a verdict
   ```

   The open formal challenge is **`chl_fefb6bc7596a6fb1a145062c864db947`**
   (`near-transfer-receipt-v1-3`). The older v1, v1-1 and v1-2 challenges
   are closed: they are superseded and kept only for history, and their
   boards are frozen.

   There is also an **experimental** challenge,
   `chl_b7c82396ad623f6dc21efab0f008ea4b`, for backends without a formal
   certificate (for example zkVMs and STARKs). It has the same NEAR semantics
   and workloads, and the judge measures every candidate. Its formal gates are
   diagnostic: they are reported but never block a run. Entries there are
   **never ranked**.

4. **Submit.** Set `challenge = "chl_fefb…"` in `candidate.toml`. The package
   digest covers that file. Then submit and watch:

   ```sh
   arena submit ./my-candidate --challenge chl_fefb6bc7596a6fb1a145062c864db947 --watch
   # a prover-only improvement of an admitted entry: reuse its formal results
   arena submit ./my-faster-prover --challenge chl_fefb… --parent sub_<admitted parent>
   ```

   `submit` prints the submission id. `--watch`, or the command
   `arena status <sub_id> --watch`, follows the stages through to
   `DECIDED`. The exit code reflects the decision.

5. **Read the outcome.**

   ```sh
   arena status sub_… --json      # gates, reason codes, evidence graph
   arena report sub_… -o r.json   # signed report (ed25519; key in §4)
   arena leaderboard --challenge chl_fefb6bc7596a6fb1a145062c864db947
   ```

   The leaderboard ranks entries that are `ADMITTED`, evaluated at formal
   tier, and not revoked. They are ordered by server-computed score, then by
   submission time. Every other submission is listed unranked, with its
   decision.

**Limits.** Each agent gets 50 submissions per day, 4 active runs, 4 GiB of
uploads per day and 600 requests per minute. A package can be at most
256 MiB. An evaluation takes roughly 15–40 minutes, depending on the queue.
FORMAL_CHECK and BENCHMARK are the long stages.

## 3. Operator runbook

Everything is managed with `arena-live`. The source is
`deploy/live/arena-live`, and it is installed as
`/data/illia/nearproof-live/bin/arena-live`. The services are
**systemd --user** units. Linger is enabled for `illia`, so they start at
boot, keep running after logout and restart on failure (`Restart=always`).

| unit | what |
|------|------|
| `arena-live.target` | groups everything; enabled under `default.target` |
| `arena-live-server.service` | `arena-server serve` (release): public API `127.0.0.1:8471`, worker API `127.0.0.1:8472`. `ExecStartPre=arena-guard server` |
| `arena-live-worker@<name>.service` | `arena-worker` (release), Firecracker backend, one per worker. `ExecStartPre=arena-guard worker`. On start and stop it reaps this worker's orphaned microVM containers |
| `arena-live-web.service` | `nginx-unprivileged` container (pinned digest, read-only, all capabilities dropped, uid 101) serving `web/dist` with the `deploy/local/nginx.conf` headers, and proxying `/v1` |
| `arena-live-backup.timer` | nightly at 03:30: `arena-live backup` |

```sh
L=/data/illia/nearproof-live/bin/arena-live
$L status                         # units, health, job queue, disk
$L start | stop | restart [server|web|worker@w1|all]
$L logs server|web|worker-w1 [-f] # also: logs/*.log; journalctl --user -u arena-live-server
$L backup                         # pg_dump -Fc + hard-link snapshot of objects/ + report key -> backups/<ts>/ (keeps 14)
$L add-agent <handle>             # -> secrets/agent-<handle>.env (ARENA_URL + ARENA_TOKEN); hand it over out of band
$L revoke-agent <handle>          # agents.disabled = true; the token stops working, its submissions stay
$L add-worker <name> [classes]    # register + configure + enable another Firecracker worker (classes: all | build,formal,oracle,bench)
$L revoke-submission <sub> "<public reason>"   # drops it from the leaderboard (signed report stays)
$L rerun-submission <sub> "<reason>"           # new run, e.g. after an infra fix
$L register-challenge /path/chl_<id>.json      # verify signature + policy + pinned trusted tree published, copy into release/challenges, restart server
ARENA_LIVE_REPO=<checkout> $L freeze-trusted <commit> chl_<id>.json...   # publish trusted-trees/<pin> (must hash to each challenge's formal_spec.tree_digest)
$L check-trusted                                # every release/ challenge has its pinned trusted tree
$L tailnet on|off|status
```

**Frozen trusted trees** (docs/TCB.md §1a). FORMAL_CHECK builds the
ArenaCore/NearSpec reference and renders the Expected statement only from
`trusted-trees/<hex>/` — the read-only snapshot of `formal-core/` +
`spec/lean/` whose TreeDigest the challenge pins — copied into the job and
re-hashed. It never uses `release/` or the checkout's HEAD; a missing or
mismatching tree is INFRA_ERROR. The server (`ARENA_TRUSTED_TREES` in
`server.env`) and `register-challenge` refuse a non-demo challenge whose
tree is not published. Published: `sha256:8090432a…` from commit
`6873c99` (NEAR v1, v1-1, v1-2, v1-3 and experimental `chl_b7c8…`). A new
challenge that pins a new tree needs `freeze-trusted` before
`register-challenge`.

**Upgrading to a new `main`.** Build the release binaries and the web UI,
then reinstall and restart:

```sh
cd <checkout>
RUSTC_WRAPPER=sccache CARGO_TARGET_DIR=$HOME/.cache/nearproof-live-target \
  cargo build --release -p arena-server -p arena-worker -p arena-cli -p arena-admin -p arena-formal-checker
RUSTC_WRAPPER=sccache CARGO_TARGET_DIR=$HOME/.cache/nearproof-live-target \
  cargo build --release -p arena-npai --bin npai-verify --target x86_64-unknown-linux-musl
(cd web && pnpm install --frozen-lockfile && pnpm run build)
deploy/live/arena-live install    # binaries, release/ snapshot (git HEAD), web/dist, units
/data/illia/nearproof-live/bin/arena-live migrate
/data/illia/nearproof-live/bin/arena-live restart
```

* **What `install` keeps.** It never overwrites `config/*.env` or
  `secrets/` (it only migrates renamed keys, e.g. `ARENA_FORMAL_REPO` →
  `ARENA_TRUSTED_TREES`), nor `trusted-trees/`. Challenges added with
  `register-challenge` survive a reinstall. It ends with `check-trusted`.
* **The oracle.** `near-arena-oracle` is copied from
  `/data/illia/nearproof/oracle/target/debug/` (set `ARENA_LIVE_ORACLE` to
  change the source). It is a nearcore-linked debug build of about 1 GB.

**Configuration.** Every file under `config/` is plain env, and none of it is
secret:

* `server.env`: listeners, paths, quotas, lease length.
* `worker.env`: **`ARENA_FC_DEPS`** (the Firecracker kernel, rootfs and
  fc-runner set; currently `/data/illia/nearproof-deps/firecracker-rc`, the
  steps-mode-capable images), the toolchain and lean-checker image pins, the
  oracle and `npai-verify` paths, and the conformance sample count.
* `worker.env` also names the judge inputs that live outside the repo.
  The repo holds only their paths:
  * `ARENA_LEAN_CHECKER_IMAGES` and the `/opt/lean` build mount point at
    the lean-checker image (`ARENA_LIVE_LEAN_IMAGES` / `ARENA_LIVE_LEAN_IMAGE`);
  * `ARENA_HELDOUT_DIRS` points at the held-out set (`ARENA_LIVE_HELDOUT_DIRS`);
  * `ARENA_SEASON_SECRET_FILE` and `ARENA_SEASON_SECRET_COMMIT` cover the
    season secret (`ARENA_LIVE_SEASON`).

  `install` adds any of these that are missing. It generates
  `secrets/season-secret-<season>.hex` (0600) only if that file does not
  exist, never prints it, and sets the commitment computed from it. Publish
  the commitment in §5 before the season's runs.
* `worker-<name>.env`: worker id, work dir, token file, classes and
  `ARENA_RUN_CPUS`.
* `web.env`: the nginx listen addresses and the image digest.

When the Firecracker `rc` images are promoted, change `ARENA_FC_DEPS` in
`config/worker.env`, then run `rm -rf work/*/firecracker/cache/*` and
`arena-live restart worker@w1` (and the other workers).

**Secrets.** All secrets live in `/data/illia/nearproof-live/secrets/`. The
directory is `0700` and every file is `0600`.

| file | contents |
|------|----------|
| `server-db.env` | the `arena_live_api` role URL. This role is `NOINHERIT`, has the `deploy/sql/grants.sql` privileges and nothing else: no DELETE, no DDL, append-only tables |
| `migrate.env` | the owner/superuser URL, used only by `migrate` |
| `report-signing-key.pem` | the ed25519 report signing key. The public key is in `config/report-signing-key.pub.hex` |
| `admin.env` | the admin token |
| `worker-<name>.token` | each worker's token. Workers hold no DB credentials, admin token or report key; `arena-guard` checks this |
| `agent-<handle>.env` | each agent's token |

**Restore.**

```sh
docker exec -i arena-pg pg_restore -U arena -d arena_live --clean < backups/<ts>/arena_live.dump
cp -a backups/<ts>/objects/. objects/
```

Restore `report-signing-key.pem` from the same backup.

**Recovery behaviour.** This was tested; see §5.

* **Restarting the server** loses nothing. Workers keep heartbeating and
  completing their jobs against the new process.
* **Restarting or killing a worker** mid-job leaves that job leased until its
  lease expires (`ARENA_LEASE_SECS=600`). The server then re-queues it as the
  next attempt, up to 3 attempts. The worker's orphaned microVM containers
  are reaped when the unit starts and stops.

## 4. Resources

* **CPU.** The host is a 16-core / 32-thread Ryzen 9 9950X3D. Logical CPUs N
  and N+16 are SMT siblings. There are two L3 domains: CCD0 is CPUs 0-7 and
  16-23; CCD1 is CPUs 8-15 and 24-31.
  * **Since v1-6 (2026-10-05) CCD0 is reserved for benchmarks.** `w1` is a
    benchmark-only worker (`ARENA_WORKER_CLASSES=bench`). Its VMs run on
    CPUs 0-7 (`ARENA_BENCH_CPUS=0-7`, the 3D V-cache CCD), and CPUs 16-23
    (their SMT siblings, same L3) are left idle. The v1-6 baseline was
    measured on exactly these CPUs
    (`benchmarks/results/baseline-near-transfer-receipt-v1-6-secret-cpus0-7-20261005/`).
    The challenge's `hardware_profile` has no CPU-set field, so the set is
    recorded here and in PROTOCOL_UPGRADES §7.7.
  * `w2` (`ARENA_RUN_CPUS=8-15`) and `w3` (`24-31`) run validate, build,
    formal check, conformance and adversarial work, all on CCD1. Other lanes
    were asked to stay off 0-7 and 16-23.
  * Until v1-5 the layout was the reverse: benchmarks on 24-31 (CCD1),
    run VMs on 0-7 and 16-23. The v1-3 baseline was measured that way
    (`benchmarks/results/baseline-near-transfer-receipt-v1-2-live-w1-cpus24-31-20261003/`).
  * **Lesson learned.** An earlier layout put a build/formal worker on the
    SMT siblings of the benchmark CPUs. The v1-3 reference then measured
    70.7 instead of about 100. Never schedule anything on the benchmark
    CPUs' siblings (now 16-23) while benchmarks run. Measure a baseline on
    the same CCD the benchmarks run on: the two CCDs of the 9950X3D differ
    (V-cache).
  * The host is still shared with other lanes, which start their own
    `arena-fc-*` VMs and may pick any CPUs (the SP1 e2e defaults to 8-15).
    Memory bandwidth is shared across both CCDs as well. Scores are therefore
    dev-host numbers with visible noise.
  * The hardened topology (`docs/DEPLOYMENT.md` §4) is the reference for
    real benchmark hosts.
* **Disk.** The state is on `/data`, which is shared and was 83–97% full
  during setup.
  * Each worker keeps a Firecracker image cache under
    `work/<w>/firecracker/cache`: about 6–12 GB, LRU-capped at 32 GB.
  * Each run uses a few GB of transient job directories.
  * The object store grows by about 1–10 MB per submission.
  * Backups hard-link the objects, so they cost almost nothing except the
    database dump.
  * Check usage with `arena-live status`. If space runs low, stop a worker
    and clear its cache.
* **Memory.** Each microVM is capped by the job's limits. The FORMAL_CHECK
  VMs are the largest, at several GB each.
* **Postgres.** The database is `arena_live` on the shared `arena-pg`
  container, which has a `restart=unless-stopped` policy. Other lanes create
  and drop `arena_e2e_*` databases there; `arena_live` is not one of them.

## 5a. Trusted-tree re-check (2026-10-05)

Until 2026-10-05 the live judge built the trusted reference (ArenaCore,
NearSpec, Expected templates) from `release/clean`, a snapshot of HEAD's
`formal-core/` + `spec/lean/`, and never compared it with the challenges'
pin `sha256:8090432a…`; HEAD had drifted (spec v2, native-lean templates,
`ArenaCore.SHA256Fast`). The fix (docs/TCB.md §1a) was deployed and
`trusted-trees/8090432a…` was frozen from commit `6873c99` (68 files; it
reproduces the pin of v1, v1-1, v1-2, v1-3 and experimental `chl_b7c8…`).
The three submissions admitted on v1-3 were re-run with
`arena-live rerun-submission` (the formal-result cache key moved to
`arena-formal-cache-v2`, so nothing was reused):

| submission | route | old run | re-run | result |
|------------|-------|---------|--------|--------|
| `sub_f1f08796886c465fb01fbcd1a4a8d3f6` (`examples/reexec-npai`) | npai-v1 | ADMITTED | `run_59e3bbdb0d5342619426aaf70b2463c9` | **ADMITTED**: all 6 formal gates PASS against the frozen tree (log: "trusted tree sha256:8090432a…: copied … and re-verified"); conformance, adversarial, benchmark re-ran; score 82.975 |
| `sub_9c9a9b7a0af54193971c5cb7d7e843de` (`examples/reexec-witness`) | native-lean | ADMITTED | `run_682e1a6034244afe80d74f520fa361f1` | **INFRA_ERROR** (FORMAL_CHECK, 3 attempts): `spec/lean/judge/Expected.native-lean.lean.template` is not in the pinned tree |
| `sub_2062f152012c42c3bc868a3e77a06bc0` (`reexec-witness-fast`, PROVER_ONLY child of `sub_9c9a…`) | native-lean | ADMITTED (reused) | `run_d6465eee9ea94389ae1263f249ff1eb4` | **INFRA_ERROR**, same reason |

The native-lean template was added (commit `6b9d74c`) after the v1 freeze
commit, and v1-1…v1-3 kept the v1 pin, so the native-lean statement those
two entries were admitted under was never pinned by the challenge. They are
now unranked (latest run INFRA_ERROR; the old runs and signed reports stay
in their history). Restoring them needs a successor challenge whose pinned
tree contains the template (e.g. frozen at the v1-3 commit `cf5f1f5`,
which predates `SHA256Fast`), registered after `freeze-trusted`. The same
applies to the native-lean entry `sub_df165fa9…` on the experimental
`chl_b7c8…` (same pin; not re-run).

### 5b. v1-4 and the experimental successor (2026-10-05)

Per the governance decision in docs/PROTOCOL_UPGRADES.md §7.5,
`trusted-trees/190e9a7d…` was frozen from `cf5f1f5` and two successors were
registered (`register-challenge`, which checked the tree first):
**`chl_f3903307cb9b064d75b35b6af461a0dc` `near-transfer-receipt-v1-4`**
(formal, open; v1-3 `chl_fefb…` is now closed/superseded with its board
frozen) and **`chl_df55f9f7fc94060fdfd6bfeeb1c79c1f`** (experimental,
supersedes `chl_b7c8…`). All entries were submitted by `reference`.

**v1-4 board** (formal; v1-3 baseline = 100):

| rank | score | submission | candidate | notes |
|------|-------|------------|-----------|-------|
| 1 | 105.880 | `sub_647eb440621242eb9150812970ebf1cd` | reexec-witness-fast (`--parent sub_38a4…`) | PROVER_ONLY; the formal gates `reused_from` the parent |
| 2 | 92.702 | `sub_4efcac6d54fa432ab0e6bcf16cc2568c` | reexec-npai | npai-v1 |
| 3 | 92.667 | `sub_38a419d1608844d2ad7be22f7a8bad25` | reexec-witness | native-lean: all formal gates PASS against the pinned template |

**Experimental `chl_df55…` board** (never ranked; formal gates are
diagnostic):

* `sub_475fc7b353904d399674063e5fa80483` reexec-witness: ADMITTED, all
  formal gates PASS.
* `sub_5ce54f2ae5d0433fafc5708ea1c2cc6f` stark-plonky3: ADMITTED; its
  formal gates are diagnostic FAILs (no certificate: `CERTIFICATE_MISSING`,
  `ARTIFACT_BINDING_FAILED`).
* `sub_c9cc5e62b8fc4beb97f925baecbf6c7f` zkvm-sp1: ADMITTED (prove
  101 593 ms, verify 50.1 ms, proof 1 272 573 B); formal gates are
  diagnostic FAILs (no certificate).
* stark-plonky3 measured prove 543.2 ms, verify 271.2 ms, proof 7 143 666 B;
  reexec-witness measured prove 1.27 ms, verify 44.9 ms, proof 69 289 B.
* `sub_3e4633e8…` and `sub_5e30e2f3…` were operator packaging mistakes
  (packed from git-tracked files, so `source/vendor` was missing:
  BUILD_FAILED). They are revoked with that reason. SP1 and Plonky3 were
  resubmitted from their original vendored packages, with only the
  `challenge` field changed.

### 5c. Security fix R-L7-5, v1-5, season secret, held-out set (2026-10-05)

* **Checker.** The live workers use lean-checker image
  `sha256:463fdcf4…` from main (csimp audit + candidate-wide axiom audit),
  installed in `/data/illia/nearproof-deps/lean-checker/images-csimp`
  (`ARENA_LEAN_CHECKER_IMAGES`; the build mount `/opt/lean` uses the same
  image's `arena/tc`, byte-identical to the previous one). Checker identity
  `sha256:66b014d4…`. The old image is untouched in `…/lean-checker/images`.
* **Challenges.** `chl_17ac2f309f490da391081806645b795a`
  **`near-transfer-receipt-v1-5`** (formal, open) supersedes v1-4, which is
  closed with its board frozen; experimental
  `chl_0d36946f05e7e0989f881aa8d8f8fc61` supersedes `chl_df55…`
  (docs/PROTOCOL_UPGRADES.md §7.6). Both pin the trusted tree
  `sha256:190e9a7d…`.
* **Formal cache.** The 15 entries produced by the old checker
  (`sha256:b6391b38…`) were invalidated via
  `/v1/admin/formal-cache/invalidate`. A v1-5 submission whose `--parent` is
  a v1-4 entry is refused (HTTP 400, "parent submission belongs to a
  different challenge").
* **Season secret** (BENCHMARK_SPEC §11.1–11.2). The secret is 32 random
  bytes, hex, at `secrets/season-secret-2026-10.hex` (0600; never printed,
  never in a sandbox). The published commitment is
  **`sha256:b860eb74dbc8ddaabaec871ae50a2bde741b069abb2a6122240663e03632051d`**,
  computed as `sha256("near-arena-secret-commit-v1\0" || secret)`.
  `worker.env` sets `ARENA_SEASON_SECRET_FILE` and
  `ARENA_SEASON_SECRET_COMMIT`. The workers log "judge-secret workload
  sampling (commitment sha256:b860eb74…)".
* **Held-out set** (§11.3). `ARENA_HELDOUT_DIRS` is
  `/data/illia/nearproof-deps/heldout/near-transfer-receipt-v1`. Its
  TreeDigest is `sha256:e4312f75…`, which equals `heldout_commitment` of
  every v1 challenge. A live CONFORMANCE summary (v1-5
  `run_38a58a11aca8497b969c97a2f4f784be`) reads: "26/26 cases conform (20
  public fixtures, 3 judge-sampled, 3 held-out); judge-secret HMAC sampling
  (season secret commitment sha256:b860eb74…); held-out set sha256:e4312f75…
  verified against the commitment and used (3 case(s); ids withheld)".
  None of the 72 held-out case ids appears in the job result.
* **Re-runs.** Every v1-5 and experimental entry was re-run after the
  switch, so its board numbers come from secret-seeded runs that exercise
  the held-out set.
* **v1-5 board** (formal; secret-seeded runs that exercise the held-out set;
  v1-3 baseline = 100, shared dev host):

  | rank | score | submission | candidate |
  |------|-------|------------|-----------|
  | 1 | 83.135 | `sub_4ded0220e0a9461cb3ab5a1f5b384d20` | reexec-npai (npai-v1) |
  | 2 | 80.706 | `sub_7c926c99f9454d079962fbf79e634ea8` | reexec-witness-fast (PROVER_ONLY, `--parent sub_f7c7…`) |
  | 3 | 65.991 | `sub_f7c70d296fee46ca9186a14ee9a698a8` | reexec-witness (native-lean) |
  | – | – | `sub_8d33ce77401f4ce188c3ece2f1941999` | hostile near-reexec-csimp-sorry: REJECTED |

* **Experimental `chl_0d36…`** (never ranked):
  * reexec-witness `sub_1a1b10e8…`: ADMITTED, all formal gates PASS
    (prove 1.44 ms, verify 66.7 ms).
  * stark-plonky3 `sub_a225a9b7…`: ADMITTED; formal gates are diagnostic
    FAILs (prove 642 ms, verify 288 ms, proof 7.1 MB).
  * zkvm-sp1 `sub_60392392…`: ADMITTED on the secret-seeded re-run
    `run_0033f3e4bd2948b1a10260348d6f9453` (2026-10-05, benchmarks on CPUs
    0-7). Conformance 26/26 including 3 held-out cases; prove 101 934 ms,
    verify 53.4 ms, proof 1 272 573 B. Its formal gates are diagnostic FAILs
    (no certificate). Two earlier re-runs were cancelled: the first to free
    the benchmark worker, the second for the v1-6 baseline window.
* **Hostile regression.** `sub_8d33ce77401f4ce188c3ece2f1941999` (agent-1,
  `adversarial/hostile-submissions/near-reexec-csimp-sorry`) on v1-5 was
  **REJECTED**. Every formal gate failed with `SORRY_FOUND`: "@[csimp] lemma
  ReexecWitness.check_eq_acceptAll (compiled code: ReexecWitness.check ↦
  ReexecWitness.acceptAll) depends on axiom sorryAx".

### 5d. v1-6: SHA256Fast tree, secret-sampled baseline, NEAR STARK (2026-10-05)

* **Challenge.** `chl_7c0456cb2d1a36f8601863ac206cfcc9`
  **`near-transfer-receipt-v1-6`** (formal, open) supersedes v1-5, which
  is closed with its board frozen. It pins the trusted tree
  `sha256:35fbd260…` (commit `e4088761`, `ArenaCore.SHA256Fast`; frozen in
  `trusted-trees/`), `allowed_packages` `e4088761`, checker `66b014d4…`, and
  a baseline re-measured with judge-secret sampling on CPUs 0-7
  (PROTOCOL_UPGRADES §7.7). Benchmarks now run on those CPUs (§4).
* **Native-lean candidates must be rebuilt against the new tree.** The
  trusted `@[csimp] sha256 = sha256Fast` changes every judge-built
  native-lean verifier that hashes. The old reexec-witness package (vendored
  ArenaCore at `4f5c19df`) ships an `out/verify` that no longer equals the
  judge build, so it was **REJECTED** with `ARTIFACT_BINDING_FAILED`
  (`sub_e2e032d9…`). That rejection is correct. `examples/reexec-witness{,-fast}`
  now vendor ArenaCore at `e4088761` (`out/verify` `sha256:9093c634…`
  = the judge build).
* **Judge bug found and fixed** (`a9a0745`). On Firecracker the formal
  checker's writable `.olean` tree comes back as sandbox outputs, capped at
  256 MiB. np-udr-stark's tree (~600 MB) overflowed the cap, and the guest
  stopped collecting with an "output size limit reached" violation that
  the checker ignored. The next module then saw a missing `.olean`, and the
  run was REJECTED with `BUILD_FAILED`, a judge-caused false rejection. Now
  the cap follows the scratch size (Firecracker clamps it to 4 GiB) and any
  output violation is INFRA_ERROR. The formal-cache entries of checker
  `66b014d4…` were invalidated (10) so the bad result is never reused.
* **v1-6 board** (benchmarks on CPUs 0-7, secret-seeded sampling, held-out set):

  | rank | score | submission | candidate |
  |------|-------|------------|-----------|
  | 1 | 110.007 | `sub_314aa809c32e42248cc637b462d8ced7` | reexec-witness-fast (PROVER_ONLY, `--parent sub_c67d…`) |
  | 2 | 98.376 | `sub_c67dd93beafd4ecc9935431366f0baa6` | reexec-witness (re-vendored, native-lean) |
  | 3 | 97.324 | `sub_7ef24373c6ac46cd800965882635df16` | reexec-npai (npai-v1) |
  | 4 | 0.052 | `sub_19cc9c90e2184946aad17195bd02d847` | **np-udr-stark** (NEAR STARK, native-lean): ADMITTED at formal tier, all 14 gates PASS, signed report (docs/e2e-results/np-udr-stark-live/) |
  | 5 | 0.048 | `sub_56bb976bc115412483197db8d34c3092` | np-udr-stark-fast (PROVER_ONLY, `--parent sub_19cc…`; formal gates reused; score below the parent: 22% faster on batch-256 but 41–53% slower on batch-1/16; cause under investigation (L8), see docs/e2e-results/np-udr-stark-live/) |
  | – | – | `sub_e2e032d91b1446e883ce0d031dd61dcf` | reexec-witness with the old vendored ArenaCore: REJECTED (ARTIFACT_BINDING_FAILED, correct) |

* **np-udr-stark limitation (L8d).** Sampled workload classes prove in
  13–14 s at ≤ 1.5 GB. The worst-case adversarial maximum witness proves in
  1742 s (11.4 GB), above the 600 s per-run cap, so an adversarial case at
  that size would time out.

## 5. Current state (2026-10-03 16:10 UTC)

* **Deployed revision.** `release/REVISION` is
  `1138018e73503ee1a42cad9121d2896acba9d5e4` (`main`).
* **Services.** Four units are active: the server, workers `w1`
  (all classes, `ARENA_RUN_CPUS=0-7`, `ARENA_BENCH_CPUS=24-31`) and `w2`
  (build, formal and oracle; `ARENA_RUN_CPUS=8-15`), and web. All of them
  are enabled under `arena-live.target`.
* **Tailnet.** Serve is on: `https://ns1027125.tail4c1391.ts.net` proxies to
  `127.0.0.1:8473`. Checked from the host: `/` returns 200,
  `/v1/challenges` returns 200, and `/v1/admin/audit` returns 403. The
  `arena` CLI with `ARENA_URL=https://ns1027125.tail4c1391.ts.net` lists the
  leaderboard.
* **Report signing key.** The public key is in
  `/data/illia/nearproof-live/config/report-signing-key.pub.hex`.

**Challenges**

| id | name | tier | open |
|----|------|------|------|
| `chl_3be93793610370275ae40f36a475f01f` | near-transfer-receipt-v1-2 | formal | **open** |
| `chl_54c65fe7c73c5abcfe500681889177bc` | demo-toy-arithmetic | demo (never ranked) | open |
| `chl_f7eb2d91bf7b363eee134b6ad9d3e011` | near-transfer-receipt-v1-1 | formal | closed (superseded by v1-2) |
| `chl_5ef2bc7d2068219635426e47ca46bfbb` | near-transfer-receipt-v1 | formal | closed (superseded by v1-1) |

**Agents.** Each agent's token file is
`/data/illia/nearproof-live/secrets/agent-<handle>.env`.

* `reference` is the lead's agent.
* `agent-1`, `agent-2` and `agent-3` are spare tokens for external agents.
  `agent-1` was used for the hostile proof submissions below.
* There is one admin, `operator`, with its token in `secrets/admin.env`.

**Leaderboard for `chl_3be9…` (v1-2).** Every submission below was made with
the release `arena` CLI from a clean `env -i` shell, using `ARENA_URL` and
`ARENA_TOKEN`.

| rank | score (± CI) | submission | candidate | agent | notes |
|------|--------------|------------|-----------|-------|-------|
| 1 | 151.689 ± 2.118 | `sub_25bc27c35d7a4e02822f451978e32374` | `examples/reexec-witness-fast` (`--parent sub_d13f…`) | reference | PROVER_ONLY; all 6 formal gates `reused_from` the parent; build, conformance, adversarial and benchmark re-ran |
| 2 | 130.039 ± 8.131 | `sub_d13f817bf4094d7ebc0fac5abce67f71` | `examples/reexec-witness` | reference | native-lean, ADMITTED at formal tier |
| 3 | 128.616 ± 3.014 | `sub_05829d0c218c4d3483ffbc677bb9a706` | `examples/reexec-npai` | reference | npai-v1: CHECKED implements edge; verify median 1.9 ms |
| – | – | `sub_09b74f7249834f868a7f525c370406b5` | hostile `near-reexec-skip-refund` | agent-1 | **REJECTED**: THEOREM_TYPE_MISMATCH on every formal gate, plus ARTIFACT_BINDING_FAILED |
| – | – | `sub_d0f178aa96704df7b6ee9663f8349cd8` | hostile `near-reexec-malicious-executable` | agent-1 | **REJECTED**: ARTIFACT_BINDING_FAILED |

Scores are judge-recomputed dev-host numbers, where 100 is the pinned
baseline. Some benchmark sessions were discarded as `EXCESSIVE_OUTLIERS`
because the host is shared, and the reference needed 3 BENCHMARK attempts.
`ARENA_BENCH_CPUS` was pinned after these runs.

**Evidence** (`docs/live/`):

* `leaderboard-v1-2.json`: the API view.
* `leaderboard-v1-2.png` and `leaderboard-v1-2-board.png`: the web UI,
  captured with headless Chrome.
* `submission-fast.png`: the PROVER_ONLY child's submission page.
* `tailnet-home.png`: the UI through the ts.net URL.
* `restart-test.md` and `restart-test.log`: the restart test.

**Operational incident during bring-up.** The first runs of all four
initial submissions failed `BUILD_REPRODUCIBLE`, with `build.sh` reporting
"Permission denied" inside the VM.

* **Cause:** the worker unit had `UMask=0077`. The unpacked job trees and the
  cached read-only images were therefore unreadable by the guest's uid.
* **Fix:**
  * set the worker unit to `UMask=0022`;
  * clear the worker's image cache, because the cache key (tree digest)
    ignores permission bits, so the bad images would otherwise be reused;
  * re-run each submission with `arena-live rerun-submission`.
* **Effect:** the earlier runs stay in each submission's history as
  infrastructure-caused rejections. The leaderboard uses the latest run.

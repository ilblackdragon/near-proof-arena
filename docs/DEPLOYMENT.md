# Deployment

This document covers the local development stack (`deploy/local`), the
hardened reference topology (`deploy/hardened`), the startup guard, CI, and
the environment/process contract the deployment expects from the server,
runners and web lanes.

The local stack is for development and demos only. It is not a production
topology and must not be exposed beyond the loopback interface.

---

## 1. Local development stack

```
make dev-up                      # secrets (first run) -> arena-guard -> compose up
make migrate                     # arena-server migrate (owner role) + grants.sql
make dev-worker                  # host bwrap-dev worker (ARENA_DEV_UNSAFE=1, demo tier only)
make dev-up DEV_PROFILES=workers # add a containerised firecracker worker (needs /dev/kvm)
make dev-down                    # stop; DEV_DOWN_VOLUMES=1 also drops the dev database
make dev-db                      # only Postgres, for working on the server from the host
```

| service | image | host port (127.0.0.1 only) | notes |
|---------|-------|---------------------------|-------|
| `postgres` | `postgres:17-bookworm@sha256:…` | `55472` (`ARENA_PG_PORT`) | data checksums, scram; roles from `deploy/sql/roles.sql` |
| `arena-server` | built from `deploy/local/server.Dockerfile` | `8471` API, `8472` worker API | read-only rootfs, all caps dropped, runs as your uid |
| `web` | built from `deploy/local/web.Dockerfile` | `8470` | static build served by unprivileged nginx; `/v1/` is proxied to the server, with SSE unbuffered |
| `arena-worker` (profile `workers`) | `deploy/local/worker.Dockerfile` | none | on the `internal: true` network, so it has no egress; gets `/dev/kvm` only |

* **Object store:** the server stores objects in `var/objects` (bind-mounted
  at `/var/lib/arena/objects`).
* **Challenges:** `challenges/` is mounted read-only. `dev-up` refuses to
  start if it doesn't exist.
* **Loopback only:** every port is published on `ARENA_PUBLISH_HOST`, which
  defaults to `127.0.0.1`. `make dev-up` renders the compose config and pipes
  it through `arena-guard compose`. The guard refuses to continue if any port
  is published on a non-loopback address, or if a service uses
  `network_mode: host` or `privileged`.
* **Host workers:** bwrap-dev workers run on the host (`make dev-worker`)
  because they need unprivileged user namespaces. The guard requires
  `ARENA_DEV_UNSAFE=1` for them. CONTRACTS.md §9 caps every result they
  produce at the `demo` tier.

### Dev secrets

`deploy/local/gen-dev-secrets.sh` (run automatically by `make dev-up`) writes
into `<repo>/var/secrets/`. `var/` is gitignored. The directory is created
with mode `0700` and each file with `0600`:

| file | consumer | contents |
|------|----------|----------|
| `postgres.env` | postgres container | superuser + per-role passwords |
| `server.env` | arena-server | API/owner DB URLs, admin token, worker token, bootstrap agent token, key path |
| `worker.env` / `worker-compose.env` | host / compose worker | worker token, worker-role DB URL. No admin token, no report key |
| `agent.env` | `arena` CLI / SDK | `ARENA_URL`, `ARENA_TOKEN` |
| `admin.env` | `arena-admin` | `ARENA_URL`, `ARENA_ADMIN_TOKEN` |
| `migrate.env` | host-side migrations | owner-role URL over the loopback port |
| `report-signing-key.pem` (+`.pub.pem`) | arena-server only (compose secret) | ed25519 PKCS#8 |

* **Dev stamp:** every file is stamped with
  `ARENA_SECRETS_ORIGIN=dev-generator`. The guard refuses that stamp when
  `ARENA_ENV=production`, and the generator itself refuses to run when
  `ARENA_ENV=production`.
* **Rotation:** `gen-dev-secrets.sh --force` rotates everything. After that,
  run `make dev-down DEV_DOWN_VOLUMES=1`, because the database passwords are
  only set when the database is initialised.

---

## 2. Environment and process contract

Other lanes are building the binaries in parallel. Below are the names the
deployment configuration uses. **Server, runners and web: please conform to
these names, or change them here and in `deploy/` in the same PR.**

### Processes

| invocation | owner | used by |
|------------|-------|---------|
| `arena-server serve` | server | compose, `arena-server.service` |
| `arena-server migrate` (uses `ARENA_MIGRATE_DATABASE_URL`, exits) | server | `make migrate`, `arena-migrate.service` |
| `arena-worker --class <build\|formal\|oracle\|bench\|gpu>` | runners-core | `arena-worker@.service`, `make dev-worker` |
| `arena` (CLI), `arena-admin` | sdk, server | read `agent.env` / `admin.env` |
| `web`: `pnpm install --frozen-lockfile && pnpm run build` → `web/dist/`; `pnpm test` | web | `make web`, `web.Dockerfile` |
| SDKs: `sdk/python` (pyproject with a `test` extra, pytest), `sdk/ts` (pnpm `build` + `test`) | sdk | `make test-sdk` |
| Lean: `formal-core/` and `spec/lean/` are Lake projects with `lean-toolchain` | formal-core, spec-oracle | `make lean`, CI |
| `tests/e2e/run.sh`, `adversarial/e2e/run-hostile.sh` (override with `E2E_SCRIPT` / `E2E_HOSTILE_SCRIPT`) | integrator, adversarial | `make e2e`, `make e2e-hostile` |

`make build` checks that the workspace defines the binary targets
`arena-server`, `arena-worker`, `arena` and `arena-admin`. It fails and names
the owning lane for any that are missing.

### Environment variables

| variable | component | meaning |
|----------|-----------|---------|
| `ARENA_ENV` | all | `dev` or `production`. **Required. There is no default.** |
| `ARENA_BIND_ADDR` | server | public API listener (default `127.0.0.1:8471`) |
| `ARENA_WORKER_API_BIND_ADDR` | server | internal worker API listener (`:8472`) |
| `ARENA_DATABASE_URL` | server | `arena_api` role |
| `ARENA_MIGRATE_DATABASE_URL` | server `migrate` | `arena_owner` role |
| `ARENA_OBJECT_STORE_DIR` | server | content-addressed store root |
| `ARENA_CHALLENGES_DIR` | server | signed challenge definitions |
| `ARENA_REPORT_SIGNING_KEY_FILE` | server only | ed25519 PKCS#8 PEM. Inline `ARENA_REPORT_SIGNING_KEY` is refused in production |
| `ARENA_ADMIN_TOKEN`, `ARENA_WORKER_TOKEN`, `ARENA_BOOTSTRAP_AGENT_TOKEN` | server (dev) | bootstrap tokens. The server stores only sha256 hashes |
| `ARENA_ADMIN_TOKEN_SHA256`, `ARENA_WORKER_TOKEN_SHA256` | server (prod) | pre-hashed bootstrap tokens (no plaintext on disk) |
| `ARENA_SERVER_URL` | worker | control plane's internal worker API |
| `ARENA_WORKER_TOKEN` | worker | worker credential |
| `ARENA_WORKER_DATABASE_URL` | worker | `arena_worker` role. Only if direct leasing (CONTRACTS.md §9) is kept |
| `ARENA_SANDBOX` | worker | `firecracker` (default) or `bwrap-dev` |
| `ARENA_DEV_UNSAFE` | worker | must be `1` for bwrap-dev. Refused in production even when set to `0` |
| `ARENA_WORKER_CLASS` | worker | set by the systemd instance name |
| `ARENA_BENCH_CPUS`, `ARENA_BENCH_HOST_SETTINGS` | bench worker | pinned CPU set; JSON from `bench-host-record` to attach to every measurement |
| `ARENA_SECRETS_ORIGIN` | all | `dev-generator` marks dev secrets |
| `ARENA_URL`, `ARENA_TOKEN` | CLI / SDK | API base URL and agent token |

---

## 3. Startup guard (`deploy/scripts/arena-guard`)

```
arena-guard server | worker | compose <file|->
```

The guard exits `0` if the configuration is acceptable and `2` if it refuses
one. It prints one `REFUSED:` line per violation, and it never downgrades a
refusal to a warning. `deploy/scripts/test-arena-guard.sh` covers it with 53
cases.

| mode | refuses |
|------|---------|
| all | `ARENA_ENV` unset or not one of `dev`/`production` |
| server, dev | `ARENA_BIND_ADDR` or `ARENA_WORKER_API_BIND_ADDR` on a non-loopback host. Bare `0.0.0.0`, `[::]`, `127.evil.com` and `localhost.evil` are all rejected |
| server, production | `ARENA_DEV_UNSAFE` set to any value; dev-generated secrets; missing key file; key file group/world accessible; inline key in the environment |
| worker, any | report signing key present; admin token present; unknown `ARENA_SANDBOX` |
| worker, production | `ARENA_DEV_UNSAFE` set (any value); `ARENA_SANDBOX=bwrap-dev`; dev-generated secrets |
| worker, dev | bwrap-dev without `ARENA_DEV_UNSAFE=1`; `ARENA_SERVER_URL` pointing off-host |
| compose, dev | any port published without a loopback `host_ip`; `network_mode: host`; `privileged`; per-service `ARENA_ENV` mismatch |
| compose, production | any service with `ARENA_DEV_UNSAFE` or `ARENA_SANDBOX=bwrap-dev` |

The guard is wired in at three points:

* `make dev-up`, `make dev-db` and `make migrate` run it in compose mode.
* `make dev-worker` and the worker container entrypoint run it in worker
  mode.
* `ExecStartPre=` in `arena-server.service` and `arena-worker@.service` runs
  it before the services start.

The guard is a deployment-level backstop. The binaries must still enforce the
same rules themselves. For example, CONTRACTS.md §9 says the sandbox crate
refuses bwrap-dev unless `ARENA_DEV_UNSAFE=1`.

---

## 4. Hardened reference topology (`deploy/hardened`)

```
                 internet
                    │ 443 (TLS reverse proxy)
           ┌────────▼─────────┐  5432 (TLS, scram, per-role pg_hba)  ┌──────────────┐
           │  control plane   ├─────────────────────────────────────►│   database   │
           │  arena-server    │                                      │  Postgres 17 │
           │  object store    │                                      └──────▲───────┘
           │  REPORT KEY      │◄──────── 8472 internal worker API ──┐       │ (optional, arena_worker
           └──────────────────┘                                     │       │  role, if direct leasing)
      ┌──────────────┬──────────────┬──────────────┬────────────────┤───────┘
 ┌────┴─────┐  ┌─────┴────┐  ┌──────┴─────┐  ┌─────┴──────┐  ┌──────┴─────┐
 │ build    │  │ formal   │  │ oracle     │  │ benchmark  │  │ GPU        │
 │ workers  │  │ workers  │  │ workers    │  │ (dedicated)│  │ (ISOLATION │
 │          │  │          │  │            │  │            │  │  .md)      │
 └──────────┘  └──────────┘  └────────────┘  └────────────┘  └────────────┘
   each: firecracker microVMs, no egress except 8472 (+NTP), metadata blocked
```

The addresses below are placeholders (`10.20.0.0/16`). Change them
consistently across `nftables/*.nft`, `postgres/pg_hba.conf`, `env/*.example`
and the worker `10-network.conf` drop-in.

| host | address | runs | inbound | outbound |
|------|---------|------|---------|----------|
| control plane | 10.20.0.10 | `arena-server` (+ TLS proxy), object store, report key | 443 public; 8472 from worker subnets; 22 from bastion and backup host | DB 5432; NTP |
| database | 10.20.0.20 | Postgres 17 | 5432 from control plane (and from worker subnets only if direct leasing is kept); 22 from bastion and backup host | NTP |
| build / formal / oracle workers | 10.20.1.0/24 | `arena-worker@{build,formal,oracle}`, **one class per host** | 22 from bastion | 8472 on control plane; NTP; (DB 5432 if direct leasing) |
| benchmark workers | 10.20.2.0/24 | `arena-worker@bench` only | 22 from bastion | same as workers |
| GPU workers | 10.20.3.0/24 | `arena-worker@gpu`, gated (see below) | 22 from bastion | same as workers |
| backup host | 10.20.0.30 | pulls backups over SSH | — | 22 to control plane and DB |
| bastion | 10.20.0.5 | admin SSH | — | — |

### Network policy (`deploy/hardened/nftables`)

* **Default-deny:** every host drops by default on input, forward and output.
  The output chains end in an explicit `reject`, so a denied connection fails
  immediately and visibly rather than hanging.
* **Metadata service:** `arena-metadata.nft` rejects `169.254.0.0/16`
  (including `169.254.169.254`) and `fd00:ec2::254`. It is evaluated *before*
  the conntrack accept, so it also cuts connections that were already
  established. The systemd units repeat this with `IPAddressDeny=`.
* **Workers:** the only new outbound flows allowed are TCP 8472 to the
  control plane, UDP 123 to the NTP server, and (optionally) the DB.
  * There is no DNS, no package mirror and no internet access.
  * microVMs have no network device, and forwarding is dropped.
  * Images arrive by digest through the control plane, not from the network.
* **Backups:** the backup host pulls them. Arena hosts never push, so a
  compromised host cannot delete off-host copies.
* **Tested:** `check-hardened` loads `worker.nft` in a throwaway network
  namespace and probes it. It expects these to be allowed: 8472, DB 5432,
  NTP. It expects these to be rejected: 8471, 443, DNS, `169.254.169.254`,
  `169.254.170.2`, `1.1.1.1`, and SSH to another worker.

### systemd units (`deploy/hardened/systemd`)

| unit | host | notes |
|------|------|-------|
| `arena-server.service` | control plane | report key via `LoadCredential=` (0400 in the service's credential dir, never in env); `/etc/arena/credentials` otherwise inaccessible; `ExecStartPre=arena-guard server` |
| `arena-migrate.service` | control plane | one-shot: `arena-server migrate` as `arena_owner`, then `grants.sql`. The running server never holds owner credentials |
| `arena-worker@<class>.service` | worker hosts | firecracker only; `DeviceAllow=/dev/kvm`; `IPAddressDeny=any` plus a per-host `10-network.conf` allowing only the control plane (fails closed without it); `ExecStartPre=arena-guard worker` |
| `arena-worker@bench.service.d/20-bench.conf` | bench hosts | `Conflicts=` every other class; `AllowedCPUs=`; `ARENA_BENCH_CPUS`; `bench-host-record --check` gates startup |
| `arena-worker@gpu.service.d/20-gpu.conf` | GPU hosts | `AssertPathExists=/etc/arena/gpu-isolation.reviewed`: refuses to start until the GPU route in `docs/ISOLATION.md` (runners-vm lane) has been reviewed for that host |
| `arena-backup-{db,objects}.{service,timer}` | DB / control plane | nightly, `age`-encrypted, retention-pruned |

Every service sets:

```
NoNewPrivileges=yes
CapabilityBoundingSet=
ProtectSystem=strict
ProtectHome=yes
PrivateTmp=yes
ProtectKernelTunables=yes
ProtectKernelModules=yes
ProtectKernelLogs=yes
ProtectControlGroups=yes
ProtectClock=yes
ProtectHostname=yes
ProtectProc=invisible
RestrictAddressFamilies=AF_UNIX AF_INET AF_INET6
RestrictNamespaces=yes
RestrictSUIDSGID=yes
LockPersonality=yes
MemoryDenyWriteExecute=yes
SystemCallArchitectures=native
SystemCallFilter=@system-service
IPAddressDeny=
UMask=0077
```

`check-hardened` enforces this list. It also runs `systemd-analyze security
--offline` and requires these exposure scores:

| unit | budget | current score |
|------|--------|---------------|
| server | ≤ 2.5 | 1.1 |
| worker | ≤ 3.5 | 1.4 |
| migrate | ≤ 2.5 | 1.1 |

If the runners-vm lane adopts the firecracker jailer, it should ship a
`arena-worker@.service.d/` drop-in that relaxes exactly what the jailer needs
(namespaces, chroot). It should not loosen the base unit.

### Benchmark hosts

Each benchmark host is dedicated: it runs no other worker class and no other
tenants. It must boot with the following settings:

| setting | how |
|---------|-----|
| isolated benchmark CPUs | `isolcpus=managed_irq,domain,<cpus> nohz_full=<cpus> rcu_nocbs=<cpus>` |
| SMT off | `nosmt` |
| turbo/boost disabled | — |
| `performance` governor | — |
| pinned frequency | `scaling_min_freq == scaling_max_freq` |

`bench-host-record` runs as `ExecStartPre`. It records the following into
`/var/lib/arena-worker/bench/host-settings.json`, together with a sha256
digest of the document:

* governor, driver and frequency limits per CPU
* turbo state and SMT state
* the relevant kernel arguments
* CPU model, microcode and kernel version

With `--check`, it refuses to start the worker if the host has drifted from
benchmark configuration. The worker must attach this document (or its digest)
to every `measurement` evidence node (CONTRACTS.md §8). Results are only
comparable across identical settings digests.

### Database roles (`deploy/sql`)

| role | privileges |
|------|-----------|
| `arena_owner` | owns the database and `public` schema; used only by migrations |
| `arena_api` | `NOINHERIT`. Default `SELECT/INSERT/UPDATE` on new tables. No DDL, no `DELETE`/`TRUNCATE`. Append-only tables (`audit_log`, `job_events`, `gate_results`, `decisions`) are `SELECT/INSERT` only. 60 s statement timeout |
| `arena_worker` | `NOINHERIT`. Only `jobs` (`SELECT, UPDATE` for `FOR UPDATE SKIP LOCKED` leasing), `job_events`/`gate_results` (`INSERT`), `artifacts` (`SELECT, INSERT`). No access to token tables or submissions. 30 s statement timeout |
| `arena_backup` | `pg_read_all_data`, peer-authenticated locally only |
| `arena_readonly` | `NOLOGIN` group for ad-hoc inspection |

* **Setup:** `roles.sql` is idempotent and runs at database init.
* **After each migration:** `grants.sql` runs after every migration. If a
  table it expects is missing, it emits a `WARNING` and skips it, so a schema
  rename shows up instead of silently granting too much. **The table names
  are the deploy lane's expectation and must be reconciled with
  `server/` migrations.**
* **Verified:** these grants were checked against a live Postgres 17
  instance:
  * the API cannot `DELETE`, cannot run DDL, and cannot `UPDATE` the audit
    log;
  * the worker cannot read `agent_tokens` or `submissions`, cannot `INSERT`
    jobs, and cannot `DELETE`.
* **Production `pg_hba.conf`:** TLS-only `scram-sha-256`, one line per
  (role, source) pair, everything else `reject`.

### Secrets and the report key

* **Secret files:** production secrets live in `/etc/arena/*.env`
  (`root:<service> 0640`). They are provisioned out of band and never
  generated by `gen-dev-secrets.sh`; the guard rejects the dev stamp.
* **Report signing key:** it exists **only on the control-plane host** at
  `/etc/arena/credentials/report-signing-key.pem` (`root 0400`). It is
  delivered to the service with `LoadCredential=`. The guard refuses any
  worker environment that references it.
  * Rotate it by publishing the new public key, swapping the credential file
    and restarting.
  * Old reports stay verifiable against the published key history.
* **Agent and admin tokens:** stored hashed (CONTRACTS.md §10). Admin tokens
  never reach worker hosts.

### Backups and audit retention

* **Database:**
  * A nightly `pg_dump -Fc` is encrypted with `age` to offline recipients.
  * WAL is archived continuously (`archive_command = arena-backup wal`,
    which never overwrites) for point-in-time recovery.
  * Retention keeps 35 daily dumps plus the oldest dump of each of the last
    13 months (`ARENA_BACKUP_KEEP_*`).
* **Object store:** a nightly incremental, encrypted tar of new objects.
  Objects are immutable and content-addressed, so the chain is never pruned.
* **Audit:**
  * The `audit_log` table is append-only for `arena_api`. Only the owner role
    can delete, and the deploy never automates that.
  * Postgres logs connections, disconnections and all DDL.
  * journald is persistent and sealed, with 400-day local retention
    (`journald/arena-retention.conf`). Ship logs to a log host for the full
    audit period.
  * Keep audit logs and backups for at least the lifetime of any leaderboard
    season they support, plus one year.
* **Restore drills:** restore into a scratch host at least quarterly. Verify
  report signatures and recompute challenge IDs against the restored data.

### Install outline (per host)

1. Create the users: `arena-server`, `arena-migrate`, `arena-worker` (in
   group `kvm`) and `arena-backup`.
2. Install the binaries to `/usr/local/bin`. Install `arena-guard`,
   `arena-backup` and `bench-host-record` to `/usr/local/lib/arena/`.
3. Install `deploy/sql` to `/usr/local/share/arena/sql/`.
4. Install the host's nftables ruleset as `/etc/nftables.conf`, and
   `arena-metadata.nft` to `/etc/nftables.d/`. Edit the defines, then run
   `nft -c -f` before enabling `nftables.service`.
5. Install the units. Copy the `10-network.conf.example` drop-in with the
   real control-plane address.
6. Write `/etc/arena/*.env` from `env/*.example`.
7. Run `systemctl start arena-migrate`, then `systemctl enable --now
   arena-server` (or `arena-worker@<class>`) and the backup timers.
8. Run `deploy/hardened/bin/check-hardened` from a checkout to validate the
   configuration offline.

---

## 5. CI (`.github/workflows/ci.yml`)

Every job runs a root `Makefile` target, so a component that hasn't landed
fails with the name of its owning lane. Nothing is skipped.

| job | what |
|-----|------|
| `rust` | `make fmt-check clippy test-rust build` with a Postgres 17 service (`DATABASE_URL`, `ARENA_TEST_DATABASE_URL`) |
| `schemas` | `make schemas-check`: regenerates `common/schemas` and fails on any diff or untracked file |
| `lean` | matrix `formal-core`, `spec/lean`: elan toolchain cache keyed on `lean-toolchain`, `lean-action` `lake build` with the `.lake` cache |
| `web` | `make web` (pnpm install --frozen-lockfile, build, test) |
| `sdk-python`, `sdk-ts` | `make test-sdk-python`, `make test-sdk-ts` |
| `deploy` | `make deploy-check` (guard tests, `check-hardened`, shellcheck); compose renders and passes the guard; a `0.0.0.0` publish must be refused |
| `workflow-lint` | `make workflow-lint` (zizmor 1.24.1, actionlint 1.7.12 pinned by digest) |
| `e2e-hostile` | `make e2e-hostile` with Postgres and bubblewrap (unprivileged user namespaces enabled) |

How the workflow itself is secured:

* All actions are pinned by commit SHA, with a version comment.
* The workflow sets `permissions: {}` at the top level, and each job gets
  only `contents: read`.
* `persist-credentials: false`.
* No `pull_request_target`.
* Service containers bind to `127.0.0.1`.

Run `make workflow-lint` locally before changing workflows.

#!/usr/bin/env bash
# Generate DEV-ONLY secrets for the local stack into <repo>/var/secrets
# (gitignored). Never use these in production: every file is stamped with
# ARENA_SECRETS_ORIGIN=dev-generator and arena-guard refuses that stamp when
# ARENA_ENV=production.
#
# Usage: deploy/local/gen-dev-secrets.sh [--force]
#   ARENA_VAR_DIR   override output root (default: <repo>/var)
#   ARENA_PG_PORT   loopback port postgres is published on (default: 55472)
#
# Produces (all mode 0600, directory 0700):
#   postgres.env           superuser + per-role DB passwords (postgres container only)
#   server.env             control plane: DB URLs, admin/worker/bootstrap-agent tokens
#   worker.env             host worker: worker token + worker-role DB URL (no admin token, no report key)
#   worker-compose.env     same, addressed from inside the compose network
#   migrate.env            host-side owner-role DB URL for running migrations outside compose
#   agent.env              CLI/SDK: ARENA_URL + agent token
#   admin.env              arena-admin: ARENA_URL + admin token
#   report-signing-key.pem ed25519 PKCS#8 private key (control plane only)
#   report-signing-key.pub.pem
set -euo pipefail

force=0
case "${1-}" in
  --force) force=1 ;;
  "") ;;
  *) echo "usage: $0 [--force]" >&2; exit 64 ;;
esac

if [[ ${ARENA_ENV-} == production ]]; then
  echo "gen-dev-secrets: REFUSED: ARENA_ENV=production; provision production secrets out of band (docs/DEPLOYMENT.md)" >&2
  exit 2
fi

repo=$(cd "$(dirname "$0")/../.." && pwd)
var=${ARENA_VAR_DIR:-$repo/var}
out=$var/secrets
pg_port=${ARENA_PG_PORT:-55472}

if [[ -e $out/server.env && $force != 1 ]]; then
  echo "gen-dev-secrets: using existing dev secrets in $out (--force rotates them; then run 'make dev-down DEV_DOWN_VOLUMES=1' since DB passwords change)" >&2
  exit 0
fi

command -v openssl >/dev/null || { echo "gen-dev-secrets: openssl is required" >&2; exit 1; }

umask 077
mkdir -p "$out" "$var/objects"
chmod 700 "$out"

rand() { openssl rand -hex 32; }
pg_super=$(rand)
pg_owner=$(rand)
pg_api=$(rand)
pg_worker=$(rand)
admin_token="arena_dev_admin_$(rand)"
worker_token="arena_dev_worker_$(rand)"
agent_token="arena_dev_agent_$(rand)"

stamp="# DEV-ONLY secrets generated $(date -u +%Y-%m-%dT%H:%M:%SZ) by deploy/local/gen-dev-secrets.sh. Do not use in production.
ARENA_SECRETS_ORIGIN=dev-generator"

write() { # FILE CONTENT
  local f=$out/$1 tmpf
  tmpf=$(mktemp "$out/.tmp.XXXXXX")
  printf '%s\n' "$2" >"$tmpf"
  chmod 600 "$tmpf"
  mv -f "$tmpf" "$f"
}

write postgres.env "$stamp
POSTGRES_USER=postgres
POSTGRES_PASSWORD=$pg_super
POSTGRES_DB=arena
ARENA_DB_OWNER_PASSWORD=$pg_owner
ARENA_DB_API_PASSWORD=$pg_api
ARENA_DB_WORKER_PASSWORD=$pg_worker"

write server.env "$stamp
ARENA_ENV=dev
ARENA_DATABASE_URL=postgres://arena_api:$pg_api@postgres:5432/arena
ARENA_MIGRATE_DATABASE_URL=postgres://arena_owner:$pg_owner@postgres:5432/arena
ARENA_ADMIN_TOKEN=$admin_token
ARENA_WORKER_TOKEN=$worker_token
ARENA_BOOTSTRAP_AGENT_TOKEN=$agent_token
ARENA_REPORT_SIGNING_KEY_FILE=/run/secrets/report-signing-key"

write worker.env "$stamp
ARENA_ENV=dev
ARENA_SERVER_URL=http://127.0.0.1:8472
ARENA_WORKER_TOKEN=$worker_token
ARENA_WORKER_DATABASE_URL=postgres://arena_worker:$pg_worker@127.0.0.1:$pg_port/arena"

# Same worker identity, addressed from inside the compose network (profile "workers").
write worker-compose.env "$stamp
ARENA_ENV=dev
ARENA_SERVER_URL=http://arena-server:8472
ARENA_WORKER_TOKEN=$worker_token
ARENA_WORKER_DATABASE_URL=postgres://arena_worker:$pg_worker@postgres:5432/arena"

write agent.env "$stamp
ARENA_URL=http://127.0.0.1:8471
ARENA_TOKEN=$agent_token"

write admin.env "$stamp
ARENA_URL=http://127.0.0.1:8471
ARENA_ADMIN_TOKEN=$admin_token"

# Host-side migration URL (owner role over the loopback-published port).
write migrate.env "$stamp
ARENA_ENV=dev
ARENA_MIGRATE_DATABASE_URL=postgres://arena_owner:$pg_owner@127.0.0.1:$pg_port/arena
ARENA_DATABASE_URL=postgres://arena_owner:$pg_owner@127.0.0.1:$pg_port/arena"

rm -f "$out/report-signing-key.pem" "$out/report-signing-key.pub.pem"
openssl genpkey -algorithm ed25519 -out "$out/report-signing-key.pem" 2>/dev/null
chmod 600 "$out/report-signing-key.pem"
openssl pkey -in "$out/report-signing-key.pem" -pubout -out "$out/report-signing-key.pub.pem"
chmod 600 "$out/report-signing-key.pub.pem"

echo "gen-dev-secrets: wrote DEV-ONLY secrets to $out"

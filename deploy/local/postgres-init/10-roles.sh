#!/usr/bin/env bash
# docker-entrypoint-initdb.d hook: create least-privilege arena roles.
# Passwords come from var/secrets/postgres.env (gen-dev-secrets.sh).
set -euo pipefail
: "${ARENA_DB_OWNER_PASSWORD:?}" "${ARENA_DB_API_PASSWORD:?}" "${ARENA_DB_WORKER_PASSWORD:?}"
psql -v ON_ERROR_STOP=1 --username "$POSTGRES_USER" --dbname "$POSTGRES_DB" \
  -v owner_pw="$ARENA_DB_OWNER_PASSWORD" \
  -v api_pw="$ARENA_DB_API_PASSWORD" \
  -v worker_pw="$ARENA_DB_WORKER_PASSWORD" \
  -f /arena-sql/roles.sql

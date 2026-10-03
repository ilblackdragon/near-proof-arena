#!/usr/bin/env bash
# Tests for deploy/scripts/arena-guard. Run: deploy/scripts/test-arena-guard.sh
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
guard=$here/arena-guard
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

pass=0
fail=0

# expect EXIT_CODE DESCRIPTION -- ENV... -- ARGS...
expect() {
  local want=$1 desc=$2
  shift 2
  [[ $1 == -- ]] && shift
  local envs=()
  while (($#)) && [[ $1 != -- ]]; do envs+=("$1"); shift; done
  [[ ${1-} == -- ]] && shift
  local got out
  out=$(env -i PATH="$PATH" "${envs[@]}" "$guard" "$@" 2>&1 </dev/null)
  got=$?
  if [[ $got == "$want" ]]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL: %s (want exit %s, got %s)\n%s\n' "$desc" "$want" "$got" "$out" >&2
  fi
}

# expect_compose EXIT_CODE DESCRIPTION ARENA_ENV JSON
expect_compose() {
  local want=$1 desc=$2 envv=$3 json=$4 got out
  out=$(printf '%s' "$json" | env -i PATH="$PATH" ARENA_ENV="$envv" "$guard" compose - 2>&1)
  got=$?
  if [[ $got == "$want" ]]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL: %s (want exit %s, got %s)\n%s\n' "$desc" "$want" "$got" "$out" >&2
  fi
}

key_ok=$tmp/report.key
key_bad=$tmp/report-world.key
echo k >"$key_ok"; chmod 600 "$key_ok"
echo k >"$key_bad"; chmod 644 "$key_bad"

# --- usage / ARENA_ENV ---------------------------------------------------
expect 64 "no mode" -- --
expect 64 "unknown mode" -- -- bogus
expect 2 "server: ARENA_ENV unset" -- -- server
expect 2 "server: ARENA_ENV invalid" -- ARENA_ENV=staging -- server
expect 2 "worker: ARENA_ENV empty" -- ARENA_ENV= -- worker

# --- server, dev: loopback only ---------------------------------------------
expect 0 "server dev default bind" -- ARENA_ENV=dev -- server
expect 0 "server dev 127.0.0.1" -- ARENA_ENV=dev ARENA_BIND_ADDR=127.0.0.1:8471 -- server
expect 0 "server dev 127.1.2.3" -- ARENA_ENV=dev ARENA_BIND_ADDR=127.1.2.3:8471 -- server
expect 0 "server dev [::1]" -- ARENA_ENV=dev 'ARENA_BIND_ADDR=[::1]:8471' -- server
expect 0 "server dev localhost" -- ARENA_ENV=dev ARENA_BIND_ADDR=localhost:8471 -- server
expect 2 "server dev 0.0.0.0" -- ARENA_ENV=dev ARENA_BIND_ADDR=0.0.0.0:8471 -- server
expect 2 "server dev [::]" -- ARENA_ENV=dev 'ARENA_BIND_ADDR=[::]:8471' -- server
expect 2 "server dev public ip" -- ARENA_ENV=dev ARENA_BIND_ADDR=10.0.0.5:8471 -- server
expect 2 "server dev bogus 127 octet" -- ARENA_ENV=dev ARENA_BIND_ADDR=127.0.0.999:8471 -- server
expect 2 "server dev 127.evil.com" -- ARENA_ENV=dev ARENA_BIND_ADDR=127.evil.com:8471 -- server
expect 2 "server dev localhost.evil" -- ARENA_ENV=dev ARENA_BIND_ADDR=localhost.evil:8471 -- server
expect 2 "server dev worker api on 0.0.0.0" -- ARENA_ENV=dev ARENA_WORKER_API_BIND_ADDR=0.0.0.0:8472 -- server
expect 2 "server dev bare host 0.0.0.0" -- ARENA_ENV=dev ARENA_BIND_ADDR=0.0.0.0 -- server

# --- server, production -------------------------------------------------------
expect 0 "server prod ok" -- ARENA_ENV=production ARENA_BIND_ADDR=10.0.0.5:8471 "ARENA_REPORT_SIGNING_KEY_FILE=$key_ok" -- server
expect 2 "server prod no key" -- ARENA_ENV=production ARENA_BIND_ADDR=10.0.0.5:8471 -- server
expect 2 "server prod missing key file" -- ARENA_ENV=production "ARENA_REPORT_SIGNING_KEY_FILE=$tmp/nope" -- server
expect 2 "server prod world-readable key" -- ARENA_ENV=production "ARENA_REPORT_SIGNING_KEY_FILE=$key_bad" -- server
expect 2 "server prod inline key" -- ARENA_ENV=production "ARENA_REPORT_SIGNING_KEY_FILE=$key_ok" ARENA_REPORT_SIGNING_KEY=abc -- server
expect 2 "server prod ARENA_DEV_UNSAFE=0 still refused" -- ARENA_ENV=production "ARENA_REPORT_SIGNING_KEY_FILE=$key_ok" ARENA_DEV_UNSAFE=0 -- server
expect 2 "server prod dev secrets" -- ARENA_ENV=production "ARENA_REPORT_SIGNING_KEY_FILE=$key_ok" ARENA_SECRETS_ORIGIN=dev-generator -- server

# --- worker -------------------------------------------------------------------
expect 0 "worker prod firecracker" -- ARENA_ENV=production ARENA_SANDBOX=firecracker -- worker
expect 0 "worker prod default sandbox" -- ARENA_ENV=production -- worker
expect 2 "worker prod ARENA_DEV_UNSAFE=1" -- ARENA_ENV=production ARENA_DEV_UNSAFE=1 -- worker
expect 2 "worker prod ARENA_DEV_UNSAFE=1 + firecracker" -- ARENA_ENV=production ARENA_DEV_UNSAFE=1 ARENA_SANDBOX=firecracker -- worker
expect 2 "worker prod ARENA_DEV_UNSAFE empty" -- ARENA_ENV=production ARENA_DEV_UNSAFE= -- worker
expect 2 "worker prod bwrap-dev" -- ARENA_ENV=production ARENA_SANDBOX=bwrap-dev -- worker
expect 2 "worker prod dev secrets" -- ARENA_ENV=production ARENA_SECRETS_ORIGIN=dev-generator -- worker
expect 2 "worker has report key" -- ARENA_ENV=production "ARENA_REPORT_SIGNING_KEY_FILE=$key_ok" -- worker
expect 2 "worker dev has report key" -- ARENA_ENV=dev "ARENA_REPORT_SIGNING_KEY_FILE=$key_ok" -- worker
expect 2 "worker has admin token" -- ARENA_ENV=dev ARENA_ADMIN_TOKEN=x -- worker
expect 2 "worker unknown sandbox" -- ARENA_ENV=dev ARENA_SANDBOX=docker -- worker
expect 0 "worker dev bwrap-dev unsafe" -- ARENA_ENV=dev ARENA_SANDBOX=bwrap-dev ARENA_DEV_UNSAFE=1 -- worker
expect 2 "worker dev bwrap-dev without unsafe" -- ARENA_ENV=dev ARENA_SANDBOX=bwrap-dev -- worker
expect 0 "worker dev loopback server url" -- ARENA_ENV=dev ARENA_SERVER_URL=http://127.0.0.1:8472/ -- worker
expect 2 "worker dev remote server url" -- ARENA_ENV=dev ARENA_SERVER_URL=http://10.1.1.1:8472 -- worker

# --- compose ------------------------------------------------------------------
ok_json='{"services":{"arena-server":{"environment":{"ARENA_ENV":"dev"},"ports":[{"target":8471,"published":"8471","host_ip":"127.0.0.1","protocol":"tcp"}]},"postgres":{"ports":[{"target":5432,"published":"55472","host_ip":"127.0.0.1"}]}}}'
expect_compose 0 "compose dev loopback" dev "$ok_json"
expect_compose 2 "compose dev no host_ip" dev '{"services":{"s":{"ports":[{"target":8471,"published":"8471"}]}}}'
expect_compose 2 "compose dev 0.0.0.0" dev '{"services":{"s":{"ports":[{"target":8471,"published":"8471","host_ip":"0.0.0.0"}]}}}'
expect_compose 2 "compose dev ::" dev '{"services":{"s":{"ports":[{"target":8471,"published":"8471","host_ip":"::"}]}}}'
expect_compose 0 "compose dev ::1" dev '{"services":{"s":{"ports":[{"target":8471,"published":"8471","host_ip":"::1"}]}}}'
expect_compose 2 "compose dev host network" dev '{"services":{"s":{"network_mode":"host"}}}'
expect_compose 2 "compose dev privileged" dev '{"services":{"s":{"privileged":true}}}'
expect_compose 2 "compose prod unsafe worker" production '{"services":{"w":{"environment":{"ARENA_ENV":"production","ARENA_DEV_UNSAFE":"1"}}}}'
expect_compose 2 "compose prod bwrap worker" production '{"services":{"w":{"environment":{"ARENA_ENV":"production","ARENA_SANDBOX":"bwrap-dev"}}}}'
expect_compose 2 "compose dev guard but prod service with unsafe" dev '{"services":{"w":{"environment":{"ARENA_ENV":"production","ARENA_DEV_UNSAFE":"1"}}}}'
expect_compose 2 "compose service env mismatch" dev '{"services":{"w":{"environment":{"ARENA_ENV":"staging"}}}}'
expect_compose 2 "compose invalid json" dev 'not json'
expect_compose 0 "compose prod public ports allowed" production '{"services":{"s":{"environment":{"ARENA_ENV":"production"},"ports":[{"target":8471,"published":"8471","host_ip":"0.0.0.0"}]}}}'

echo "arena-guard tests: $pass passed, $fail failed"
((fail == 0))

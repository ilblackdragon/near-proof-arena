# NEAR Proof Arena — developer entry points.
#
# Every target that depends on a component another lane builds checks that the
# component exists first and fails with a clear message if it does not. No
# target "passes" by skipping work.
#
#   make help

SHELL := bash
.SHELLFLAGS := -euo pipefail -c
.DEFAULT_GOAL := help
.DELETE_ON_ERROR:
MAKEFLAGS += --no-builtin-rules

REPO        := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
VAR         := $(REPO)/var
SECRETS     := $(VAR)/secrets
COMPOSE_DIR := $(REPO)/deploy/local
COMPOSE     := docker compose -f $(COMPOSE_DIR)/compose.yaml
GUARD       := $(REPO)/deploy/scripts/arena-guard
CARGO       ?= cargo
CARGO_JOBS  ?= 8
CARGO_FLAGS ?= --locked -j $(CARGO_JOBS)
PNPM        ?= pnpm
PYTHON      ?= python3
LAKE        ?= lake

DEV_PROFILES     ?=
DEV_DOWN_VOLUMES ?= 0
E2E_SCRIPT         ?= tests/e2e/run.sh
E2E_HOSTILE_SCRIPT ?= adversarial/e2e/run.sh
LEAN_PROJECTS      ?= formal-core spec/lean spec/lean/v3 research/near-compression/wasm-base-lean
SHELL_SCRIPTS := deploy/scripts/arena-guard deploy/scripts/test-arena-guard.sh \
                 deploy/local/gen-dev-secrets.sh deploy/local/postgres-init/10-roles.sh \
                 deploy/hardened/bin/arena-backup deploy/hardened/bin/check-hardened
ACTIONLINT_IMAGE := rhysd/actionlint:1.7.12@sha256:b1934ee5f1c509618f2508e6eb47ee0d3520686341fec936f3b79331f9315667
SHELLCHECK_IMAGE := koalaman/shellcheck:v0.11.0@sha256:61862eba1fcf09a484ebcc6feea46f1782532571a34ed51fedf90dd25f925a8d

# Binaries the workspace must provide (docs/CONTRACTS.md, docs/LANES.md).
REQUIRED_BINS := arena-server:server arena-worker:runners-core arena:sdk arena-admin:server

export ARENA_UID := $(shell id -u)
export ARENA_GID := $(shell id -g)

# $(call require,PATH,OWNER-LANE,WHAT)
define require
	@if [ ! -e "$(REPO)/$(1)" ]; then \
	  echo "make: *** MISSING COMPONENT: '$(1)' ($(3)) does not exist yet." >&2; \
	  echo "make: *** It is owned by the '$(2)' lane (docs/LANES.md). Refusing to pass silently." >&2; \
	  exit 2; \
	fi
endef

# $(call require_cmd,CMD,HINT)
define require_cmd
	@command -v $(1) >/dev/null 2>&1 || { echo "make: *** required tool '$(1)' not found: $(2)" >&2; exit 2; }
endef

.PHONY: help
help: ## List targets
	@grep -hE '^[a-zA-Z0-9_-]+:.*## ' $(MAKEFILE_LIST) | sort | \
	  awk 'BEGIN{FS=":.*## "}{printf "  \033[36m%-18s\033[0m %s\n", $$1, $$2}'

# --------------------------------------------------------------------------
# Local dev stack (deploy/local)
# --------------------------------------------------------------------------

.PHONY: dev-secrets
dev-secrets: ## Generate DEV-ONLY secrets into var/secrets (no-op if present)
	@$(COMPOSE_DIR)/gen-dev-secrets.sh

.PHONY: dev-guard
dev-guard: dev-secrets ## Run arena-guard against the rendered dev compose config
	$(call require_cmd,docker,install Docker with the compose plugin)
	@$(COMPOSE) $(foreach p,$(DEV_PROFILES),--profile $(p)) config --format json \
	  | ARENA_ENV=dev $(GUARD) compose -

.PHONY: dev-up
dev-up: dev-guard ## Start postgres + arena-server + web on 127.0.0.1 (DEV_PROFILES=workers for a VM worker)
	$(call require,server/arena-server,server,arena-server crate)
	$(call require,web/package.json,web,web frontend)
	$(call require,challenges,governance,signed challenge definitions)
	$(COMPOSE) $(foreach p,$(DEV_PROFILES),--profile $(p)) up -d --build --wait
	@echo "API: http://127.0.0.1:$${ARENA_API_PORT:-8471}  web: http://127.0.0.1:$${ARENA_WEB_PORT:-8470}"
	@echo "Agent creds: var/secrets/agent.env   admin creds: var/secrets/admin.env"

.PHONY: dev-db
dev-db: dev-guard ## Start only postgres (loopback) for local development
	$(COMPOSE) up -d --wait postgres

.PHONY: dev-down
dev-down: ## Stop the dev stack (DEV_DOWN_VOLUMES=1 also deletes the dev database)
	$(call require_cmd,docker,install Docker with the compose plugin)
	@if [ ! -f $(SECRETS)/server.env ]; then echo "no dev secrets; nothing to stop"; exit 0; fi; \
	 $(COMPOSE) --profile workers down $(if $(filter 1,$(DEV_DOWN_VOLUMES)),--volumes)

.PHONY: dev-worker
dev-worker: dev-secrets ## Run a host bwrap-dev worker (ARENA_DEV_UNSAFE=1, results tier-capped at demo)
	$(call require,runners/worker,runners-core,arena-worker crate)
	$(call require_cmd,bwrap,install bubblewrap)
	set -a; . $(SECRETS)/worker.env; set +a; \
	export ARENA_SANDBOX=bwrap-dev ARENA_DEV_UNSAFE=1 ARENA_WORK_DIR=$(REPO)/var/worker \
	  ARENA_FIXTURES_DIRS=$(REPO)/challenges/demo/toy-arithmetic/fixtures; \
	$(GUARD) worker && exec $(CARGO) run $(CARGO_FLAGS) --bin arena-worker

.PHONY: migrate
migrate: dev-guard ## Apply DB migrations (arena-server migrate, owner role) then least-privilege grants
	$(call require,server/arena-server,server,arena-server crate / migrations)
	$(COMPOSE) up -d --wait postgres
	$(COMPOSE) run --rm --no-deps --build arena-server migrate
	$(COMPOSE) exec -T postgres psql -v ON_ERROR_STOP=1 -U postgres -d arena -f /arena-sql/grants.sql

# --------------------------------------------------------------------------
# Build / test
# --------------------------------------------------------------------------

.PHONY: build
build: ## cargo build the workspace and verify all required binaries exist
	$(CARGO) build $(CARGO_FLAGS) --workspace --all-targets
	@$(CARGO) metadata --format-version 1 --no-deps --locked | $(PYTHON) -c '\
import json,sys; \
bins={t["name"] for p in json.load(sys.stdin)["packages"] for t in p["targets"] if "bin" in t["kind"]}; \
need=[x.split(":") for x in sys.argv[1:]]; \
miss=[(b,l) for b,l in need if b not in bins]; \
[print(f"make: *** MISSING COMPONENT: binary {b!r} is not a workspace target yet (owner lane: {l})", file=sys.stderr) for b,l in miss]; \
sys.exit(2 if miss else 0)' $(REQUIRED_BINS)

.PHONY: pin-check
pin-check: ## Fail if oracle/v3 drifts from the source the signed D0 challenge's generator specs pin
	$(PYTHON) spec/tools/check_oracle_pins.py

.PHONY: test
test: test-rust test-sdk ## Rust workspace tests + SDK tests (web: `make web`, Lean: `make lean`)

.PHONY: test-rust
test-rust: ## cargo test --workspace (set DATABASE_URL / ARENA_TEST_DATABASE_URL for DB tests; needs bwrap)
	$(call require_cmd,bwrap,install bubblewrap (bwrap-dev sandbox tests))
	ARENA_DEV_UNSAFE=1 $(CARGO) test $(CARGO_FLAGS) --workspace --all-targets
	$(CARGO) test $(CARGO_FLAGS) --workspace --doc

.PHONY: test-sdk
test-sdk: test-sdk-python test-sdk-ts ## Python + TypeScript SDK tests

.PHONY: test-sdk-python
test-sdk-python:
	$(call require,sdk/python/pyproject.toml,sdk,Python SDK)
	$(PYTHON) -m venv $(VAR)/venv-sdk
	$(VAR)/venv-sdk/bin/pip install --quiet --upgrade pip
	$(VAR)/venv-sdk/bin/pip install --quiet -e 'sdk/python[test]' pytest
	cd sdk/python && $(VAR)/venv-sdk/bin/python -m pytest -q

.PHONY: test-sdk-ts
test-sdk-ts:
	$(call require,sdk/typescript/package.json,sdk,TypeScript SDK)
	cd sdk/typescript && npm ci && npm run build && npm test

.PHONY: lean
lean: ## lake build the Lean projects in LEAN_PROJECTS
	$(call require_cmd,$(LAKE),install elan: https://github.com/leanprover/elan)
	@for p in $(LEAN_PROJECTS); do \
	  if [ ! -f "$$p/lakefile.lean" ] && [ ! -f "$$p/lakefile.toml" ]; then \
	    echo "make: *** MISSING COMPONENT: Lean project '$$p' has no lakefile (owner: formal-core / spec-oracle lane)" >&2; exit 2; \
	  fi; \
	done
	@for p in $(LEAN_PROJECTS); do echo "== lake build ($$p)"; (cd "$$p" && $(LAKE) build) || exit $$?; done

# The D3 differential drivers live in two separate Lake projects:
#   * spec/lean/v3             — checkD3G (genesis), checkD3Proto (L1 protocol gas)
#   * oracle/wasm-d3/lean      — checkD3 (the D3alpha checker the difftests use), checkD3F (floats),
#                                the read-logging checker (nearspec-v3-check-logged) and its audit
# None of those are in v3's defaultTargets, and oracle/wasm-d3/lean is not in LEAN_PROJECTS at all,
# so a plain `lake build` leaves them unbuilt (the W01 "root's default build does not include every
# executable" gap). This target builds each by name and refuses to pass if a binary is absent.
D3_DRIVERS := spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3g \
              spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3proto \
              oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3 \
              oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3f \
              oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-logged \
              spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
              spec/lean/v3/.lake/build/bin/nearspec-v3-runtime \
              spec/lean/v3/.lake/build/bin/nearspec-v3-test-storage-resolution \
              spec/lean/v3/.lake/build/bin/nearspec-v3-test-global-actions \
              spec/lean/v3/.lake/build/bin/nearspec-v3-test-global-codecs

.PHONY: d3-drivers
d3-drivers: ## Build the named D3 successor drivers (genesis, protocol-gas, D3alpha, floats)
	$(call require_cmd,$(LAKE),install elan: https://github.com/leanprover/elan)
	$(call require_cmd,$(PYTHON),install python3)
	@cd spec/lean/v3 && $(LAKE) build nearspec-v3-check-d3g nearspec-v3-check-d3proto nearspec-v3-check-successor nearspec-v3-runtime nearspec-v3-test-storage-resolution nearspec-v3-test-global-actions nearspec-v3-test-global-codecs nearspec-v3-test-gate-b-caps NearSpecV3.Successor.CodeResolutionTests NearSpecV3.Successor.PromiseActionsTests
	@cd oracle/wasm-d3/lean && $(LAKE) build nearspec-v3-check-d3 nearspec-v3-check-d3f nearspec-v3-check-logged LoggedHarness
	@# the read-logging checker's axiom audit (#guard_msgs: fails on any change, e.g. a sorryAx)
	@cd oracle/wasm-d3/lean && $(LAKE) env lean AuditLogged.lean
	@for b in $(D3_DRIVERS); do \
	  [ -x "$$b" ] || { echo "make: *** MISSING BINARY: '$$b' was not built" >&2; exit 2; }; \
	done
	@$(PYTHON) oracle/wasm-d3/tests/d3_smoke/run_smoke.py --write-stamp
	@echo "d3 drivers built: $(D3_DRIVERS)"

# Depends on `d3-drivers` so the binaries it runs are rebuilt from current sources first. Without that
# prerequisite the recipe executed whatever happened to sit in `.lake/build/bin`: a green smoke could
# mean "the stale binaries from a previous build still pass", which is exactly the failure mode this
# target exists to prevent. The prerequisite is cheap when up to date (lake is incremental).
.PHONY: d3-smoke
d3-smoke: d3-drivers ## Run the D3 drivers + comparison contract against the committed 7-case fixture
	$(call require_cmd,$(PYTHON),install python3)
	@$(PYTHON) oracle/wasm-d3/tests/d3_smoke/run_smoke.py
	@spec/lean/v3/.lake/build/bin/nearspec-v3-test-storage-resolution tools/d3/storage-fixtures/record.wasm tools/d3/storage-fixtures/exhaust.wasm
	@spec/lean/v3/.lake/build/bin/nearspec-v3-test-global-actions
	@spec/lean/v3/.lake/build/bin/nearspec-v3-test-global-codecs docs/evidence/lean-chunk-completion/global-cache-fixtures/codec-vectors.json
	@spec/lean/v3/.lake/build/bin/nearspec-v3-test-gate-b-caps
	@$(PYTHON) tools/d3/smoke_successor.py
	@$(PYTHON) tools/d3/check_runtime_golden.py
	@$(PYTHON) tools/d3/check_float_golden.py

.PHONY: web
web: ## Build and test the web frontend (pnpm)
	$(call require,web/package.json,web,web frontend)
	cd web && $(PNPM) install --frozen-lockfile && $(PNPM) run build && $(PNPM) test

.PHONY: e2e
e2e: ## End-to-end happy-path test (E2E_SCRIPT, default tests/e2e/run.sh)
	$(call require,$(E2E_SCRIPT),integrator,end-to-end test driver)
	$(REPO)/$(E2E_SCRIPT)

.PHONY: e2e-hostile
e2e-hostile: ## Hostile-submission e2e suite (E2E_HOSTILE_SCRIPT, default adversarial/e2e/run.sh)
	$(call require,$(E2E_HOSTILE_SCRIPT),adversarial,hostile-submission e2e driver)
	$(REPO)/$(E2E_HOSTILE_SCRIPT)

# --------------------------------------------------------------------------
# Contracts / formatting / lint
# --------------------------------------------------------------------------

.PHONY: schemas
schemas: ## Regenerate common/schemas from arena-types
	$(CARGO) run $(CARGO_FLAGS) -p arena-types --bin gen-schemas

.PHONY: schemas-check
schemas-check: schemas ## Fail if common/schemas drifts from arena-types
	@git -C $(REPO) diff --exit-code --stat -- common/schemas || \
	  { echo "make: *** common/schemas is out of date: run 'make schemas' and commit" >&2; exit 1; }
	@untracked=$$(git -C $(REPO) ls-files --others --exclude-standard -- common/schemas); \
	 if [ -n "$$untracked" ]; then echo "make: *** untracked generated schemas: $$untracked" >&2; exit 1; fi

.PHONY: fmt
fmt: ## Format Rust code
	$(CARGO) fmt --all

.PHONY: fmt-check
fmt-check:
	$(CARGO) fmt --all -- --check

.PHONY: lint
lint: fmt-check clippy shellcheck ## rustfmt --check, clippy -D warnings, shellcheck

.PHONY: clippy
clippy:
	$(CARGO) clippy $(CARGO_FLAGS) --workspace --all-targets -- -D warnings

.PHONY: shellcheck
shellcheck:
	@if command -v shellcheck >/dev/null 2>&1; then \
	  shellcheck $(SHELL_SCRIPTS); \
	elif command -v docker >/dev/null 2>&1; then \
	  docker run --rm -v $(REPO):/mnt:ro -w /mnt $(SHELLCHECK_IMAGE) $(SHELL_SCRIPTS); \
	else echo "make: *** shellcheck not found (and no docker to run it)" >&2; exit 2; fi

.PHONY: deploy-check
deploy-check: shellcheck ## Guard tests + compose/systemd/nftables validation
	deploy/scripts/test-arena-guard.sh
	deploy/hardened/bin/check-hardened

.PHONY: workflow-lint
workflow-lint: ## zizmor + actionlint over .github/workflows
	@z=$$(command -v zizmor || echo $$HOME/.cargo/bin/zizmor); [ -x "$$z" ] || { echo "make: *** zizmor not found" >&2; exit 2; }; \
	 "$$z" --offline --min-severity low .github/workflows
	@if command -v actionlint >/dev/null 2>&1; then actionlint; \
	 elif command -v docker >/dev/null 2>&1; then docker run --rm -v $(REPO):/repo:ro -w /repo $(ACTIONLINT_IMAGE); \
	 else echo "make: *** actionlint not found (and no docker to run it)" >&2; exit 2; fi

# W13 is a data-dependent release gate. Unit tests do not certify mainnet replay.
W13_CAPTURE ?= $(REPO)/var/mainnet-w13
W13_REPORT ?= $(REPO)/var/mainnet-w13-report
W13_BINARY ?= $(REPO)/spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor
W13_TIER ?= allFeatures
W13_JOBS ?= 1

.PHONY: w13-test w13-gate
w13-test: ## Test W13 coverage, binding, failure handling and mismatch accounting (offline)
	@$(PYTHON) -m unittest discover -s oracle/tools -p 'test_mainnet_gate.py'

w13-gate: ## Require 1000-block all-shard mainnet replay, 100% coverage and zero mismatches
	@$(PYTHON) tools/mainnet-replay/gate.py run --capture "$(W13_CAPTURE)" --binary "$(W13_BINARY)" --tier "$(W13_TIER)" --out "$(W13_REPORT)" --jobs "$(W13_JOBS)" $(if $(W13_NATIVE_COMMAND_FILE),--native-command-file "$(W13_NATIVE_COMMAND_FILE)",)

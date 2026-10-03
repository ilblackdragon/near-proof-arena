-- NEAR Proof Arena control-plane schema (v1).
-- Invariants enforced in the database (not only in application code):
--   * audit_events is append-only (trigger rejects UPDATE/DELETE/TRUNCATE)
--   * submissions, gate_results, revocations, reports are immutable
--   * a run is immutable once decided; reruns create new run rows
--   * challenge definitions are frozen once registered (only `open` may change)

CREATE OR REPLACE FUNCTION arena_reject_mutation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
  RAISE EXCEPTION 'arena: % on % is forbidden (append-only/immutable table)', TG_OP, TG_TABLE_NAME
    USING ERRCODE = 'insufficient_privilege';
END $$;

-- ---------------------------------------------------------------- principals
CREATE TABLE agents (
  id          text PRIMARY KEY CHECK (id ~ '^agt_[0-9a-f]{32}$'),
  handle      text NOT NULL UNIQUE CHECK (handle ~ '^[a-z0-9][a-z0-9_-]{0,47}$'),
  token_hash  bytea NOT NULL UNIQUE CHECK (length(token_hash) = 32),
  disabled    boolean NOT NULL DEFAULT false,
  created_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE admins (
  id          text PRIMARY KEY CHECK (id ~ '^adm_[0-9a-f]{32}$'),
  name        text NOT NULL UNIQUE CHECK (name ~ '^[a-z0-9][a-z0-9_-]{0,47}$'),
  token_hash  bytea NOT NULL UNIQUE CHECK (length(token_hash) = 32),
  disabled    boolean NOT NULL DEFAULT false,
  created_at  timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE workers (
  id              text PRIMARY KEY CHECK (id ~ '^wrk_[0-9a-f]{32}$'),
  name            text NOT NULL UNIQUE CHECK (name ~ '^[a-z0-9][a-z0-9_-]{0,47}$'),
  token_hash      bytea NOT NULL UNIQUE CHECK (length(token_hash) = 32),
  sandbox_backend text NOT NULL CHECK (sandbox_backend ~ '^[a-z0-9][a-z0-9_-]{0,31}$'),
  -- highest challenge tier this worker may execute: 0 demo, 1 experimental, 2 formal
  tier_cap        smallint NOT NULL CHECK (tier_cap BETWEEN 0 AND 2),
  disabled        boolean NOT NULL DEFAULT false,
  created_at      timestamptz NOT NULL DEFAULT now(),
  -- the namespaces-only dev sandbox can never run non-demo work
  CHECK (sandbox_backend <> 'bwrap-dev' OR tier_cap = 0)
);

-- ---------------------------------------------------------------- challenges
CREATE TABLE challenges (
  id              text PRIMARY KEY CHECK (id ~ '^chl_[0-9a-f]{32}$'),
  digest          text NOT NULL UNIQUE CHECK (digest ~ '^sha256:[0-9a-f]{64}$'),
  name            text NOT NULL,
  tier            text NOT NULL CHECK (tier IN ('formal', 'experimental', 'demo')),
  definition      jsonb NOT NULL,
  canonical_bytes bytea NOT NULL,           -- exact JCS bytes that were signed
  signature       bytea NOT NULL CHECK (length(signature) = 64),
  governance_key  bytea NOT NULL CHECK (length(governance_key) = 32),
  frozen          boolean NOT NULL DEFAULT true CHECK (frozen),
  open            boolean NOT NULL DEFAULT true,   -- accepting new submissions
  registered_by   text NOT NULL,
  created_at      timestamptz NOT NULL DEFAULT now()
);

CREATE OR REPLACE FUNCTION arena_challenge_frozen() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
  IF TG_OP = 'DELETE' THEN
    RAISE EXCEPTION 'arena: challenges cannot be deleted' USING ERRCODE = 'insufficient_privilege';
  END IF;
  IF NEW.id IS DISTINCT FROM OLD.id OR NEW.digest IS DISTINCT FROM OLD.digest
     OR NEW.definition IS DISTINCT FROM OLD.definition
     OR NEW.canonical_bytes IS DISTINCT FROM OLD.canonical_bytes
     OR NEW.signature IS DISTINCT FROM OLD.signature
     OR NEW.governance_key IS DISTINCT FROM OLD.governance_key
     OR NEW.tier IS DISTINCT FROM OLD.tier OR NEW.name IS DISTINCT FROM OLD.name
     OR NEW.frozen IS DISTINCT FROM OLD.frozen
     OR NEW.registered_by IS DISTINCT FROM OLD.registered_by
     OR NEW.created_at IS DISTINCT FROM OLD.created_at THEN
    RAISE EXCEPTION 'arena: challenge definitions are frozen' USING ERRCODE = 'insufficient_privilege';
  END IF;
  RETURN NEW;
END $$;
CREATE TRIGGER challenges_frozen BEFORE UPDATE OR DELETE ON challenges
  FOR EACH ROW EXECUTE FUNCTION arena_challenge_frozen();

-- ---------------------------------------------------------------- objects
CREATE TABLE uploads (
  id          text PRIMARY KEY CHECK (id ~ '^upl_[0-9a-f]{32}$'),
  agent_id    text NOT NULL REFERENCES agents(id),
  digest      text NOT NULL CHECK (digest ~ '^sha256:[0-9a-f]{64}$'),
  size_bytes  bigint NOT NULL CHECK (size_bytes >= 0),
  created_at  timestamptz NOT NULL DEFAULT now(),
  UNIQUE (agent_id, digest)
);
CREATE INDEX uploads_agent_time ON uploads (agent_id, created_at);

-- Objects written by workers through the artifact API.
CREATE TABLE artifacts (
  digest      text PRIMARY KEY CHECK (digest ~ '^sha256:[0-9a-f]{64}$'),
  size_bytes  bigint NOT NULL CHECK (size_bytes >= 0),
  worker_id   text REFERENCES workers(id),
  created_at  timestamptz NOT NULL DEFAULT now()
);

-- ---------------------------------------------------------------- submissions
CREATE TABLE submissions (
  id              text PRIMARY KEY CHECK (id ~ '^sub_[0-9a-f]{32}$'),
  agent_id        text NOT NULL REFERENCES agents(id),
  challenge_id    text NOT NULL REFERENCES challenges(id),
  package_digest  text NOT NULL CHECK (package_digest ~ '^sha256:[0-9a-f]{64}$'),
  upload_id       text NOT NULL REFERENCES uploads(id),
  parent_id       text REFERENCES submissions(id),
  idempotency_key text NOT NULL CHECK (length(idempotency_key) BETWEEN 1 AND 128),
  request_digest  text NOT NULL,
  created_at      timestamptz NOT NULL DEFAULT now(),
  UNIQUE (agent_id, idempotency_key)
);
CREATE INDEX submissions_challenge ON submissions (challenge_id, created_at);
CREATE INDEX submissions_agent ON submissions (agent_id, created_at);
CREATE TRIGGER submissions_immutable BEFORE UPDATE OR DELETE ON submissions
  FOR EACH ROW EXECUTE FUNCTION arena_reject_mutation();

CREATE TABLE runs (
  id                text PRIMARY KEY CHECK (id ~ '^run_[0-9a-f]{32}$'),
  submission_id     text NOT NULL REFERENCES submissions(id),
  run_number        integer NOT NULL CHECK (run_number >= 1),
  trigger           text NOT NULL,             -- 'submit' | 'rerun'
  requested_by      text NOT NULL,
  challenge_tier    text NOT NULL CHECK (challenge_tier IN ('formal', 'experimental', 'demo')),
  -- effective tier: min(challenge tier, every result's tier cap)
  tier              text NOT NULL CHECK (tier IN ('formal', 'experimental', 'demo')),
  stage             text NOT NULL,
  decision          text CHECK (decision IN ('ADMITTED','REJECTED','INCONCLUSIVE','INFRA_ERROR','CANCELLED')),
  accepted          boolean,
  score_milli       bigint CHECK (score_milli >= 0),
  change_class      text,
  candidate_name    text NOT NULL DEFAULT '',
  backend_family    text NOT NULL DEFAULT '',
  manifest          jsonb,
  build_outputs     jsonb,
  verified_surface  jsonb,
  formal_cache_key  text,
  benchmark         jsonb,
  evidence_graph    jsonb,
  reason_codes      jsonb NOT NULL DEFAULT '[]',
  not_run_gates     jsonb NOT NULL DEFAULT '[]',
  created_at        timestamptz NOT NULL DEFAULT now(),
  updated_at        timestamptz NOT NULL DEFAULT now(),
  decided_at        timestamptz,
  UNIQUE (submission_id, run_number),
  CHECK ((decision IS NULL) = (decided_at IS NULL)),
  CHECK (decision IS NULL OR stage = 'DECIDED'),
  CHECK (accepted IS NOT TRUE OR decision = 'ADMITTED'),
  CHECK (score_milli IS NULL OR accepted IS TRUE)
);
CREATE INDEX runs_pending ON runs (submission_id) WHERE decision IS NULL;

CREATE OR REPLACE FUNCTION arena_run_guard() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
  IF TG_OP = 'DELETE' THEN
    RAISE EXCEPTION 'arena: runs cannot be deleted' USING ERRCODE = 'insufficient_privilege';
  END IF;
  IF OLD.decision IS NOT NULL THEN
    RAISE EXCEPTION 'arena: run % is decided and immutable', OLD.id USING ERRCODE = 'insufficient_privilege';
  END IF;
  IF NEW.id <> OLD.id OR NEW.submission_id <> OLD.submission_id OR NEW.run_number <> OLD.run_number
     OR NEW.challenge_tier <> OLD.challenge_tier OR NEW.created_at <> OLD.created_at THEN
    RAISE EXCEPTION 'arena: run identity is immutable' USING ERRCODE = 'insufficient_privilege';
  END IF;
  NEW.updated_at := now();
  RETURN NEW;
END $$;
CREATE TRIGGER runs_guard BEFORE UPDATE OR DELETE ON runs
  FOR EACH ROW EXECUTE FUNCTION arena_run_guard();

CREATE TABLE gate_results (
  id          bigserial PRIMARY KEY,
  run_id      text NOT NULL REFERENCES runs(id),
  job_id      uuid,
  gate        text NOT NULL,
  mandatory   boolean NOT NULL,
  status      text NOT NULL CHECK (status IN ('PASS','FAIL','UNKNOWN','NOT_APPLICABLE')),
  result      jsonb NOT NULL,              -- full GateResult
  created_at  timestamptz NOT NULL DEFAULT now(),
  UNIQUE (run_id, gate)
);
CREATE TRIGGER gate_results_immutable BEFORE UPDATE OR DELETE ON gate_results
  FOR EACH ROW EXECUTE FUNCTION arena_reject_mutation();

-- ---------------------------------------------------------------- job queue
CREATE TABLE jobs (
  id            uuid PRIMARY KEY,
  run_id        text NOT NULL REFERENCES runs(id),
  submission_id text NOT NULL REFERENCES submissions(id),
  kind          text NOT NULL CHECK (kind IN ('VALIDATE','BUILD','FORMAL_CHECK','CONFORMANCE','ADVERSARIAL','BENCHMARK')),
  tier_rank     smallint NOT NULL CHECK (tier_rank BETWEEN 0 AND 2),
  payload       jsonb NOT NULL,
  state         text NOT NULL CHECK (state IN ('queued','leased','done','failed','cancelled')),
  attempt       integer NOT NULL DEFAULT 0 CHECK (attempt >= 0),
  max_attempts  integer NOT NULL CHECK (max_attempts >= 1),
  lease_id      uuid,
  lease_owner   text REFERENCES workers(id),
  lease_until   timestamptz,
  run_after     timestamptz NOT NULL DEFAULT now(),
  last_error    text,
  result        jsonb,
  execution     jsonb,
  created_at    timestamptz NOT NULL DEFAULT now(),
  updated_at    timestamptz NOT NULL DEFAULT now(),
  finished_at   timestamptz,
  UNIQUE (run_id, kind),
  CHECK (state <> 'leased' OR (lease_id IS NOT NULL AND lease_owner IS NOT NULL AND lease_until IS NOT NULL))
);
CREATE INDEX jobs_runnable ON jobs (run_after, created_at) WHERE state IN ('queued', 'leased');
CREATE INDEX jobs_run ON jobs (run_id);

-- ---------------------------------------------------------------- audit
CREATE TABLE audit_events (
  id             bigserial PRIMARY KEY,
  at             timestamptz NOT NULL DEFAULT clock_timestamp(),
  actor_kind     text NOT NULL CHECK (actor_kind IN ('agent','admin','worker','system')),
  actor_id       text NOT NULL,
  action         text NOT NULL,
  submission_id  text,
  run_id         text,
  public         boolean NOT NULL,
  data           jsonb NOT NULL DEFAULT '{}'
);
CREATE INDEX audit_submission ON audit_events (submission_id, id) WHERE submission_id IS NOT NULL;
CREATE TRIGGER audit_append_only BEFORE UPDATE OR DELETE ON audit_events
  FOR EACH ROW EXECUTE FUNCTION arena_reject_mutation();
CREATE TRIGGER audit_no_truncate BEFORE TRUNCATE ON audit_events
  FOR EACH STATEMENT EXECUTE FUNCTION arena_reject_mutation();

-- ---------------------------------------------------------------- revocations
CREATE TABLE revocations (
  id             bigserial PRIMARY KEY,
  submission_id  text NOT NULL UNIQUE REFERENCES submissions(id),
  reason         text NOT NULL CHECK (length(reason) BETWEEN 1 AND 2048),
  revoked_by     text NOT NULL,
  revoked_at     timestamptz NOT NULL DEFAULT now()
);
CREATE TRIGGER revocations_immutable BEFORE UPDATE OR DELETE ON revocations
  FOR EACH ROW EXECUTE FUNCTION arena_reject_mutation();

-- ---------------------------------------------------------------- formal cache
CREATE TABLE formal_cache (
  key                  text PRIMARY KEY CHECK (key ~ '^sha256:[0-9a-f]{64}$'),
  challenge_id         text NOT NULL REFERENCES challenges(id),
  challenge_digest     text NOT NULL,
  verified_surface     jsonb NOT NULL,
  checker_image        text NOT NULL,
  assumptions          text[] NOT NULL,
  tier_rank            smallint NOT NULL CHECK (tier_rank BETWEEN 0 AND 2),
  gates                jsonb NOT NULL,
  evidence_graph       jsonb,
  source_submission_id text NOT NULL REFERENCES submissions(id),
  source_run_id        text NOT NULL REFERENCES runs(id),
  created_at           timestamptz NOT NULL DEFAULT now(),
  invalidated_at       timestamptz,
  invalidated_by       text,
  invalidated_reason   text
);
CREATE INDEX formal_cache_checker ON formal_cache (checker_image);
CREATE INDEX formal_cache_assumptions ON formal_cache USING gin (assumptions);

CREATE OR REPLACE FUNCTION arena_formal_cache_guard() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
  IF TG_OP = 'DELETE' THEN
    RAISE EXCEPTION 'arena: formal cache entries are invalidated, never deleted' USING ERRCODE = 'insufficient_privilege';
  END IF;
  IF OLD.invalidated_at IS NOT NULL OR NEW.key <> OLD.key OR NEW.gates <> OLD.gates
     OR NEW.verified_surface <> OLD.verified_surface OR NEW.tier_rank <> OLD.tier_rank
     OR NEW.source_run_id <> OLD.source_run_id OR NEW.invalidated_at IS NULL THEN
    RAISE EXCEPTION 'arena: formal cache entries may only be invalidated once' USING ERRCODE = 'insufficient_privilege';
  END IF;
  RETURN NEW;
END $$;
CREATE TRIGGER formal_cache_guard BEFORE UPDATE OR DELETE ON formal_cache
  FOR EACH ROW EXECUTE FUNCTION arena_formal_cache_guard();

-- ---------------------------------------------------------------- quotas
CREATE TABLE quotas (
  agent_id                 text PRIMARY KEY REFERENCES agents(id),
  max_submissions_per_day  integer NOT NULL CHECK (max_submissions_per_day >= 0),
  max_upload_bytes_per_day bigint NOT NULL CHECK (max_upload_bytes_per_day >= 0),
  max_active_runs          integer NOT NULL CHECK (max_active_runs >= 0),
  updated_at               timestamptz NOT NULL DEFAULT now()
);

-- ---------------------------------------------------------------- reports
CREATE TABLE reports (
  run_id          text PRIMARY KEY REFERENCES runs(id),
  submission_id   text NOT NULL REFERENCES submissions(id),
  canonical_bytes bytea NOT NULL,     -- JCS bytes that were signed
  signature       bytea NOT NULL CHECK (length(signature) = 64),
  public_key      bytea NOT NULL CHECK (length(public_key) = 32),
  created_at      timestamptz NOT NULL DEFAULT now()
);
CREATE TRIGGER reports_immutable BEFORE UPDATE OR DELETE ON reports
  FOR EACH ROW EXECUTE FUNCTION arena_reject_mutation();

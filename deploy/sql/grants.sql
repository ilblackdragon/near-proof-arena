-- Table-level least-privilege grants. Run after every `arena-server migrate`,
-- as arena_owner or a superuser:
--   psql -v ON_ERROR_STOP=1 -d arena -f grants.sql
--
-- The table names below are the deploy lane's expectation of the server
-- schema (docs/CONTRACTS.md §9: workers lease jobs with FOR UPDATE SKIP
-- LOCKED and write results/artifacts). Missing tables raise a WARNING and are
-- skipped, so a renamed table is visible, never silently over-granted.
-- Reconcile with server/ migrations when they land (docs/DEPLOYMENT.md).

\set ON_ERROR_STOP on

DO $$
DECLARE
  -- table => privileges for arena_worker
  worker_grants CONSTANT text[][] := ARRAY[
    ARRAY['jobs',          'SELECT, UPDATE'],
    ARRAY['job_events',    'INSERT'],
    ARRAY['gate_results',  'INSERT'],
    ARRAY['artifacts',     'SELECT, INSERT']
  ];
  -- append-only tables: the API may only INSERT/SELECT
  append_only CONSTANT text[] := ARRAY['audit_log', 'job_events', 'gate_results', 'decisions'];
  -- secret-bearing tables workers must never read
  api_only CONSTANT text[] := ARRAY['agent_tokens', 'admin_tokens', 'worker_tokens'];
  i int;
  t text;
BEGIN
  FOR i IN 1 .. array_length(worker_grants, 1) LOOP
    t := worker_grants[i][1];
    IF to_regclass('public.' || t) IS NULL THEN
      RAISE WARNING 'grants.sql: table public.% not found; arena_worker gets no access to it', t;
    ELSE
      EXECUTE format('REVOKE ALL ON public.%I FROM arena_worker', t);
      EXECUTE format('GRANT %s ON public.%I TO arena_worker', worker_grants[i][2], t);
    END IF;
  END LOOP;

  FOREACH t IN ARRAY append_only LOOP
    IF to_regclass('public.' || t) IS NULL THEN
      RAISE WARNING 'grants.sql: append-only table public.% not found', t;
    ELSE
      EXECUTE format('REVOKE UPDATE, DELETE, TRUNCATE ON public.%I FROM arena_api', t);
      EXECUTE format('GRANT SELECT, INSERT ON public.%I TO arena_api', t);
    END IF;
  END LOOP;

  FOREACH t IN ARRAY api_only LOOP
    IF to_regclass('public.' || t) IS NOT NULL THEN
      EXECUTE format('REVOKE ALL ON public.%I FROM arena_worker, arena_readonly', t);
    END IF;
  END LOOP;

  -- Workers need sequences only for tables they insert into.
  EXECUTE 'GRANT USAGE ON ALL SEQUENCES IN SCHEMA public TO arena_worker';
  -- Nobody but the owner may DELETE/TRUNCATE.
  EXECUTE 'REVOKE DELETE, TRUNCATE ON ALL TABLES IN SCHEMA public FROM arena_api, arena_worker, arena_readonly';
END
$$;

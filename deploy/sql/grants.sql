-- Generated from server/arena-db/src/roles.rs (`arena-server grants-sql`). Do not edit by hand;
-- a server test fails if this file drifts from the schema.
-- Run after every `arena-server migrate`, as arena_owner or a superuser:
--   psql -v ON_ERROR_STOP=1 -d arena -f grants.sql
--
--   arena_api      the control plane (public API, worker gateway, admin): union of the
--                  split roles' privileges; no DELETE/TRUNCATE anywhere. Append-only and
--                  immutable tables are additionally enforced by triggers.
--   arena_worker   NO database access: workers only reach the internal worker API (8472).
--   arena_readonly SELECT on everything except credential-hash tables.
\set ON_ERROR_STOP on
BEGIN;
REVOKE ALL ON agents, admins, workers, challenges, uploads, artifacts, submissions, runs, gate_results, jobs, audit_events, revocations, formal_cache, quotas, reports FROM PUBLIC;
REVOKE ALL ON agents, admins, workers, challenges, uploads, artifacts, submissions, runs, gate_results, jobs, audit_events, revocations, formal_cache, quotas, reports FROM arena_api;
GRANT USAGE ON SCHEMA public TO arena_api;
GRANT USAGE ON SEQUENCE audit_events_id_seq, formal_cache_id_seq, gate_results_id_seq, revocations_id_seq TO arena_api;
GRANT SELECT ON agents, challenges, uploads, submissions, runs, gate_results, jobs, audit_events, revocations, quotas, reports, workers, artifacts, formal_cache, admins TO arena_api;
GRANT INSERT ON uploads, submissions, runs, jobs, audit_events, reports, artifacts, gate_results, formal_cache, agents, admins, workers, challenges, revocations, quotas TO arena_api;
GRANT UPDATE ON runs, jobs, agents, admins, workers, challenges, quotas, formal_cache TO arena_api;
REVOKE ALL ON agents, admins, workers, challenges, uploads, artifacts, submissions, runs, gate_results, jobs, audit_events, revocations, formal_cache, quotas, reports FROM arena_worker;
REVOKE ALL ON ALL SEQUENCES IN SCHEMA public FROM arena_worker;
REVOKE ALL ON agents, admins, workers, challenges, uploads, artifacts, submissions, runs, gate_results, jobs, audit_events, revocations, formal_cache, quotas, reports FROM arena_readonly;
GRANT SELECT ON challenges, uploads, artifacts, submissions, runs, gate_results, jobs, audit_events, revocations, formal_cache, quotas, reports TO arena_readonly;
COMMIT;

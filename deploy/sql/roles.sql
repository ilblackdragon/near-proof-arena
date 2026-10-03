-- NEAR Proof Arena database roles (least privilege). Idempotent.
--
-- Run as a superuser against the arena database:
--   psql -v ON_ERROR_STOP=1 -d arena \
--        -v owner_pw=... -v api_pw=... -v worker_pw=... -f roles.sql
--
--   arena_owner   owns the schema; used ONLY by `arena-server migrate`
--                 (a separate, short-lived step). Never by the running server.
--   arena_api     the running control plane: DML, no DDL, no DELETE on
--                 append-only tables (see grants.sql).
--   arena_worker  workers: only the job/artifact tables they need (grants.sql).
--   arena_backup  read-only role for pg_dump.
--   arena_readonly ad-hoc inspection.
--
-- Table-level grants depend on the server's migrations and are applied by
-- grants.sql after every `arena-server migrate`.

\set ON_ERROR_STOP on

SELECT format('CREATE ROLE %I LOGIN', r)
FROM unnest(ARRAY['arena_owner','arena_api','arena_worker','arena_backup']) AS r
WHERE NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = r)
\gexec
SELECT 'CREATE ROLE arena_readonly NOLOGIN'
WHERE NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = 'arena_readonly')
\gexec

ALTER ROLE arena_owner  NOSUPERUSER NOCREATEDB NOCREATEROLE NOREPLICATION NOBYPASSRLS PASSWORD :'owner_pw';
ALTER ROLE arena_api    NOSUPERUSER NOCREATEDB NOCREATEROLE NOREPLICATION NOBYPASSRLS NOINHERIT PASSWORD :'api_pw';
ALTER ROLE arena_worker NOSUPERUSER NOCREATEDB NOCREATEROLE NOREPLICATION NOBYPASSRLS NOINHERIT PASSWORD :'worker_pw';
ALTER ROLE arena_backup NOSUPERUSER NOCREATEDB NOCREATEROLE NOREPLICATION NOBYPASSRLS;
\if :{?backup_pw}
ALTER ROLE arena_backup PASSWORD :'backup_pw';
\endif
GRANT pg_read_all_data TO arena_backup;

-- Bound the blast radius of a compromised connection.
ALTER ROLE arena_api    SET statement_timeout = '60s';
ALTER ROLE arena_worker SET statement_timeout = '30s';
ALTER ROLE arena_api    SET idle_in_transaction_session_timeout = '60s';
ALTER ROLE arena_worker SET idle_in_transaction_session_timeout = '30s';
ALTER ROLE arena_api    CONNECTION LIMIT 64;
ALTER ROLE arena_worker CONNECTION LIMIT 64;

-- Lock down the database and the public schema.
SELECT format('ALTER DATABASE %I OWNER TO arena_owner', current_database()) \gexec
SELECT format('REVOKE ALL ON DATABASE %I FROM PUBLIC', current_database()) \gexec
SELECT format('GRANT CONNECT ON DATABASE %I TO arena_owner, arena_api, arena_worker, arena_backup', current_database()) \gexec
ALTER SCHEMA public OWNER TO arena_owner;
REVOKE ALL ON SCHEMA public FROM PUBLIC;
GRANT USAGE ON SCHEMA public TO arena_api, arena_worker, arena_readonly;

-- New tables created by migrations: the API gets read/insert/update (no
-- DELETE/TRUNCATE) by default; workers get nothing by default.
ALTER DEFAULT PRIVILEGES FOR ROLE arena_owner IN SCHEMA public
  GRANT SELECT, INSERT, UPDATE ON TABLES TO arena_api;
ALTER DEFAULT PRIVILEGES FOR ROLE arena_owner IN SCHEMA public
  GRANT USAGE, SELECT ON SEQUENCES TO arena_api;
ALTER DEFAULT PRIVILEGES FOR ROLE arena_owner IN SCHEMA public
  GRANT SELECT ON TABLES TO arena_readonly;

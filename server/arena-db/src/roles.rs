//! Least-privilege Postgres roles.
//!
//! Three roles, each used by one connection pool of the control plane:
//!
//! * **api** — public/agent API: reads, uploads, submissions, cancellation.
//! * **worker** — the *worker gateway* inside the control plane that serves
//!   `/internal/v1/*`. Worker processes themselves never receive database
//!   credentials; they only speak HTTP to the gateway.
//! * **admin** — challenge registration, revocations, reruns, cache
//!   invalidation, principal management.
//!
//! No role is granted `DELETE` or `TRUNCATE` on any table; immutability of
//! audit events, submissions, gate results, revocations and reports is
//! additionally enforced by triggers that apply even to the table owner.
//! The migration owner (the role that runs `arena-server migrate`) owns the
//! schema and should not be used by the serving process in production.

/// Default role names (used by `server/arena-db/sql/roles.sql`).
pub const DEFAULT_ROLES: RoleNames<'static> = RoleNames {
    api: "arena_api",
    worker: "arena_worker",
    admin: "arena_admin",
};

#[derive(Clone, Copy, Debug)]
pub struct RoleNames<'a> {
    pub api: &'a str,
    pub worker: &'a str,
    pub admin: &'a str,
}

fn ident_ok(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 63
        && s.bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
        && !s.as_bytes()[0].is_ascii_digit()
}

const ALL_TABLES: &[&str] = &[
    "agents",
    "admins",
    "workers",
    "challenges",
    "uploads",
    "artifacts",
    "submissions",
    "runs",
    "gate_results",
    "jobs",
    "audit_events",
    "revocations",
    "formal_cache",
    "quotas",
    "reports",
];

/// Table privileges of one role: (privilege, tables).
type Privs = &'static [(&'static str, &'static [&'static str])];

const API_PRIVS: Privs = &[
    (
        "SELECT",
        &[
            "agents",
            "challenges",
            "uploads",
            "submissions",
            "runs",
            "gate_results",
            "jobs",
            "audit_events",
            "revocations",
            "quotas",
            "reports",
        ],
    ),
    (
        "INSERT",
        &[
            "uploads",
            "submissions",
            "runs",
            "jobs",
            "audit_events",
            "reports",
        ],
    ),
    // cancellation updates pending runs / jobs; the agent row is locked (FOR UPDATE) for quota checks
    ("UPDATE", &["runs", "jobs", "agents"]),
];
const API_SEQS: &[&str] = &["audit_events_id_seq"];

const WORKER_PRIVS: Privs = &[
    (
        "SELECT",
        &[
            "workers",
            "agents",
            "challenges",
            "uploads",
            "artifacts",
            "submissions",
            "runs",
            "gate_results",
            "jobs",
            "formal_cache",
            "reports",
            "revocations",
        ],
    ),
    (
        "INSERT",
        &[
            "artifacts",
            "gate_results",
            "jobs",
            "audit_events",
            "formal_cache",
            "reports",
        ],
    ),
    ("UPDATE", &["runs", "jobs"]),
];
const WORKER_SEQS: &[&str] = &[
    "audit_events_id_seq",
    "gate_results_id_seq",
    "formal_cache_id_seq",
];

const ADMIN_PRIVS: Privs = &[
    ("SELECT", ALL_TABLES),
    (
        "INSERT",
        &[
            "agents",
            "admins",
            "workers",
            "challenges",
            "revocations",
            "quotas",
            "runs",
            "jobs",
            "gate_results",
            "audit_events",
            "reports",
            "formal_cache",
        ],
    ),
    (
        "UPDATE",
        &[
            "agents",
            "admins",
            "workers",
            "challenges",
            "quotas",
            "runs",
            "jobs",
            "formal_cache",
        ],
    ),
];
const ADMIN_SEQS: &[&str] = &[
    "audit_events_id_seq",
    "gate_results_id_seq",
    "revocations_id_seq",
    "formal_cache_id_seq",
];

fn emit(s: &mut String, role: &str, privs: &[(&str, Vec<&str>)], seqs: &[&str]) {
    assert!(ident_ok(role), "invalid role name {role:?}");
    let all = ALL_TABLES.join(", ");
    s.push_str(&format!("REVOKE ALL ON {all} FROM {role};\n"));
    s.push_str(&format!("GRANT USAGE ON SCHEMA public TO {role};\n"));
    s.push_str(&format!(
        "GRANT USAGE ON SEQUENCE {} TO {role};\n",
        seqs.join(", ")
    ));
    for (p, tables) in privs {
        s.push_str(&format!("GRANT {p} ON {} TO {role};\n", tables.join(", ")));
    }
}

fn owned(p: Privs) -> Vec<(&'static str, Vec<&'static str>)> {
    p.iter().map(|(k, t)| (*k, t.to_vec())).collect()
}

/// `GRANT` statements for the three split roles (roles must already exist).
pub fn grants_sql(r: RoleNames<'_>) -> String {
    let mut s = format!("REVOKE ALL ON {} FROM PUBLIC;\n", ALL_TABLES.join(", "));
    emit(&mut s, r.api, &owned(API_PRIVS), API_SEQS);
    emit(&mut s, r.worker, &owned(WORKER_PRIVS), WORKER_SEQS);
    emit(&mut s, r.admin, &owned(ADMIN_PRIVS), ADMIN_SEQS);
    s
}

/// Single-role deployment (one `ARENA_DATABASE_URL` for the whole control
/// plane): `server_role` gets the union of the api, worker-gateway and admin
/// privileges (still no DELETE/TRUNCATE anywhere); every role in `no_access`
/// (e.g. `arena_worker`: workers talk HTTP only) gets nothing.
pub fn single_role_grants_sql(server_role: &str, no_access: &[&str]) -> String {
    let mut union: Vec<(&str, Vec<&str>)> = Vec::new();
    for (p, tables) in API_PRIVS.iter().chain(WORKER_PRIVS).chain(ADMIN_PRIVS) {
        let entry = match union.iter_mut().find(|(k, _)| k == p) {
            Some(e) => e,
            None => {
                union.push((p, vec![]));
                union.last_mut().unwrap()
            }
        };
        for t in tables.iter() {
            if !entry.1.contains(t) {
                entry.1.push(t);
            }
        }
    }
    let mut seqs: Vec<&str> = API_SEQS
        .iter()
        .chain(WORKER_SEQS)
        .chain(ADMIN_SEQS)
        .copied()
        .collect();
    seqs.sort();
    seqs.dedup();
    let all = ALL_TABLES.join(", ");
    let mut s = format!("REVOKE ALL ON {all} FROM PUBLIC;\n");
    emit(&mut s, server_role, &union, &seqs);
    for r in no_access {
        assert!(ident_ok(r), "invalid role name {r:?}");
        s.push_str(&format!("REVOKE ALL ON {all} FROM {r};\n"));
        s.push_str(&format!(
            "REVOKE ALL ON ALL SEQUENCES IN SCHEMA public FROM {r};\n"
        ));
    }
    s
}

/// Tables holding credential hashes; never readable by inspection roles.
const SECRET_TABLES: &[&str] = &["agents", "admins", "workers"];

/// `deploy/sql/grants.sql`: the reference deployment runs the whole control
/// plane as `arena_api`; workers (`arena_worker`) have no database access at
/// all (they use the worker HTTP API); `arena_readonly` may read everything
/// except credential tables.
pub fn deploy_grants_sql() -> String {
    let mut s = String::from(
        "-- Generated from server/arena-db/src/roles.rs (`arena-server grants-sql`). Do not edit by hand;\n\
         -- a server test fails if this file drifts from the schema.\n\
         -- Run after every `arena-server migrate`, as arena_owner or a superuser:\n\
         --   psql -v ON_ERROR_STOP=1 -d arena -f grants.sql\n\
         --\n\
         --   arena_api      the control plane (public API, worker gateway, admin): union of the\n\
         --                  split roles' privileges; no DELETE/TRUNCATE anywhere. Append-only and\n\
         --                  immutable tables are additionally enforced by triggers.\n\
         --   arena_worker   NO database access: workers only reach the internal worker API (8472).\n\
         --   arena_readonly SELECT on everything except credential-hash tables.\n\
         \\set ON_ERROR_STOP on\n\
         BEGIN;\n",
    );
    s.push_str(&single_role_grants_sql("arena_api", &["arena_worker"]));
    let all = ALL_TABLES.join(", ");
    let readable: Vec<&str> = ALL_TABLES
        .iter()
        .copied()
        .filter(|t| !SECRET_TABLES.contains(t))
        .collect();
    s.push_str(&format!("REVOKE ALL ON {all} FROM arena_readonly;\n"));
    s.push_str(&format!(
        "GRANT SELECT ON {} TO arena_readonly;\n",
        readable.join(", ")
    ));
    s.push_str("COMMIT;\n");
    s
}

/// Full script: create NOLOGIN roles if missing, then grants. Operators attach
/// LOGIN + password (or certificate auth) to these roles, or grant them to
/// login roles.
pub fn roles_script(r: RoleNames<'_>) -> String {
    let mut s = String::from(
        "-- Generated by `arena-server roles-sql` (server/arena-db/src/roles.rs). Do not edit.\n\
         -- Run as the schema owner after `arena-server migrate`.\n",
    );
    for role in [r.api, r.worker, r.admin] {
        assert!(ident_ok(role));
        s.push_str(&format!(
            "DO $$ BEGIN IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = '{role}') THEN \
             CREATE ROLE {role} NOLOGIN; END IF; END $$;\n"
        ));
    }
    s.push_str(&grants_sql(r));
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn checked_in_roles_sql_is_current() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/sql/roles.sql");
        let want = roles_script(DEFAULT_ROLES);
        if std::env::var_os("UPDATE_ROLES_SQL").is_some() {
            std::fs::write(path, &want).unwrap();
        }
        let have = std::fs::read_to_string(path).unwrap_or_default();
        assert_eq!(
            have, want,
            "run with UPDATE_ROLES_SQL=1 to regenerate {path}"
        );
    }
    #[test]
    fn deploy_grants_sql_is_current() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../deploy/sql/grants.sql");
        let want = deploy_grants_sql();
        if std::env::var_os("UPDATE_ROLES_SQL").is_some() {
            std::fs::write(path, &want).unwrap();
        }
        let have = std::fs::read_to_string(path).unwrap_or_default();
        assert_eq!(
            have, want,
            "run with UPDATE_ROLES_SQL=1 to regenerate {path}"
        );
    }
    #[test]
    fn no_delete_grants() {
        for s in [grants_sql(DEFAULT_ROLES), deploy_grants_sql()] {
            assert!(
                !s.contains("GRANT DELETE")
                    && !s.contains("GRANT TRUNCATE")
                    && !s.contains("GRANT ALL")
            );
        }
    }
    #[test]
    #[should_panic]
    fn rejects_bad_names() {
        grants_sql(RoleNames {
            api: "x; drop",
            worker: "w",
            admin: "a",
        });
    }
}

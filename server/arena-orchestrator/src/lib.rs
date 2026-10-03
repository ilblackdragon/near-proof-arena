//! Pipeline state machine of the arena judge.
//!
//! ```text
//! RECEIVED --VALIDATE--> VALIDATED --BUILD--> BUILT --FORMAL_CHECK (or cache)--> FORMAL_CHECKED
//!   --CONFORMANCE + ADVERSARIAL (parallel)--> CONFORMANCE_CHECKED --BENCHMARK--> BENCHMARKED --> DECIDED
//! ```
//!
//! The control plane enqueues one durable job per stage; workers lease jobs
//! over HTTP (`FOR UPDATE SKIP LOCKED`), heartbeat, and complete or fail them.
//! Every transition runs in one database transaction that first locks the
//! run row, so concurrent completions of parallel jobs are serialized and the
//! join is exact.
//!
//! * Experimental tier: the formal gates and `ARTIFACT_BINDING` are
//!   diagnostic (`ChallengeDefinition::blocking_obligations`): reported with
//!   `mandatory = false`, never fail-fast, never in the decision; when they
//!   did not all pass the run carries their reason codes plus
//!   `OBLIGATION_UNDISCHARGED`. Formal and demo tier are unchanged.
//! * Fail-fast: after any mandatory `FAIL` the run is decided immediately;
//!   outstanding jobs are cancelled and the required gates that never ran are
//!   recorded in `not_run_gates`.
//! * `UNKNOWN` mandatory gates make the decision `INCONCLUSIVE` (via
//!   [`arena_types::decide`]).
//! * Infrastructure failures are retried with backoff up to `max_attempts`
//!   (lease expiry counts as an attempt), then the run is `INFRA_ERROR`.
//! * Lease fencing: every lease has a fresh `lease_id`; stale workers cannot
//!   heartbeat/complete/fail a job that was re-leased.

pub mod cache;
pub mod normalize;
pub mod report;
pub mod score;
pub mod signer;

use arena_db::challenge::StoredChallenge;
use arena_db::views::{Run, SubmissionRow};
use arena_db::{audit, enum_str, json, rfc3339, tier_min, tier_rank, Actor, DbError, WorkerRow};
use arena_jobs::sanitize::{sanitize_text, MAX_ERROR_BYTES};
use arena_jobs::*;
use arena_types::{
    challenge::Tier, decide, ChangeClass, Decision, GateResult, GateStatus, ObligationId,
    ReasonCode, Stage, VerifiedSurface,
};
use ed25519_dalek::VerifyingKey;
use serde_json::json as j;
use signer::ReportSigner;
use sqlx::{PgConnection, PgPool};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use uuid::Uuid;

#[derive(Clone, Debug)]
pub struct Config {
    /// Attempts per job (lease expiries count) before the run is INFRA_ERROR.
    pub max_attempts: i32,
    /// Base retry delay; attempt `n` waits `base * 2^(n-1)`.
    pub retry_backoff: Duration,
    pub lease_default: Duration,
    pub lease_min: Duration,
    pub lease_max: Duration,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            retry_backoff: Duration::from_secs(5),
            lease_default: Duration::from_secs(300),
            lease_min: Duration::from_secs(10),
            lease_max: Duration::from_secs(3600),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum OrchError {
    #[error("not found: {0}")]
    NotFound(String),
    #[error("lease lost (expired, re-leased, or not owned by this worker)")]
    LeaseLost,
    #[error("run was cancelled or already decided")]
    Cancelled,
    #[error("invalid job result: {0}")]
    InvalidResult(String),
    #[error("conflict: {0}")]
    Conflict(String),
    #[error(transparent)]
    Db(#[from] DbError),
}

impl From<sqlx::Error> for OrchError {
    fn from(e: sqlx::Error) -> Self {
        OrchError::Db(DbError::Sqlx(e))
    }
}

pub type Result<T, E = OrchError> = std::result::Result<T, E>;

/// Everything a transition needs about one run (run row locked).
pub(crate) struct Ctx {
    pub sub: SubmissionRow,
    pub run: Run,
    pub chal: StoredChallenge,
}

enum Finish {
    Completed,
    FailFast,
    Blocked(String),
    Infra(String),
    Cancelled(Actor),
}

#[derive(sqlx::FromRow)]
struct JobRow {
    id: Uuid,
    kind: String,
    state: String,
    attempt: i32,
    max_attempts: i32,
    lease_id: Option<Uuid>,
    lease_owner: Option<String>,
    live: bool,
}

const JOB_COLS: &str = "id, kind, state, attempt, max_attempts, lease_id, lease_owner, \
    (lease_until IS NOT NULL AND lease_until >= now()) AS live";

pub struct Orchestrator {
    pub cfg: Config,
    signer: Arc<ReportSigner>,
    gov_keys: Arc<Vec<VerifyingKey>>,
}

impl Orchestrator {
    pub fn new(cfg: Config, signer: Arc<ReportSigner>, gov_keys: Arc<Vec<VerifyingKey>>) -> Self {
        Self {
            cfg,
            signer,
            gov_keys,
        }
    }

    pub fn report_public_key_hex(&self) -> String {
        self.signer.public_key_hex()
    }

    pub fn governance_keys(&self) -> &[VerifyingKey] {
        &self.gov_keys
    }

    // ------------------------------------------------------------------ context

    async fn load_ctx(&self, conn: &mut PgConnection, run_id: &str) -> Result<Ctx> {
        let run = arena_db::views::run_for_update(conn, run_id)
            .await?
            .ok_or_else(|| OrchError::NotFound(format!("run {run_id}")))?;
        let sub = arena_db::views::submission(&mut *conn, &run.submission_id)
            .await?
            .ok_or_else(|| OrchError::NotFound(format!("submission {}", run.submission_id)))?;
        let chal = arena_db::challenge::load(&mut *conn, &sub.challenge_id, &self.gov_keys)
            .await?
            .ok_or_else(|| OrchError::NotFound(format!("challenge {}", sub.challenge_id)))?;
        Ok(Ctx { sub, run, chal })
    }

    fn job_ctx(ctx: &Ctx) -> JobContext {
        JobContext {
            submission_id: ctx.sub.id.clone(),
            run_id: ctx.run.id.clone(),
            challenge_id: ctx.chal.id.clone(),
            challenge_digest: ctx.chal.digest.clone(),
            tier: ctx.run.challenge_tier,
            package_digest: arena_types::Digest::try_from(ctx.sub.package_digest.clone())
                .expect("DB constraint"),
        }
    }

    async fn enqueue(&self, conn: &mut PgConnection, ctx: &Ctx, spec: JobSpec) -> Result<Uuid> {
        let id = Uuid::new_v4();
        let kind = spec.kind();
        sqlx::query(
            "INSERT INTO jobs (id, run_id, submission_id, kind, tier_rank, payload, state, max_attempts)
             VALUES ($1, $2, $3, $4, $5, $6, 'queued', $7)",
        )
        .bind(id)
        .bind(&ctx.run.id)
        .bind(&ctx.sub.id)
        .bind(kind.as_str())
        .bind(tier_rank(ctx.run.challenge_tier))
        .bind(json(&spec))
        .bind(self.cfg.max_attempts)
        .execute(&mut *conn)
        .await?;
        audit::record(
            &mut *conn,
            &Actor::system(),
            "job.enqueued",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({ "job_id": id, "kind": kind }),
        )
        .await?;
        Ok(id)
    }

    async fn set_stage(&self, conn: &mut PgConnection, ctx: &mut Ctx, stage: Stage) -> Result<()> {
        sqlx::query("UPDATE runs SET stage = $2 WHERE id = $1")
            .bind(&ctx.run.id)
            .bind(enum_str(&stage))
            .execute(&mut *conn)
            .await?;
        ctx.run.stage = stage;
        audit::record(
            &mut *conn,
            &Actor::system(),
            "run.stage",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({ "stage": stage }),
        )
        .await?;
        Ok(())
    }

    async fn run_gates(conn: &mut PgConnection, run_id: &str) -> Result<Vec<GateResult>> {
        Ok(arena_db::views::gates_of(&mut *conn, &[run_id.to_string()])
            .await?
            .remove(run_id)
            .unwrap_or_default())
    }

    async fn job_states(conn: &mut PgConnection, run_id: &str) -> Result<HashMap<JobKind, String>> {
        let rows: Vec<(String, String)> =
            sqlx::query_as("SELECT kind, state FROM jobs WHERE run_id = $1")
                .bind(run_id)
                .fetch_all(&mut *conn)
                .await?;
        rows.into_iter()
            .map(|(k, s)| Ok((k.parse::<JobKind>().map_err(DbError::Corrupt)?, s)))
            .collect()
    }

    async fn insert_gate(
        conn: &mut PgConnection,
        ctx: &Ctx,
        job_id: Option<Uuid>,
        g: &GateResult,
        actor: &Actor,
    ) -> Result<()> {
        sqlx::query(
            "INSERT INTO gate_results (run_id, job_id, gate, mandatory, status, result) VALUES ($1, $2, $3, $4, $5, $6)",
        )
        .bind(&ctx.run.id)
        .bind(job_id)
        .bind(enum_str(&g.gate))
        .bind(g.mandatory)
        .bind(enum_str(&g.status))
        .bind(json(g))
        .execute(&mut *conn)
        .await?;
        audit::record(
            &mut *conn,
            actor,
            "gate.result",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({
                "gate": g.gate, "status": g.status, "mandatory": g.mandatory,
                "reason_codes": g.reason_codes, "reused_from": g.reused_from,
            }),
        )
        .await?;
        Ok(())
    }

    // ------------------------------------------------------------------ runs

    /// Create a new run for `submission_id` and enqueue its first job. Must be
    /// called inside the caller's transaction (after the submission insert).
    pub async fn start_run(
        &self,
        conn: &mut PgConnection,
        submission_id: &str,
        trigger: &str,
        actor: &Actor,
    ) -> Result<String> {
        let sub = arena_db::views::submission(&mut *conn, submission_id)
            .await?
            .ok_or_else(|| OrchError::NotFound(format!("submission {submission_id}")))?;
        let chal = arena_db::challenge::load(&mut *conn, &sub.challenge_id, &self.gov_keys)
            .await?
            .ok_or_else(|| OrchError::NotFound(format!("challenge {}", sub.challenge_id)))?;
        let pending: Option<(String,)> =
            sqlx::query_as("SELECT id FROM runs WHERE submission_id = $1 AND decision IS NULL")
                .bind(submission_id)
                .fetch_optional(&mut *conn)
                .await?;
        if pending.is_some() {
            return Err(OrchError::Conflict("submission has a pending run".into()));
        }
        let (n,): (i32,) = sqlx::query_as(
            "SELECT COALESCE(MAX(run_number), 0) + 1 FROM runs WHERE submission_id = $1",
        )
        .bind(submission_id)
        .fetch_one(&mut *conn)
        .await?;
        let run_id = arena_db::new_id("run");
        let tier = enum_str(&chal.tier);
        sqlx::query(
            "INSERT INTO runs (id, submission_id, run_number, trigger, requested_by, challenge_tier, tier, stage)
             VALUES ($1, $2, $3, $4, $5, $6, $6, 'RECEIVED')",
        )
        .bind(&run_id)
        .bind(submission_id)
        .bind(n)
        .bind(trigger)
        .bind(format!("{}:{}", actor.kind.as_str(), actor.id))
        .bind(&tier)
        .execute(&mut *conn)
        .await?;
        audit::record(
            &mut *conn,
            actor,
            "run.created",
            Some(submission_id),
            Some(&run_id),
            true,
            j!({ "run_number": n, "trigger": trigger, "tier": chal.tier }),
        )
        .await?;
        let ctx = self.load_ctx(conn, &run_id).await?;
        self.enqueue(
            conn,
            &ctx,
            JobSpec::Validate(ValidateJob {
                ctx: Self::job_ctx(&ctx),
                challenge: ctx.chal.definition.clone(),
            }),
        )
        .await?;
        Ok(run_id)
    }

    /// Drive the state machine as far as possible without waiting on a worker.
    async fn advance(&self, conn: &mut PgConnection, ctx: &mut Ctx) -> Result<()> {
        loop {
            if ctx.run.decision.is_some() {
                return Ok(());
            }
            let gates = Self::run_gates(conn, &ctx.run.id).await?;
            if gates
                .iter()
                .any(|g| g.mandatory && g.status == GateStatus::Fail)
            {
                return self.finalize(conn, ctx, Finish::FailFast).await;
            }
            let jobs = Self::job_states(conn, &ctx.run.id).await?;
            let exists = |k: JobKind| jobs.contains_key(&k);
            let done = |k: JobKind| jobs.get(&k).is_some_and(|s| s == "done");
            let def = ctx.chal.definition.clone();
            match ctx.run.stage {
                Stage::Received => {
                    if !done(JobKind::Validate) {
                        return Ok(());
                    }
                    self.set_stage(conn, ctx, Stage::Validated).await?;
                }
                Stage::Validated => {
                    if !exists(JobKind::Build) {
                        let Some(manifest) = ctx.run.manifest.clone() else {
                            return self
                                .finalize(
                                    conn,
                                    ctx,
                                    Finish::Blocked("no validated manifest".into()),
                                )
                                .await;
                        };
                        let spec = JobSpec::Build(BuildJob {
                            ctx: Self::job_ctx(ctx),
                            challenge: def,
                            manifest,
                        });
                        self.enqueue(conn, ctx, spec).await?;
                        return Ok(());
                    }
                    if !done(JobKind::Build) {
                        return Ok(());
                    }
                    self.set_stage(conn, ctx, Stage::Built).await?;
                }
                Stage::Built => {
                    let needs_formal = def
                        .required_obligations
                        .iter()
                        .any(|o| JobKind::FormalCheck.owned_gates().contains(o));
                    if !needs_formal {
                        self.set_stage(conn, ctx, Stage::FormalChecked).await?;
                        continue;
                    }
                    if !exists(JobKind::FormalCheck) {
                        let (Some(manifest), Some(build), Some(vs)) = (
                            ctx.run.manifest.clone(),
                            ctx.run.build_outputs.clone(),
                            ctx.run.verified_surface.clone(),
                        ) else {
                            return self
                                .finalize(conn, ctx, Finish::Blocked("no build outputs".into()))
                                .await;
                        };
                        if self.reuse_formal(conn, ctx, &vs).await? {
                            self.set_stage(conn, ctx, Stage::FormalChecked).await?;
                            continue;
                        }
                        let spec = JobSpec::FormalCheck(FormalCheckJob {
                            ctx: Self::job_ctx(ctx),
                            challenge: def,
                            manifest,
                            build,
                            verified_surface: vs,
                        });
                        self.enqueue(conn, ctx, spec).await?;
                        return Ok(());
                    }
                    if !done(JobKind::FormalCheck) {
                        return Ok(());
                    }
                    self.set_stage(conn, ctx, Stage::FormalChecked).await?;
                }
                Stage::FormalChecked => {
                    if !exists(JobKind::Conformance) && !exists(JobKind::Adversarial) {
                        let Some(e) = self.exec_job(ctx) else {
                            return self
                                .finalize(conn, ctx, Finish::Blocked("no build outputs".into()))
                                .await;
                        };
                        self.enqueue(conn, ctx, JobSpec::Conformance(e.clone()))
                            .await?;
                        self.enqueue(conn, ctx, JobSpec::Adversarial(e)).await?;
                        return Ok(());
                    }
                    if !(done(JobKind::Conformance) && done(JobKind::Adversarial)) {
                        return Ok(());
                    }
                    self.set_stage(conn, ctx, Stage::ConformanceChecked).await?;
                }
                Stage::ConformanceChecked => {
                    if !exists(JobKind::Benchmark) {
                        let Some(e) = self.exec_job(ctx) else {
                            return self
                                .finalize(conn, ctx, Finish::Blocked("no build outputs".into()))
                                .await;
                        };
                        self.enqueue(conn, ctx, JobSpec::Benchmark(e)).await?;
                        return Ok(());
                    }
                    if !done(JobKind::Benchmark) {
                        return Ok(());
                    }
                    self.set_stage(conn, ctx, Stage::Benchmarked).await?;
                }
                Stage::Benchmarked => return self.finalize(conn, ctx, Finish::Completed).await,
                Stage::Decided => return Ok(()),
            }
        }
    }

    fn exec_job(&self, ctx: &Ctx) -> Option<ExecJob> {
        Some(ExecJob {
            ctx: Self::job_ctx(ctx),
            challenge: ctx.chal.definition.clone(),
            manifest: ctx.run.manifest.clone()?,
            build: ctx.run.build_outputs.clone()?,
        })
    }

    /// Reuse cached formal gate results if a live entry exists for the run's
    /// full content-addressed key at a sufficient tier.
    async fn reuse_formal(
        &self,
        conn: &mut PgConnection,
        ctx: &mut Ctx,
        vs: &VerifiedSurface,
    ) -> Result<bool> {
        let key = cache::cache_key(&ctx.chal.digest, &ctx.chal.definition, vs);
        let Some(entry) = cache::lookup(conn, &key).await? else {
            return Ok(false);
        };
        if entry.tier_rank < tier_rank(ctx.run.challenge_tier) {
            return Ok(false);
        }
        let required = ctx.chal.definition.blocking_obligations();
        for g in &entry.gates {
            let mut g = g.clone();
            g.mandatory = required.contains(&g.gate);
            g.reused_from = Some(entry.source_submission_id.clone());
            Self::insert_gate(conn, ctx, None, &g, &Actor::system()).await?;
        }
        // native-lean route: the judge-built verifier is a function of the
        // verified surface (formal tree, certificate), which is identical, so
        // the source run's build is reused with the formal results.
        let src_build: Option<Option<serde_json::Value>> =
            sqlx::query_scalar("SELECT build_outputs FROM runs WHERE id = $1")
                .bind(&entry.source_run_id)
                .fetch_optional(&mut *conn)
                .await?;
        if let (Some(Some(v)), Some(mine)) = (src_build, ctx.run.build_outputs.as_mut()) {
            if let Ok(src) = serde_json::from_value::<BuildOutputs>(v) {
                if src.native_verifier.is_some() && mine.native_verifier.is_none() {
                    mine.native_verifier = src.native_verifier;
                    sqlx::query("UPDATE runs SET build_outputs = $2 WHERE id = $1")
                        .bind(&ctx.run.id)
                        .bind(json(&*mine))
                        .execute(&mut *conn)
                        .await?;
                }
            }
        }
        let graph = entry.evidence_graph.as_ref().map(|eg| {
            normalize::merge_graphs(ctx.run.evidence_graph.clone(), eg, JobKind::FormalCheck)
        });
        sqlx::query("UPDATE runs SET evidence_graph = COALESCE($2, evidence_graph) WHERE id = $1")
            .bind(&ctx.run.id)
            .bind(graph.as_ref().map(json))
            .execute(&mut *conn)
            .await?;
        if graph.is_some() {
            ctx.run.evidence_graph = graph;
        }
        audit::record(
            &mut *conn,
            &Actor::system(),
            "formal.cache_reused",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({ "key": key, "source_submission_id": entry.source_submission_id, "source_run_id": entry.source_run_id }),
        )
        .await?;
        Ok(true)
    }

    async fn finalize(&self, conn: &mut PgConnection, ctx: &mut Ctx, finish: Finish) -> Result<()> {
        let def = &ctx.chal.definition;
        let gates = Self::run_gates(conn, &ctx.run.id).await?;
        let mut not_run: Vec<ObligationId> = def
            .required_obligations
            .iter()
            .copied()
            .filter(|o| !gates.iter().any(|g| g.gate == *o))
            .collect();
        not_run.sort();
        not_run.dedup();
        let mut reasons: Vec<ReasonCode> = Vec::new();
        let (mut decision, mut accepted) = match &finish {
            Finish::Infra(_) => (Decision::InfraError, false),
            Finish::Cancelled(_) => (Decision::Cancelled, false),
            // Experimental tier: formal gates are diagnostic, so they are
            // left out of the decision (formal/demo: every required gate).
            Finish::Completed | Finish::FailFast | Finish::Blocked(_) => decide(
                &gates,
                &def.blocking_obligations(),
                &def.not_applicable_gates,
            ),
        };
        for g in gates
            .iter()
            .filter(|g| g.mandatory && matches!(g.status, GateStatus::Fail | GateStatus::Unknown))
        {
            reasons.extend(g.reason_codes.iter().copied());
        }
        match &finish {
            Finish::Infra(_) => reasons.push(ReasonCode::InfraError),
            Finish::Cancelled(_) => reasons.push(ReasonCode::Cancelled),
            _ => {}
        }
        if !not_run.is_empty() && decision != Decision::Admitted {
            reasons.push(ReasonCode::ObligationUndischarged);
        }
        // Experimental: diagnostic (formal) gates never decide the run, but a
        // run whose formal obligations did not all pass says so in its reason
        // codes, so an experimental ADMITTED is never read as formal acceptance.
        let diagnostic = def.diagnostic_obligations();
        let diag_open: Vec<&GateResult> = gates
            .iter()
            .filter(|g| {
                diagnostic.contains(&g.gate)
                    && g.status != GateStatus::Pass
                    && !(g.status == GateStatus::NotApplicable
                        && def.not_applicable_gates.contains(&g.gate))
            })
            .collect();
        for g in &diag_open {
            reasons.extend(g.reason_codes.iter().copied());
        }
        if !diag_open.is_empty() || diagnostic.iter().any(|o| not_run.contains(o)) {
            reasons.push(ReasonCode::ObligationUndischarged);
        }
        if ctx.run.tier == Tier::Demo || ctx.run.tier != ctx.run.challenge_tier {
            reasons.push(ReasonCode::DemoOnly);
        }
        // Defense in depth: a formal challenge can only be admitted by a
        // formal-tier evaluation (workers below that tier are never leased its
        // jobs in the first place).
        if ctx.run.challenge_tier == Tier::Formal
            && ctx.run.tier != Tier::Formal
            && decision == Decision::Admitted
        {
            decision = Decision::Inconclusive;
            accepted = false;
        }
        let mut seen = std::collections::HashSet::new();
        reasons.retain(|r| seen.insert(*r));
        let score = if accepted {
            ctx.run.benchmark.as_ref().and_then(|b| b.score_milli)
        } else {
            None
        };
        sqlx::query(
            "UPDATE runs SET stage = 'DECIDED', decision = $2, accepted = $3, score_milli = $4,
                reason_codes = $5, not_run_gates = $6, decided_at = now() WHERE id = $1",
        )
        .bind(&ctx.run.id)
        .bind(enum_str(&decision))
        .bind(accepted)
        .bind(score.map(|s| s as i64))
        .bind(json(&reasons))
        .bind(json(&not_run))
        .execute(&mut *conn)
        .await?;
        let cancelled = sqlx::query(
            "UPDATE jobs SET state = 'cancelled', finished_at = now(), updated_at = now()
             WHERE run_id = $1 AND state IN ('queued', 'leased')",
        )
        .bind(&ctx.run.id)
        .execute(&mut *conn)
        .await?
        .rows_affected();
        let (actor, detail) = match &finish {
            Finish::Completed => (Actor::system(), "completed".to_string()),
            Finish::FailFast => (
                Actor::system(),
                "fail-fast after mandatory FAIL".to_string(),
            ),
            Finish::Blocked(w) => (Actor::system(), format!("pipeline blocked: {w}")),
            Finish::Infra(w) => (Actor::system(), format!("infrastructure error: {w}")),
            Finish::Cancelled(a) => (a.clone(), "cancelled".to_string()),
        };
        audit::record(
            &mut *conn,
            &actor,
            "run.decided",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({
                "decision": decision, "accepted": accepted, "score_milli": score,
                "reason_codes": reasons, "not_run_gates": not_run, "tier": ctx.run.tier,
                "detail": detail, "cancelled_jobs": cancelled,
            }),
        )
        .await?;
        ctx.run.stage = Stage::Decided;
        ctx.run.decision = Some(decision);
        report::build_and_store(conn, ctx, &self.signer).await?;
        Ok(())
    }

    // ------------------------------------------------------------------ worker API

    fn lease_secs(&self, req: Option<u32>) -> f64 {
        let d = req
            .map(|s| Duration::from_secs(s as u64))
            .unwrap_or(self.cfg.lease_default);
        d.clamp(self.cfg.lease_min, self.cfg.lease_max)
            .as_secs_f64()
    }

    /// Lease the oldest runnable job this worker may execute: queued jobs whose
    /// backoff elapsed, or leased jobs whose lease expired (crash recovery).
    /// Jobs of a tier above the worker's registered capability are never
    /// offered (e.g. `bwrap-dev` workers only ever see demo-tier work).
    pub async fn lease(
        &self,
        pool: &PgPool,
        worker: &WorkerRow,
        req: &LeaseRequest,
    ) -> Result<Option<LeasedJob>> {
        let kinds: Vec<String> = req.kinds.iter().map(|k| k.as_str().to_string()).collect();
        let lease_id = Uuid::new_v4();
        let mut tx = pool.begin().await?;
        #[allow(clippy::type_complexity)]
        let row: Option<(Uuid, String, String, String, i32, i32, time::OffsetDateTime, serde_json::Value, String, Option<String>)> =
            sqlx::query_as(
                "WITH cand AS (
                    SELECT id, state AS prev_state, lease_owner AS prev_owner FROM jobs
                    WHERE ((state = 'queued' AND run_after <= now())
                           OR (state = 'leased' AND lease_until < now() AND attempt < max_attempts))
                      AND tier_rank <= $1
                      AND (cardinality($2::text[]) = 0 OR kind = ANY($2))
                    ORDER BY run_after, created_at, id
                    LIMIT 1 FOR UPDATE SKIP LOCKED)
                 UPDATE jobs j SET state = 'leased', attempt = j.attempt + 1, lease_id = $3, lease_owner = $4,
                    lease_until = now() + make_interval(secs => $5), updated_at = now()
                 FROM cand WHERE j.id = cand.id
                 RETURNING j.id, j.run_id, j.submission_id, j.kind, j.attempt, j.max_attempts, j.lease_until,
                    j.payload, cand.prev_state, cand.prev_owner",
            )
            .bind(worker.tier_cap)
            .bind(&kinds)
            .bind(lease_id)
            .bind(&worker.id)
            .bind(self.lease_secs(req.lease_seconds))
            .fetch_optional(&mut *tx)
            .await?;
        let Some((
            job_id,
            run_id,
            sub_id,
            kind,
            attempt,
            max_attempts,
            until,
            payload,
            prev_state,
            prev_owner,
        )) = row
        else {
            return Ok(None);
        };
        if prev_state == "leased" {
            audit::record(
                &mut *tx,
                &Actor::system(),
                "job.lease_expired",
                Some(&sub_id),
                Some(&run_id),
                true,
                j!({ "job_id": job_id, "kind": kind, "attempt": attempt - 1, "previous_worker": prev_owner }),
            )
            .await?;
        }
        audit::record(
            &mut *tx,
            &Actor::worker(&worker.id),
            "job.leased",
            Some(&sub_id),
            Some(&run_id),
            true,
            j!({ "job_id": job_id, "kind": kind, "attempt": attempt, "sandbox_backend": worker.sandbox_backend }),
        )
        .await?;
        tx.commit().await?;
        let spec: JobSpec = serde_json::from_value(payload).map_err(DbError::corrupt)?;
        Ok(Some(LeasedJob {
            job_id: job_id.to_string(),
            lease_id: lease_id.to_string(),
            submission_id: sub_id,
            run_id,
            kind: kind.parse().map_err(DbError::Corrupt)?,
            attempt: attempt as u32,
            max_attempts: max_attempts as u32,
            lease_until: rfc3339(until),
            protocol: JOB_PROTOCOL_VERSION.to_string(),
            spec,
        }))
    }

    fn check_lease(job: &JobRow, lease_id: Uuid, worker: &WorkerRow) -> Result<()> {
        let mine = job.lease_id == Some(lease_id)
            && job.lease_owner.as_deref() == Some(worker.id.as_str());
        if job.state == "cancelled" && mine {
            return Err(OrchError::Cancelled);
        }
        if job.state != "leased" || !mine || !job.live {
            return Err(OrchError::LeaseLost);
        }
        Ok(())
    }

    pub async fn heartbeat(
        &self,
        pool: &PgPool,
        worker: &WorkerRow,
        job_id: Uuid,
        req: &HeartbeatRequest,
    ) -> Result<HeartbeatResponse> {
        let lease_id = Uuid::parse_str(&req.lease_id).map_err(|_| OrchError::LeaseLost)?;
        let row: Option<(time::OffsetDateTime,)> = sqlx::query_as(
            "UPDATE jobs SET lease_until = now() + make_interval(secs => $4), updated_at = now()
             WHERE id = $1 AND lease_id = $2 AND lease_owner = $3 AND state = 'leased' AND lease_until >= now()
             RETURNING lease_until",
        )
        .bind(job_id)
        .bind(lease_id)
        .bind(&worker.id)
        .bind(self.lease_secs(req.extend_seconds))
        .fetch_optional(pool)
        .await?;
        if let Some((until,)) = row {
            return Ok(HeartbeatResponse {
                lease_until: rfc3339(until),
                cancelled: false,
            });
        }
        let job: Option<JobRow> =
            sqlx::query_as(&format!("SELECT {JOB_COLS} FROM jobs WHERE id = $1"))
                .bind(job_id)
                .fetch_optional(pool)
                .await?;
        let job = job.ok_or_else(|| OrchError::NotFound(format!("job {job_id}")))?;
        match Self::check_lease(&job, lease_id, worker) {
            Err(OrchError::Cancelled) => Ok(HeartbeatResponse {
                lease_until: rfc3339(time::OffsetDateTime::now_utc()),
                cancelled: true,
            }),
            Err(e) => Err(e),
            Ok(()) => Err(OrchError::LeaseLost),
        }
    }

    /// Lock the job's run, then the job, and verify the caller's lease.
    async fn lock_job(
        &self,
        conn: &mut PgConnection,
        job_id: Uuid,
        lease_id: Uuid,
        worker: &WorkerRow,
    ) -> Result<(Ctx, JobRow)> {
        let run_id: Option<(String,)> = sqlx::query_as("SELECT run_id FROM jobs WHERE id = $1")
            .bind(job_id)
            .fetch_optional(&mut *conn)
            .await?;
        let (run_id,) = run_id.ok_or_else(|| OrchError::NotFound(format!("job {job_id}")))?;
        let ctx = self.load_ctx(conn, &run_id).await?;
        let job: JobRow = sqlx::query_as(&format!(
            "SELECT {JOB_COLS} FROM jobs WHERE id = $1 FOR UPDATE"
        ))
        .bind(job_id)
        .fetch_one(&mut *conn)
        .await?;
        Self::check_lease(&job, lease_id, worker)?;
        if ctx.run.decision.is_some() {
            return Err(OrchError::Cancelled);
        }
        Ok((ctx, job))
    }

    /// Record an infrastructure failure of the current attempt: retry with
    /// backoff, or decide the run as INFRA_ERROR when attempts are exhausted.
    async fn job_failed(
        &self,
        conn: &mut PgConnection,
        ctx: &mut Ctx,
        job: &JobRow,
        error: &str,
        retryable: bool,
        actor: &Actor,
    ) -> Result<bool> {
        let error = sanitize_text(error, MAX_ERROR_BYTES);
        let retry = retryable && job.attempt < job.max_attempts;
        if retry {
            let backoff =
                self.cfg.retry_backoff.as_secs_f64() * 2f64.powi((job.attempt - 1).max(0));
            sqlx::query(
                "UPDATE jobs SET state = 'queued', lease_id = NULL, lease_owner = NULL, lease_until = NULL,
                    last_error = $2, run_after = now() + make_interval(secs => $3), updated_at = now()
                 WHERE id = $1",
            )
            .bind(job.id)
            .bind(&error)
            .bind(backoff)
            .execute(&mut *conn)
            .await?;
        } else {
            sqlx::query(
                "UPDATE jobs SET state = 'failed', last_error = $2, finished_at = now(), updated_at = now() WHERE id = $1",
            )
            .bind(job.id)
            .bind(&error)
            .execute(&mut *conn)
            .await?;
        }
        audit::record(
            &mut *conn,
            actor,
            "job.failed",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({ "job_id": job.id, "kind": job.kind, "attempt": job.attempt, "max_attempts": job.max_attempts,
                 "retrying": retry, "error": error }),
        )
        .await?;
        if !retry {
            let why = format!(
                "{} job failed after {} attempt(s): {error}",
                job.kind, job.attempt
            );
            self.finalize(conn, ctx, Finish::Infra(why)).await?;
        }
        Ok(retry)
    }

    pub async fn fail(
        &self,
        pool: &PgPool,
        worker: &WorkerRow,
        job_id: Uuid,
        req: &FailRequest,
    ) -> Result<AckResponse> {
        let lease_id = Uuid::parse_str(&req.lease_id).map_err(|_| OrchError::LeaseLost)?;
        let mut tx = pool.begin().await?;
        let (mut ctx, job) = self.lock_job(&mut tx, job_id, lease_id, worker).await?;
        let retry = self
            .job_failed(
                &mut tx,
                &mut ctx,
                &job,
                &req.error,
                req.retryable,
                &Actor::worker(&worker.id),
            )
            .await?;
        tx.commit().await?;
        Ok(AckResponse {
            ok: true,
            message: if retry {
                "requeued for retry".into()
            } else {
                "run decided INFRA_ERROR".into()
            },
        })
    }

    pub async fn complete(
        &self,
        pool: &PgPool,
        worker: &WorkerRow,
        job_id: Uuid,
        req: &CompleteRequest,
    ) -> Result<AckResponse> {
        let lease_id = Uuid::parse_str(&req.lease_id).map_err(|_| OrchError::LeaseLost)?;
        let actor = Actor::worker(&worker.id);
        let mut tx = pool.begin().await?;
        let (mut ctx, job) = self.lock_job(&mut tx, job_id, lease_id, worker).await?;
        let kind: JobKind = job.kind.parse().map_err(DbError::Corrupt)?;
        let checked = normalize::check_result(
            kind,
            &req.result,
            &ctx.chal.definition,
            &ctx.chal.id,
            ctx.run.challenge_tier,
            arena_db::tier_from_rank(worker.tier_cap),
        )
        .and_then(|n| self.check_consistency(kind, &ctx, &n).map(|_| n));
        let n = match checked {
            Ok(n) => n,
            Err(msg) => {
                self.job_failed(
                    &mut tx,
                    &mut ctx,
                    &job,
                    &format!("protocol error: {msg}"),
                    true,
                    &actor,
                )
                .await?;
                tx.commit().await?;
                return Err(OrchError::InvalidResult(msg));
            }
        };
        for g in &n.gates {
            Self::insert_gate(&mut tx, &ctx, Some(job.id), g, &actor).await?;
        }
        let stored_result = JobResult {
            gates: n.gates.clone(),
            artifacts: n.artifacts.clone(),
            benchmark: n.benchmark.clone(),
            evidence_graph: n.evidence_graph.clone(),
            manifest: n.manifest.clone(),
            build: n.build.clone(),
            execution: n.execution.clone(),
            log_excerpt: n.log_excerpt.clone(),
            native_verifier: n.native_verifier.clone(),
        };
        sqlx::query(
            "UPDATE jobs SET state = 'done', result = $2, execution = $3, finished_at = now(), updated_at = now() WHERE id = $1",
        )
        .bind(job.id)
        .bind(json(&stored_result))
        .bind(json(&n.execution))
        .execute(&mut *tx)
        .await?;
        audit::record(
            &mut *tx,
            &actor,
            "job.completed",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({ "job_id": job.id, "kind": kind, "attempt": job.attempt, "tier_cap": n.tier_cap,
                 "sandbox_backend": n.execution.sandbox_backend }),
        )
        .await?;
        self.apply_result(&mut tx, &mut ctx, kind, &n).await?;
        self.advance(&mut tx, &mut ctx).await?;
        tx.commit().await?;
        Ok(AckResponse {
            ok: true,
            message: "result recorded".into(),
        })
    }

    /// Cross-checks that need run state (protocol errors, not candidate failures).
    fn check_consistency(
        &self,
        kind: JobKind,
        ctx: &Ctx,
        n: &normalize::Normalized,
    ) -> Result<(), String> {
        if kind == JobKind::Build {
            if let (Some(b), Some(m)) = (&n.build, &ctx.run.manifest) {
                let want = m
                    .formal
                    .as_ref()
                    .map(|f| f.certificate.as_str())
                    .unwrap_or("");
                if b.certificate_decl != want {
                    return Err(format!(
                        "build certificate_decl {:?} does not match manifest certificate {:?}",
                        b.certificate_decl, want
                    ));
                }
            }
        }
        Ok(())
    }

    async fn apply_result(
        &self,
        conn: &mut PgConnection,
        ctx: &mut Ctx,
        kind: JobKind,
        n: &normalize::Normalized,
    ) -> Result<()> {
        let tier = tier_min(ctx.run.tier, n.tier_cap);
        if tier != ctx.run.tier {
            audit::record(
                &mut *conn,
                &Actor::system(),
                "run.tier_capped",
                Some(&ctx.sub.id),
                Some(&ctx.run.id),
                true,
                j!({ "from": ctx.run.tier, "to": tier, "kind": kind, "sandbox_backend": n.execution.sandbox_backend }),
            )
            .await?;
            ctx.run.tier = tier;
        }
        if let Some(eg) = &n.evidence_graph {
            ctx.run.evidence_graph = Some(normalize::merge_graphs(
                ctx.run.evidence_graph.take(),
                eg,
                kind,
            ));
        }
        match kind {
            JobKind::Validate => {
                if let Some(m) = &n.manifest {
                    ctx.run.candidate_name = m.name.clone();
                    ctx.run.backend_family = m.backend_family.clone();
                    ctx.run.manifest = Some(m.clone());
                }
            }
            JobKind::Build => {
                if let (Some(b), true) = (
                    &n.build,
                    n.gates.iter().any(|g| g.status == GateStatus::Pass),
                ) {
                    let Some(vs) = verified_surface(ctx, b) else {
                        // Fail closed: without a complete surface there is no
                        // formal-cache key and the formal stage blocks.
                        ctx.run.build_outputs = n.build.clone();
                        audit::record(
                            &mut *conn,
                            &Actor::system(),
                            "run.verified_surface_incomplete",
                            Some(&ctx.sub.id),
                            Some(&ctx.run.id),
                            true,
                            j!({ "detail": "npai-v1 build reported no verifier_bytecode digest" }),
                        )
                        .await?;
                        return self.persist_run(conn, ctx).await;
                    };
                    let class = self.classify(conn, ctx, &vs).await?;
                    ctx.run.formal_cache_key = Some(
                        cache::cache_key(&ctx.chal.digest, &ctx.chal.definition, &vs).to_string(),
                    );
                    ctx.run.change_class = Some(class);
                    ctx.run.verified_surface = Some(vs);
                }
                ctx.run.build_outputs = n.build.clone();
            }
            JobKind::FormalCheck => {
                // native-lean route: later stages run the judge-built verifier.
                if let (Some(d), Some(b)) = (&n.native_verifier, ctx.run.build_outputs.as_mut()) {
                    if !n.gates.iter().any(|g| g.status == GateStatus::Fail) {
                        b.native_verifier = Some(d.clone());
                    }
                }
                if n.definite {
                    if let (Some(vs), Some(_)) =
                        (&ctx.run.verified_surface, &ctx.run.formal_cache_key)
                    {
                        let key = cache::cache_key(&ctx.chal.digest, &ctx.chal.definition, vs);
                        let stored = cache::store(
                            conn,
                            &key,
                            &ctx.chal.id,
                            &ctx.chal.digest,
                            &ctx.chal.definition,
                            vs,
                            &n.gates,
                            n.evidence_graph.as_ref(),
                            tier_rank(n.tier_cap),
                            &ctx.sub.id,
                            &ctx.run.id,
                        )
                        .await?;
                        if stored {
                            audit::record(
                                &mut *conn,
                                &Actor::system(),
                                "formal.cache_stored",
                                Some(&ctx.sub.id),
                                Some(&ctx.run.id),
                                false,
                                j!({ "key": key }),
                            )
                            .await?;
                        }
                    }
                }
            }
            JobKind::Benchmark => ctx.run.benchmark = n.benchmark.clone(),
            JobKind::Conformance | JobKind::Adversarial => {}
        }
        self.persist_run(conn, ctx).await
    }

    async fn persist_run(&self, conn: &mut PgConnection, ctx: &Ctx) -> Result<()> {
        sqlx::query(
            "UPDATE runs SET tier = $2, candidate_name = $3, backend_family = $4, manifest = $5, build_outputs = $6,
                verified_surface = $7, change_class = $8, formal_cache_key = $9, benchmark = $10, evidence_graph = $11
             WHERE id = $1",
        )
        .bind(&ctx.run.id)
        .bind(enum_str(&ctx.run.tier))
        .bind(&ctx.run.candidate_name)
        .bind(&ctx.run.backend_family)
        .bind(ctx.run.manifest.as_ref().map(json))
        .bind(ctx.run.build_outputs.as_ref().map(json))
        .bind(ctx.run.verified_surface.as_ref().map(json))
        .bind(ctx.run.change_class.as_ref().map(enum_str))
        .bind(&ctx.run.formal_cache_key)
        .bind(ctx.run.benchmark.as_ref().map(json))
        .bind(ctx.run.evidence_graph.as_ref().map(json))
        .execute(&mut *conn)
        .await?;
        Ok(())
    }

    /// Change classification from verified-surface digests (never trusted from the agent).
    async fn classify(
        &self,
        conn: &mut PgConnection,
        ctx: &Ctx,
        vs: &VerifiedSurface,
    ) -> Result<ChangeClass> {
        let Some(parent) = &ctx.sub.parent_id else {
            return Ok(ChangeClass::NoParent);
        };
        let row: Option<(serde_json::Value,)> = sqlx::query_as(
            "SELECT verified_surface FROM runs WHERE submission_id = $1 AND verified_surface IS NOT NULL
             ORDER BY run_number DESC LIMIT 1",
        )
        .bind(parent)
        .fetch_optional(&mut *conn)
        .await?;
        let parent_vs: Option<VerifiedSurface> =
            row.map(|r| arena_db::from_json(r.0)).transpose()?;
        let class = if parent_vs.as_ref() == Some(vs) {
            ChangeClass::ProverOnly
        } else {
            ChangeClass::VerifierOrProtocol
        };
        audit::record(
            &mut *conn,
            &Actor::system(),
            "run.change_class",
            Some(&ctx.sub.id),
            Some(&ctx.run.id),
            true,
            j!({ "change_class": class, "parent": parent }),
        )
        .await?;
        Ok(class)
    }

    /// Requeue / fail jobs whose lease expired after the last allowed attempt
    /// (crash recovery). Jobs with attempts left are re-leased directly by
    /// [`Self::lease`]. Returns the number of jobs reaped.
    pub async fn reap_expired(&self, pool: &PgPool) -> Result<usize> {
        let ids: Vec<(Uuid,)> = sqlx::query_as(
            "SELECT id FROM jobs WHERE state = 'leased' AND lease_until < now() AND attempt >= max_attempts LIMIT 100",
        )
        .fetch_all(pool)
        .await?;
        let mut n = 0;
        for (id,) in ids {
            let mut tx = pool.begin().await?;
            let run_id: (String,) = sqlx::query_as("SELECT run_id FROM jobs WHERE id = $1")
                .bind(id)
                .fetch_one(&mut *tx)
                .await?;
            let mut ctx = self.load_ctx(&mut tx, &run_id.0).await?;
            let job: JobRow = sqlx::query_as(&format!(
                "SELECT {JOB_COLS} FROM jobs WHERE id = $1 FOR UPDATE"
            ))
            .bind(id)
            .fetch_one(&mut *tx)
            .await?;
            // re-check under lock
            if job.state != "leased"
                || job.live
                || job.attempt < job.max_attempts
                || ctx.run.decision.is_some()
            {
                continue;
            }
            self.job_failed(
                &mut tx,
                &mut ctx,
                &job,
                &format!(
                    "lease expired (worker {} presumed crashed) on final attempt",
                    job.lease_owner.as_deref().unwrap_or("?")
                ),
                false,
                &Actor::system(),
            )
            .await?;
            tx.commit().await?;
            n += 1;
        }
        Ok(n)
    }

    /// Cancel the pending run of a submission.
    pub async fn cancel(&self, pool: &PgPool, submission_id: &str, actor: &Actor) -> Result<()> {
        let mut tx = pool.begin().await?;
        let run: Option<(String,)> = sqlx::query_as(
            "SELECT id FROM runs WHERE submission_id = $1 ORDER BY run_number DESC LIMIT 1",
        )
        .bind(submission_id)
        .fetch_optional(&mut *tx)
        .await?;
        let (run_id,) =
            run.ok_or_else(|| OrchError::NotFound(format!("submission {submission_id}")))?;
        let mut ctx = self.load_ctx(&mut tx, &run_id).await?;
        if ctx.run.decision.is_some() {
            return Err(OrchError::Conflict("latest run is already decided".into()));
        }
        self.finalize(&mut tx, &mut ctx, Finish::Cancelled(actor.clone()))
            .await?;
        tx.commit().await?;
        Ok(())
    }

    /// Admin rerun: a new run record; previous runs stay untouched.
    pub async fn rerun(
        &self,
        pool: &PgPool,
        submission_id: &str,
        actor: &Actor,
        reason: &str,
    ) -> Result<String> {
        let mut tx = pool.begin().await?;
        // serialize with other reruns/submits of this submission
        sqlx::query("SELECT pg_advisory_xact_lock(hashtext($1))")
            .bind(submission_id)
            .execute(&mut *tx)
            .await?;
        let run_id = self
            .start_run(&mut tx, submission_id, "rerun", actor)
            .await?;
        audit::record(
            &mut *tx,
            actor,
            "submission.rerun",
            Some(submission_id),
            Some(&run_id),
            true,
            j!({ "reason": reason }),
        )
        .await?;
        tx.commit().await?;
        Ok(run_id)
    }
}

/// The verified surface of a passing build: every input that determines the
/// judge-built admission statement or the code executed as `verify`. `None`
/// when the build is missing a digest the manifest's route requires.
fn verified_surface(ctx: &Ctx, b: &BuildOutputs) -> Option<VerifiedSurface> {
    let manifest = ctx.run.manifest.as_ref();
    let route = manifest
        .and_then(|m| m.entry.verify_route)
        .unwrap_or(arena_types::VerifyRoute::Native);
    let formal = manifest.and_then(|m| m.formal.as_ref());
    let verifier_bytecode = match route {
        arena_types::VerifyRoute::NpaiV1 => Some(b.verifier_bytecode.clone()?),
        _ => None,
    };
    let (verifier_model, verifier_model_module) = match route {
        arena_types::VerifyRoute::NativeLean => (
            formal.and_then(|f| f.verifier_model.clone()),
            formal.and_then(|f| f.verifier_model_module.clone()),
        ),
        _ => (None, None),
    };
    Some(VerifiedSurface {
        challenge_id: ctx.chal.id.clone(),
        verify_artifact: b.verify.clone(),
        prepare_artifact: b.prepare.clone(),
        public_artifacts: b.public_artifacts.clone(),
        formal_tree: b.formal_tree.clone(),
        certificate_decl: b.certificate_decl.clone(),
        checker_image: ctx.chal.definition.toolchain_policy.checker_image.clone(),
        verify_route: Some(route),
        verifier_bytecode,
        verifier_model,
        verifier_model_module,
    })
}

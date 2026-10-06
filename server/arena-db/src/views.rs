//! Read models: submission views and leaderboards.

use crate::{from_json, from_json_opt, parse_enum, rfc3339, DbError};
use arena_jobs::BuildOutputs;
use arena_types::{
    challenge::Tier, evidence::NodeKind, ArtifactRef, AssumptionRef, BenchmarkResult, BuildInfo,
    CandidateManifest, ChallengeDefinition, ChangeClass, Decision, Digest, EvidenceGraph,
    EvidenceRef, GateResult, GateStatus, LeaderboardEntry, LogExcerpt, ObligationId, ReasonCode,
    Revocation, RevocationEvent, Stage, SubmissionView, TrustedBaseEntry, VerifiedSurface,
};
use serde::Serialize;
use sqlx::{PgExecutor, PgPool};
use std::collections::HashMap;
use time::OffsetDateTime;

#[derive(Clone, Debug, sqlx::FromRow)]
pub struct SubmissionRow {
    pub id: String,
    pub agent_id: String,
    pub agent_handle: String,
    pub challenge_id: String,
    pub package_digest: String,
    pub upload_id: String,
    pub parent_id: Option<String>,
    pub idempotency_key: String,
    pub request_digest: String,
    pub created_at: OffsetDateTime,
}

const SUB_COLS: &str =
    "s.id, s.agent_id, a.handle AS agent_handle, s.challenge_id, s.package_digest, \
    s.upload_id, s.parent_id, s.idempotency_key, s.request_digest, s.created_at";

#[derive(Clone, Debug, sqlx::FromRow)]
pub struct RunRowRaw {
    pub id: String,
    pub submission_id: String,
    pub run_number: i32,
    pub trigger: String,
    pub requested_by: String,
    pub challenge_tier: String,
    pub tier: String,
    pub stage: String,
    pub decision: Option<String>,
    pub accepted: Option<bool>,
    pub score_milli: Option<i64>,
    pub change_class: Option<String>,
    pub candidate_name: String,
    pub backend_family: String,
    pub manifest: Option<serde_json::Value>,
    pub build_outputs: Option<serde_json::Value>,
    pub verified_surface: Option<serde_json::Value>,
    pub formal_cache_key: Option<String>,
    pub benchmark: Option<serde_json::Value>,
    pub evidence_graph: Option<serde_json::Value>,
    pub coverage: Option<serde_json::Value>,
    pub reason_codes: serde_json::Value,
    pub not_run_gates: serde_json::Value,
    pub created_at: OffsetDateTime,
    pub updated_at: OffsetDateTime,
    pub decided_at: Option<OffsetDateTime>,
}

pub const RUN_COLS: &str = "id, submission_id, run_number, trigger, requested_by, challenge_tier, tier, \
    stage, decision, accepted, score_milli, change_class, candidate_name, backend_family, manifest, \
    build_outputs, verified_surface, formal_cache_key, benchmark, evidence_graph, coverage, reason_codes, \
    not_run_gates, created_at, updated_at, decided_at";

/// Typed run record.
#[derive(Clone, Debug)]
pub struct Run {
    pub id: String,
    pub submission_id: String,
    pub run_number: i32,
    pub trigger: String,
    pub requested_by: String,
    pub challenge_tier: Tier,
    pub tier: Tier,
    pub stage: Stage,
    pub decision: Option<Decision>,
    pub accepted: Option<bool>,
    pub score_milli: Option<u64>,
    pub change_class: Option<ChangeClass>,
    pub candidate_name: String,
    pub backend_family: String,
    pub manifest: Option<CandidateManifest>,
    pub build_outputs: Option<BuildOutputs>,
    pub verified_surface: Option<VerifiedSurface>,
    pub formal_cache_key: Option<String>,
    pub benchmark: Option<BenchmarkResult>,
    pub evidence_graph: Option<EvidenceGraph>,
    /// v1.7 coverage-tiered challenges: proven coverage (CONFORMANCE).
    pub coverage: Option<arena_types::CoverageReport>,
    pub reason_codes: Vec<ReasonCode>,
    pub not_run_gates: Vec<ObligationId>,
    pub created_at: OffsetDateTime,
    pub updated_at: OffsetDateTime,
    pub decided_at: Option<OffsetDateTime>,
}

impl TryFrom<RunRowRaw> for Run {
    type Error = DbError;
    fn try_from(r: RunRowRaw) -> Result<Self, DbError> {
        Ok(Run {
            id: r.id,
            submission_id: r.submission_id,
            run_number: r.run_number,
            trigger: r.trigger,
            requested_by: r.requested_by,
            challenge_tier: parse_enum(&r.challenge_tier)?,
            tier: parse_enum(&r.tier)?,
            stage: parse_enum(&r.stage)?,
            decision: r.decision.as_deref().map(parse_enum).transpose()?,
            accepted: r.accepted,
            score_milli: r.score_milli.map(|s| s as u64),
            change_class: r.change_class.as_deref().map(parse_enum).transpose()?,
            candidate_name: r.candidate_name,
            backend_family: r.backend_family,
            manifest: from_json_opt(r.manifest)?,
            build_outputs: from_json_opt(r.build_outputs)?,
            verified_surface: from_json_opt(r.verified_surface)?,
            formal_cache_key: r.formal_cache_key,
            benchmark: from_json_opt(r.benchmark)?,
            evidence_graph: from_json_opt(r.evidence_graph)?,
            coverage: from_json_opt(r.coverage)?,
            reason_codes: from_json(r.reason_codes)?,
            not_run_gates: from_json(r.not_run_gates)?,
            created_at: r.created_at,
            updated_at: r.updated_at,
            decided_at: r.decided_at,
        })
    }
}

pub async fn submission<'e>(
    ex: impl PgExecutor<'e>,
    id: &str,
) -> Result<Option<SubmissionRow>, DbError> {
    Ok(sqlx::query_as(&format!(
        "SELECT {SUB_COLS} FROM submissions s JOIN agents a ON a.id = s.agent_id WHERE s.id = $1"
    ))
    .bind(id)
    .fetch_optional(ex)
    .await?)
}

pub async fn run<'e>(ex: impl PgExecutor<'e>, id: &str) -> Result<Option<Run>, DbError> {
    let r: Option<RunRowRaw> =
        sqlx::query_as(&format!("SELECT {RUN_COLS} FROM runs WHERE id = $1"))
            .bind(id)
            .fetch_optional(ex)
            .await?;
    r.map(Run::try_from).transpose()
}

/// Lock a run row for the rest of the transaction (serializes pipeline transitions per run).
pub async fn run_for_update(
    conn: &mut sqlx::PgConnection,
    id: &str,
) -> Result<Option<Run>, DbError> {
    let r: Option<RunRowRaw> = sqlx::query_as(&format!(
        "SELECT {RUN_COLS} FROM runs WHERE id = $1 FOR UPDATE"
    ))
    .bind(id)
    .fetch_optional(&mut *conn)
    .await?;
    r.map(Run::try_from).transpose()
}

pub async fn runs_of<'e>(
    ex: impl PgExecutor<'e>,
    submission_ids: &[String],
) -> Result<Vec<Run>, DbError> {
    let rows: Vec<RunRowRaw> = sqlx::query_as(&format!(
        "SELECT {RUN_COLS} FROM runs WHERE submission_id = ANY($1) ORDER BY submission_id, run_number"
    ))
    .bind(submission_ids)
    .fetch_all(ex)
    .await?;
    rows.into_iter().map(Run::try_from).collect()
}

pub async fn gates_of<'e>(
    ex: impl PgExecutor<'e>,
    run_ids: &[String],
) -> Result<HashMap<String, Vec<GateResult>>, DbError> {
    let rows: Vec<(String, serde_json::Value)> = sqlx::query_as(
        "SELECT run_id, result FROM gate_results WHERE run_id = ANY($1) ORDER BY id",
    )
    .bind(run_ids)
    .fetch_all(ex)
    .await?;
    let mut out: HashMap<String, Vec<GateResult>> = HashMap::new();
    for (run, v) in rows {
        out.entry(run).or_default().push(from_json(v)?);
    }
    Ok(out)
}

pub async fn revocations_of<'e>(
    ex: impl PgExecutor<'e>,
    submission_ids: &[String],
) -> Result<HashMap<String, Revocation>, DbError> {
    let rows: Vec<(String, String, String, OffsetDateTime)> = sqlx::query_as(
        "SELECT submission_id, reason, revoked_by, revoked_at FROM revocations WHERE submission_id = ANY($1)",
    )
    .bind(submission_ids)
    .fetch_all(ex)
    .await?;
    Ok(rows
        .into_iter()
        .map(|(s, reason, by, at)| {
            (
                s,
                Revocation {
                    reason,
                    revoked_by: by,
                    revoked_at: rfc3339(at),
                },
            )
        })
        .collect())
}

/// Per-job information shown in submission views.
#[derive(Clone, Debug)]
pub struct JobSummary {
    pub kind: String,
    pub state: String,
    pub attempt: i32,
    pub last_error: Option<String>,
    pub artifacts: Vec<EvidenceRef>,
    pub log_excerpt: Option<String>,
    pub sandbox_backend: Option<String>,
}

pub async fn jobs_of<'e>(
    ex: impl PgExecutor<'e>,
    run_ids: &[String],
) -> Result<HashMap<String, Vec<JobSummary>>, DbError> {
    #[allow(clippy::type_complexity)]
    let rows: Vec<(
        String,
        String,
        String,
        i32,
        Option<String>,
        Option<serde_json::Value>,
        Option<serde_json::Value>,
    )> = sqlx::query_as(
        "SELECT run_id, kind, state, attempt, last_error, result, execution FROM jobs
             WHERE run_id = ANY($1) ORDER BY created_at, kind",
    )
    .bind(run_ids)
    .fetch_all(ex)
    .await?;
    let mut out: HashMap<String, Vec<JobSummary>> = HashMap::new();
    for (run, kind, state, attempt, last_error, result, execution) in rows {
        let artifacts = result
            .as_ref()
            .and_then(|r| r.get("artifacts").cloned())
            .and_then(|a| serde_json::from_value(a).ok())
            .unwrap_or_default();
        let log_excerpt = result
            .as_ref()
            .and_then(|r| r.get("log_excerpt"))
            .and_then(|l| l.as_str())
            .map(str::to_string);
        let sandbox_backend = execution
            .as_ref()
            .and_then(|e| e.get("sandbox_backend"))
            .and_then(|b| b.as_str())
            .map(str::to_string);
        out.entry(run).or_default().push(JobSummary {
            kind,
            state,
            attempt,
            last_error,
            artifacts,
            log_excerpt,
            sandbox_backend,
        });
    }
    Ok(out)
}

/// Remove evidence references that must not be shown publicly (e.g. held-out data).
pub fn public_gate(mut g: GateResult) -> GateResult {
    g.evidence.retain(|e| e.public);
    g
}

/// A submission together with all of its runs (oldest first).
#[derive(Clone, Debug)]
pub struct SubmissionBundle {
    pub sub: SubmissionRow,
    pub runs: Vec<Run>,
    pub gates: HashMap<String, Vec<GateResult>>,
    pub jobs: HashMap<String, Vec<JobSummary>>,
    pub revocation: Option<Revocation>,
}

const LOG_VIEW_BYTES: usize = 16 * 1024;

fn excerpt(name: String, stage: &str, text: &str) -> LogExcerpt {
    let truncated = text.len() > LOG_VIEW_BYTES;
    LogExcerpt {
        name,
        stage: stage.to_string(),
        text: arena_jobs::sanitize::sanitize_text(text, LOG_VIEW_BYTES),
        truncated,
    }
}

impl SubmissionBundle {
    pub fn latest_run(&self) -> Option<&Run> {
        self.runs.last()
    }
    pub fn latest_decided_run(&self) -> Option<&Run> {
        self.runs.iter().rev().find(|r| r.decision.is_some())
    }

    /// Public view of the latest run.
    pub fn view(&self, chal: &ChallengeDefinition) -> SubmissionView {
        let s = &self.sub;
        let run = self.latest_run();
        let gates: Vec<GateResult> = run
            .and_then(|r| self.gates.get(&r.id))
            .map(|g| g.iter().cloned().map(public_gate).collect())
            .unwrap_or_default();
        let jobs: &[JobSummary] = run
            .and_then(|r| self.jobs.get(&r.id))
            .map(|v| v.as_slice())
            .unwrap_or(&[]);
        let graph = run.and_then(|r| r.evidence_graph.clone());

        let mut artifacts: Vec<ArtifactRef> = Vec::new();
        for a in jobs
            .iter()
            .flat_map(|j| j.artifacts.iter())
            .filter(|a| a.public)
        {
            if !artifacts.iter().any(|x| x.digest == a.digest) {
                artifacts.push(ArtifactRef {
                    label: a.label.clone(),
                    digest: a.digest.clone(),
                });
            }
        }
        let mut logs = Vec::new();
        for j in jobs {
            if let Some(t) = &j.log_excerpt {
                logs.push(excerpt(j.kind.clone(), &j.kind, t));
            }
            if let Some(e) = &j.last_error {
                logs.push(excerpt(
                    format!("{}/error (attempt {})", j.kind, j.attempt),
                    &j.kind,
                    e,
                ));
            }
        }
        let build = run.and_then(|r| {
            let b = r.build_outputs.as_ref()?;
            Some(BuildInfo {
                toolchain_image: b.toolchain_image.clone(),
                reproducible: gates.iter().any(|g| {
                    g.gate == ObligationId::BuildReproducible && g.status == GateStatus::Pass
                }),
                build_ns: b.build_ns,
            })
        });
        let mut assumptions: Vec<AssumptionRef> = chal
            .security_profile
            .allowed_assumptions
            .iter()
            .map(|id| AssumptionRef {
                id: id.clone(),
                lean_decl: None,
                description: None,
            })
            .collect();
        if let Some(g) = &graph {
            for n in g.nodes.iter().filter(|n| n.kind == NodeKind::Assumption) {
                match assumptions.iter_mut().find(|a| a.id == n.id) {
                    Some(a) => a.description = Some(n.label.clone()),
                    None => assumptions.push(AssumptionRef {
                        id: n.id.clone(),
                        lean_decl: None,
                        description: Some(n.label.clone()),
                    }),
                }
            }
        }
        let tp = &chal.toolchain_policy;
        let mut trusted_base = vec![
            TrustedBaseEntry {
                id: "lean-toolchain".into(),
                label: format!("Lean kernel ({})", tp.lean_toolchain),
                digest: None,
            },
            TrustedBaseEntry {
                id: "checker-image".into(),
                label: "formal checker image".into(),
                digest: Some(tp.checker_image.clone()),
            },
        ];
        for r in &tp.recheckers {
            trusted_base.push(TrustedBaseEntry {
                id: format!("rechecker:{r}"),
                label: format!("rechecker {r}"),
                digest: None,
            });
        }
        let mut backends: Vec<&str> = jobs
            .iter()
            .filter_map(|j| j.sandbox_backend.as_deref())
            .collect();
        backends.sort();
        backends.dedup();
        for b in backends {
            trusted_base.push(TrustedBaseEntry {
                id: format!("sandbox:{b}"),
                label: format!("judge sandbox backend {b}"),
                digest: None,
            });
        }
        if let Some(g) = &graph {
            for n in g.nodes.iter().filter(|n| n.kind == NodeKind::TcbComponent) {
                trusted_base.push(TrustedBaseEntry {
                    id: n.id.clone(),
                    label: n.label.clone(),
                    digest: n.digest.clone(),
                });
            }
        }
        SubmissionView {
            coverage: run.and_then(|r| r.coverage.clone()),
            id: s.id.clone(),
            challenge_id: s.challenge_id.clone(),
            agent: s.agent_handle.clone(),
            candidate_name: run.map(|r| r.candidate_name.clone()).unwrap_or_default(),
            backend_family: run.map(|r| r.backend_family.clone()).unwrap_or_default(),
            parent: s.parent_id.clone(),
            tier: run.map(|r| r.tier).unwrap_or(chal.tier),
            package_digest: Digest::try_from(s.package_digest.clone())
                .expect("checked by DB constraint"),
            stage: run.map(|r| r.stage).unwrap_or(Stage::Received),
            decision: run.and_then(|r| r.decision),
            accepted: run.and_then(|r| r.accepted),
            score_milli: run.and_then(|r| r.score_milli),
            change_class: run.and_then(|r| r.change_class),
            gates,
            reason_codes: run.map(|r| r.reason_codes.clone()).unwrap_or_default(),
            benchmark: run.and_then(|r| r.benchmark.clone()),
            evidence_graph: graph,
            revoked: self.revocation.clone(),
            created_at: rfc3339(s.created_at),
            updated_at: rfc3339(run.map(|r| r.updated_at).unwrap_or(s.created_at)),
            artifacts,
            verified_surface: run.and_then(|r| r.verified_surface.clone()),
            build,
            assumptions,
            trusted_base,
            logs,
            revocation_history: self
                .revocation
                .iter()
                .map(|r| RevocationEvent {
                    action: "revoked".into(),
                    reason: r.reason.clone(),
                    at: r.revoked_at.clone(),
                    by: r.revoked_by.clone(),
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct SubmissionFilter {
    pub challenge_id: Option<String>,
    pub agent_handle: Option<String>,
    pub limit: i64,
    /// Only submissions created strictly before this one (keyset pagination).
    pub before_id: Option<String>,
}

async fn assemble(
    pool: &PgPool,
    subs: Vec<SubmissionRow>,
) -> Result<Vec<SubmissionBundle>, DbError> {
    let ids: Vec<String> = subs.iter().map(|s| s.id.clone()).collect();
    let runs = runs_of(pool, &ids).await?;
    let run_ids: Vec<String> = runs.iter().map(|r| r.id.clone()).collect();
    let mut gates = gates_of(pool, &run_ids).await?;
    let mut jobs = jobs_of(pool, &run_ids).await?;
    let mut revs = revocations_of(pool, &ids).await?;
    let mut by_sub: HashMap<String, Vec<Run>> = HashMap::new();
    for r in runs {
        by_sub.entry(r.submission_id.clone()).or_default().push(r);
    }
    Ok(subs
        .into_iter()
        .map(|sub| {
            let runs = by_sub.remove(&sub.id).unwrap_or_default();
            let g = runs
                .iter()
                .filter_map(|r| gates.remove_entry(&r.id))
                .collect();
            let j = runs
                .iter()
                .filter_map(|r| jobs.remove_entry(&r.id))
                .collect();
            let revocation = revs.remove(&sub.id);
            SubmissionBundle {
                sub,
                runs,
                gates: g,
                jobs: j,
                revocation,
            }
        })
        .collect())
}

pub async fn bundle(pool: &PgPool, id: &str) -> Result<Option<SubmissionBundle>, DbError> {
    let Some(s) = submission(pool, id).await? else {
        return Ok(None);
    };
    Ok(assemble(pool, vec![s]).await?.pop())
}

pub async fn list_bundles(
    pool: &PgPool,
    f: &SubmissionFilter,
) -> Result<Vec<SubmissionBundle>, DbError> {
    let subs: Vec<SubmissionRow> = sqlx::query_as(&format!(
        "SELECT {SUB_COLS} FROM submissions s JOIN agents a ON a.id = s.agent_id
         WHERE ($1::text IS NULL OR s.challenge_id = $1)
           AND ($2::text IS NULL OR a.handle = $2)
           AND ($3::text IS NULL OR (s.created_at, s.id) < (SELECT created_at, id FROM submissions WHERE id = $3))
         ORDER BY s.created_at DESC, s.id DESC LIMIT $4"
    ))
    .bind(&f.challenge_id)
    .bind(&f.agent_handle)
    .bind(&f.before_id)
    .bind(f.limit)
    .fetch_all(pool)
    .await?;
    assemble(pool, subs).await
}

// ------------------------------------------------------------------ leaderboard

#[derive(Clone, Debug, Serialize, schemars::JsonSchema)]
pub struct Leaderboard {
    pub challenge_id: String,
    /// Successor challenge, if this board is historical.
    pub superseded_by: Option<String>,
    pub challenge_tier: Tier,
    /// Only `formal` challenges have an official ranked board.
    pub official: bool,
    /// Ranked entries: tier=formal (challenge *and* effective), decision ADMITTED,
    /// accepted=true, not revoked, with a score; ordered by score desc.
    pub ranked: Vec<LeaderboardEntry>,
    /// Every submission with labels (rank set only for ranked entries).
    pub all_submissions: Vec<LeaderboardEntry>,
    /// `speed`, or `cost_v1` when the challenge pins a price model (then
    /// `cost_ranked` is the second board; docs/BENCHMARK_SPEC.md §14).
    pub scoring_kind: arena_types::ScoringKind,
    /// Cost board (cost_v1 challenges only): the same rankable runs, ordered
    /// by the server-recomputed cost score; `rank` is the cost rank and
    /// `board = cost_v1` on every entry. Never merged with the speed board.
    pub cost_ranked: Vec<LeaderboardEntry>,
}

impl Leaderboard {
    /// Flat list for `GET /v1/leaderboards/{id}`: ranked entries in rank order,
    /// then every other submission (rank `null`, newest first) with its labels.
    pub fn entries(&self) -> Vec<LeaderboardEntry> {
        let mut ranked: Vec<LeaderboardEntry> = self.ranked.clone();
        let mut rest: Vec<LeaderboardEntry> = self
            .all_submissions
            .iter()
            .filter(|e| e.rank.is_none())
            .cloned()
            .collect();
        rest.sort_by(|a, b| {
            b.submitted_at
                .cmp(&a.submitted_at)
                .then(b.submission_id.cmp(&a.submission_id))
        });
        ranked.extend(rest);
        ranked
    }

    /// Flat list of one board. `None` if the challenge has no such board.
    pub fn entries_for(&self, board: arena_types::ScoringKind) -> Option<Vec<LeaderboardEntry>> {
        use arena_types::ScoringKind::*;
        match (board, self.scoring_kind) {
            (Speed, _) => Some(self.entries()),
            (CostV1, CostV1) => {
                let mut v = self.cost_ranked.clone();
                let ranked: std::collections::HashSet<&str> =
                    v.iter().map(|e| e.submission_id.as_str()).collect();
                let mut rest: Vec<LeaderboardEntry> = self
                    .all_submissions
                    .iter()
                    .filter(|e| !ranked.contains(e.submission_id.as_str()))
                    .cloned()
                    .map(|mut e| {
                        e.rank = None;
                        e.board = Some(CostV1);
                        e
                    })
                    .collect();
                rest.sort_by(|a, b| {
                    b.submitted_at
                        .cmp(&a.submitted_at)
                        .then(b.submission_id.cmp(&a.submission_id))
                });
                v.extend(rest);
                Some(v)
            }
            (CostV1, Speed) => None,
        }
    }
}

/// Weighted geometric mean of a per-class quantity (weights in ppm).
fn weighted_geomean(vals: impl Iterator<Item = (u32, u64)>) -> Option<u64> {
    let mut acc = 0f64;
    let mut wsum = 0u64;
    for (w, v) in vals {
        if v == 0 {
            return None;
        }
        acc += (w as f64) * (v as f64).ln();
        wsum += w as u64;
    }
    if wsum == 0 {
        return None;
    }
    Some((acc / wsum as f64).exp().round() as u64)
}

/// Whether a run qualifies for the official ranked board.
pub fn rankable(challenge_tier: Tier, run: &Run, revoked: bool) -> bool {
    challenge_tier == Tier::Formal
        && run.challenge_tier == Tier::Formal
        && run.tier == Tier::Formal
        && run.decision == Some(Decision::Admitted)
        && run.accepted == Some(true)
        && run.score_milli.is_some()
        && !revoked
}

fn entry(
    b: &SubmissionBundle,
    run: Option<&Run>,
    chal: &arena_types::ChallengeDefinition,
    challenge_id: &str,
    superseded_by: Option<&str>,
) -> LeaderboardEntry {
    let bench = run.and_then(|r| r.benchmark.as_ref());
    // v1.7: the declared coverage tier (validated at VALIDATE).
    let tier = run
        .and_then(|r| r.manifest.as_ref())
        .and_then(|m| chal.declared_tier(m).ok().flatten());
    // A cost result only counts under the challenge's own price model.
    let cost = bench.and_then(|b| b.cost.clone()).filter(|c| {
        chal.scoring.as_ref().is_some_and(|s| {
            s.kind == arena_types::ScoringKind::CostV1
                && s.price_model_digest.as_ref() == Some(&c.price_model_digest)
        })
    });
    LeaderboardEntry {
        coverage_share_ppm: run
            .and_then(|r| r.coverage.as_ref())
            .map(|c| c.conformance.share_ppm),
        declared_tier: tier.map(|t| t.id.clone()),
        tier_rank: tier.map(|t| t.rank),
        rank: None,
        submission_id: b.sub.id.clone(),
        agent: b.sub.agent_handle.clone(),
        candidate_name: run.map(|r| r.candidate_name.clone()).unwrap_or_default(),
        backend_family: run.map(|r| r.backend_family.clone()).unwrap_or_default(),
        tier: run.map(|r| r.tier).unwrap_or(chal.tier),
        decision: run.and_then(|r| r.decision),
        accepted: run.and_then(|r| r.accepted),
        score_milli: run.and_then(|r| r.score_milli),
        prove_median_ns: bench.and_then(|b| {
            weighted_geomean(
                b.classes
                    .iter()
                    .filter(|c| !c.abstained)
                    .map(|c| (c.weight_ppm, c.median_ns)),
            )
        }),
        verify_median_ns: bench.and_then(|b| {
            weighted_geomean(
                b.classes
                    .iter()
                    .filter(|c| !c.abstained)
                    .map(|c| (c.weight_ppm, c.verify_median_ns)),
            )
        }),
        proof_bytes: bench.and_then(|b| b.classes.iter().map(|c| c.proof_bytes_max).max()),
        peak_rss_bytes: bench.and_then(|b| b.classes.iter().map(|c| c.peak_rss_bytes).max()),
        hardware_profile: bench
            .map(|b| b.hardware_profile.clone())
            .unwrap_or_else(|| chal.hardware_profile.id.clone()),
        scope: chal.semantic_scope.name.clone(),
        security_profile: chal.security_profile.id.clone(),
        submitted_at: rfc3339(b.sub.created_at),
        revoked: b.revocation.is_some(),
        score_ci_milli: bench.and_then(|b| b.score_ci_milli),
        challenge_id: challenge_id.to_string(),
        protocol_version: chal.protocol_version,
        superseded_by: superseded_by.map(str::to_string),
        board: None,
        cost_score_milli: cost.as_ref().and_then(|c| c.score_milli),
        cost_score_ci_milli: cost.as_ref().and_then(|c| c.score_ci_milli),
        cost,
    }
}

/// Compute the leaderboard from submission bundles of one challenge.
/// The ranked board uses each submission's latest *decided* run, so a rerun in
/// progress does not hide an existing result. Only bundles of `challenge_id`
/// are ever considered: boards of a superseded challenge and its successor
/// are never merged (docs/PROTOCOL_UPGRADES.md §5). A superseded board keeps
/// its ranking and carries `superseded_by` on every entry.
pub fn compute_leaderboard(
    challenge_id: &str,
    chal: &arena_types::ChallengeDefinition,
    superseded_by: Option<&str>,
    bundles: &[SubmissionBundle],
) -> Leaderboard {
    // A run whose formal gates were reused from a revoked submission carries
    // that submission's (now withdrawn) evidence: it is not rankable either.
    let revoked: std::collections::HashSet<&str> = bundles
        .iter()
        .filter(|b| b.revocation.is_some())
        .map(|b| b.sub.id.as_str())
        .collect();
    let bundles: Vec<&SubmissionBundle> = bundles
        .iter()
        .filter(|b| b.sub.challenge_id == challenge_id)
        .collect();
    let mut ranked: Vec<(LeaderboardEntry, OffsetDateTime)> = bundles
        .iter()
        .filter_map(|b| {
            let r = b.latest_decided_run()?;
            let tainted = b.gates.get(&r.id).is_some_and(|gs| {
                gs.iter().any(|g| {
                    g.reused_from
                        .as_deref()
                        .is_some_and(|s| revoked.contains(s))
                })
            });
            rankable(chal.tier, r, b.revocation.is_some() || tainted).then(|| {
                (
                    entry(b, Some(r), chal, challenge_id, superseded_by),
                    b.sub.created_at,
                )
            })
        })
        .collect();
    // v1.7: coverage-tiered challenges order by declared tier rank first
    // (CONTRACTS §11); `tier_rank` is `None` on every other challenge.
    ranked.sort_by(|(a, at), (b, bt)| {
        b.tier_rank
            .cmp(&a.tier_rank)
            .then(b.score_milli.cmp(&a.score_milli))
            .then(at.cmp(bt))
            .then(a.submission_id.cmp(&b.submission_id))
    });
    let scoring_kind = chal.scoring_kind();
    let mut cost_ranked: Vec<(LeaderboardEntry, OffsetDateTime)> =
        if scoring_kind == arena_types::ScoringKind::CostV1 {
            ranked
                .iter()
                .filter(|(e, _)| e.cost_score_milli.is_some())
                .cloned()
                .collect()
        } else {
            vec![]
        };
    cost_ranked.sort_by(|(a, at), (b, bt)| {
        b.tier_rank
            .cmp(&a.tier_rank)
            .then(b.cost_score_milli.cmp(&a.cost_score_milli))
            .then(at.cmp(bt))
            .then(a.submission_id.cmp(&b.submission_id))
    });
    let cost_ranked: Vec<LeaderboardEntry> = cost_ranked
        .into_iter()
        .enumerate()
        .map(|(i, (mut e, _))| {
            e.rank = Some(i as u32 + 1);
            e.board = Some(arena_types::ScoringKind::CostV1);
            e
        })
        .collect();
    let ranked: Vec<LeaderboardEntry> = ranked
        .into_iter()
        .enumerate()
        .map(|(i, (mut e, _))| {
            e.rank = Some(i as u32 + 1);
            e
        })
        .collect();
    let rank_of: HashMap<&str, u32> = ranked
        .iter()
        .map(|e| (e.submission_id.as_str(), e.rank.unwrap()))
        .collect();
    let all_submissions = bundles
        .iter()
        .map(|b| {
            let mut e = entry(
                b,
                b.latest_decided_run().or(b.latest_run()),
                chal,
                challenge_id,
                superseded_by,
            );
            e.rank = rank_of.get(b.sub.id.as_str()).copied();
            e
        })
        .collect();
    Leaderboard {
        challenge_id: challenge_id.to_string(),
        superseded_by: superseded_by.map(str::to_string),
        challenge_tier: chal.tier,
        official: chal.tier == Tier::Formal,
        ranked,
        all_submissions,
        scoring_kind,
        cost_ranked,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use arena_types::scoring::{CostBaselineClass, PriceModel, ScoringKind, ScoringSpec};

    fn chal(cost: bool) -> ChallengeDefinition {
        let mut c: ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../challenges/chl_7c0456cb2d1a36f8601863ac206cfcc9.json"
        ))
        .unwrap();
        if cost {
            let mut pm: PriceModel = serde_json::from_str(include_str!(
                "../../../challenges/price-models/pm-near-mainnet-2026q4.draft.json"
            ))
            .unwrap();
            pm.status = "governed".into();
            c.scoring = Some(ScoringSpec {
                kind: ScoringKind::CostV1,
                price_model_digest: Some(pm.digest().unwrap()),
                price_model: Some(pm),
                cost_baseline: c
                    .workload_suite
                    .baseline_ns
                    .iter()
                    .map(|(id, ns)| CostBaselineClass {
                        class_id: id.clone(),
                        prove_ns: *ns,
                        verify_ns: 1,
                        proof_bytes: 1,
                    })
                    .collect(),
                cost_baseline_prepare_ns: None,
                verify_statistic: None,
            });
            c.check_scoring().unwrap();
        }
        c
    }

    fn bundle(id: &str, at: i64, speed: u64, cost: Option<(u64, Digest)>) -> SubmissionBundle {
        let t = OffsetDateTime::from_unix_timestamp(at).unwrap();
        let bench = BenchmarkResult {
            hardware_profile: "hw".into(),
            suite_revision: "r".into(),
            classes: vec![],
            score_milli: Some(speed),
            score_ci_milli: Some(1),
            prepare_ns: 0,
            public_artifact_bytes: 0,
            measured_by: "t".into(),
            cost: cost.map(|(s, d)| arena_types::CostResult {
                kind: ScoringKind::CostV1,
                price_model_id: "pm".into(),
                price_model_digest: d,
                validators_per_chunk: 84,
                verifier_vcpus: 8,
                score_milli: Some(s),
                score_ci_milli: Some(2),
                classes: vec![],
            }),
        };
        SubmissionBundle {
            sub: SubmissionRow {
                id: id.into(),
                agent_id: "a".into(),
                agent_handle: "a".into(),
                challenge_id: "chl_x".into(),
                package_digest: String::new(),
                upload_id: String::new(),
                parent_id: None,
                idempotency_key: String::new(),
                request_digest: String::new(),
                created_at: t,
            },
            runs: vec![Run {
                coverage: None,
                id: format!("run_{id}"),
                submission_id: id.into(),
                run_number: 1,
                trigger: "submit".into(),
                requested_by: "a".into(),
                challenge_tier: Tier::Formal,
                tier: Tier::Formal,
                stage: Stage::Decided,
                decision: Some(Decision::Admitted),
                accepted: Some(true),
                score_milli: Some(speed),
                change_class: None,
                candidate_name: id.into(),
                backend_family: "f".into(),
                manifest: None,
                build_outputs: None,
                verified_surface: None,
                formal_cache_key: None,
                benchmark: Some(bench),
                evidence_graph: None,
                reason_codes: vec![],
                not_run_gates: vec![],
                created_at: t,
                updated_at: t,
                decided_at: Some(t),
            }],
            gates: HashMap::new(),
            jobs: HashMap::new(),
            revocation: None,
        }
    }

    #[test]
    fn speed_and_cost_boards_are_separate() {
        let c = chal(true);
        let d = c
            .scoring
            .as_ref()
            .unwrap()
            .price_model_digest
            .clone()
            .unwrap();
        let other = Digest::of_bytes(b"another price model");
        let bundles = vec![
            bundle("sub_fast", 1, 110_000, Some((90_000, d.clone()))),
            bundle("sub_lean", 2, 97_000, Some((207_000, d.clone()))),
            bundle("sub_stark", 3, 52, Some((1_500, d))),
            // a cost result under a different price model is never ranked
            bundle("sub_alien", 4, 100_000, Some((999_000, other))),
        ];
        let lb = compute_leaderboard("chl_x", &c, None, &bundles);
        let speed: Vec<_> = lb.ranked.iter().map(|e| e.submission_id.as_str()).collect();
        assert_eq!(speed, ["sub_fast", "sub_alien", "sub_lean", "sub_stark"]);
        let cost: Vec<_> = lb
            .cost_ranked
            .iter()
            .map(|e| e.submission_id.as_str())
            .collect();
        assert_eq!(cost, ["sub_lean", "sub_fast", "sub_stark"]);
        assert!(lb
            .cost_ranked
            .iter()
            .all(|e| e.board == Some(ScoringKind::CostV1)));
        let flat = lb.entries_for(ScoringKind::CostV1).unwrap();
        assert_eq!(flat.len(), 4);
        let alien = flat
            .iter()
            .find(|e| e.submission_id == "sub_alien")
            .unwrap();
        assert_eq!((alien.rank, alien.cost_score_milli), (None, None));
        // the speed board keeps speed scores and ranks
        assert_eq!(lb.entries_for(ScoringKind::Speed).unwrap()[0].rank, Some(1));
    }

    /// v1.7 (CONTRACTS §11): ranked by declared tier rank first, then score;
    /// the board shows tier, rank and the coverage share.
    #[test]
    fn coverage_tiers_rank_first() {
        let mut c = chal(true);
        let d = c
            .scoring
            .as_ref()
            .unwrap()
            .price_model_digest
            .clone()
            .unwrap();
        let class0 = c.workload_suite.classes[0].id.clone();
        c.coverage = Some(arena_types::CoverageSpec {
            version: "coverage-v1".into(),
            statement_spec: "S".into(),
            soundness_lift: "L".into(),
            tiers: vec![
                arena_types::CoverageTier {
                    id: "D0".into(),
                    rank: 0,
                    params: "P0".into(),
                    classes: vec![],
                },
                arena_types::CoverageTier {
                    id: "D3a".into(),
                    rank: 3,
                    params: "P3".into(),
                    classes: vec![class0],
                },
            ],
        });
        c.check_coverage().unwrap();
        let manifest = CandidateManifest::parse(include_str!(
            "../../../examples/reexec-v3-d0/candidate.toml"
        ))
        .unwrap();
        let with = |id: &str, at: i64, speed: u64, cost: u64, tier: &str, share: u32| {
            let mut b = bundle(id, at, speed, Some((cost, d.clone())));
            let mut m = manifest.clone();
            m.entry.declared_tier = Some(tier.into());
            b.runs[0].manifest = Some(m);
            let mut cov = arena_types::CoverageReport {
                tier: tier.into(),
                conformance: Default::default(),
                heldout: None,
            };
            cov.conformance.share_ppm = share;
            b.runs[0].coverage = Some(cov);
            b
        };
        let bundles = vec![
            with("sub_zk_d0", 1, 900_000, 900_000, "D0", 400_000),
            with("sub_reexec_d3", 2, 100_000, 100_000, "D3a", 1_000_000),
            with("sub_slow_d3", 3, 50_000, 60_000, "D3a", 1_000_000),
        ];
        let lb = compute_leaderboard("chl_x", &c, None, &bundles);
        let order = |v: &[LeaderboardEntry]| {
            v.iter()
                .map(|e| e.submission_id.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            order(&lb.ranked),
            ["sub_reexec_d3", "sub_slow_d3", "sub_zk_d0"]
        );
        assert_eq!(
            order(&lb.cost_ranked),
            ["sub_reexec_d3", "sub_slow_d3", "sub_zk_d0"]
        );
        let zk = &lb.ranked[2];
        assert_eq!(
            (
                zk.declared_tier.as_deref(),
                zk.tier_rank,
                zk.coverage_share_ppm
            ),
            (Some("D0"), Some(0), Some(400_000))
        );
        // untiered challenges: no tier fields, plain score order
        let lb = compute_leaderboard("chl_x", &chal(true), None, &bundles);
        assert_eq!(
            order(&lb.ranked),
            ["sub_zk_d0", "sub_reexec_d3", "sub_slow_d3"]
        );
        assert!(lb
            .ranked
            .iter()
            .all(|e| e.tier_rank.is_none() && e.declared_tier.is_none()));
    }

    #[test]
    fn speed_challenge_has_no_cost_board() {
        let c = chal(false);
        let d = Digest::of_bytes(b"x");
        let lb = compute_leaderboard("chl_x", &c, None, &[bundle("sub_a", 1, 1, Some((5, d)))]);
        assert!(lb.cost_ranked.is_empty());
        assert!(lb.entries_for(ScoringKind::CostV1).is_none());
        assert_eq!(lb.ranked[0].cost_score_milli, None);
        assert!(lb.ranked[0].cost.is_none());
    }

    #[test]
    fn geomean() {
        assert_eq!(
            weighted_geomean([(500_000, 100), (500_000, 400)].into_iter()),
            Some(200)
        );
        assert_eq!(weighted_geomean([(1, 0)].into_iter()), None);
        assert_eq!(weighted_geomean(std::iter::empty()), None);
    }
}

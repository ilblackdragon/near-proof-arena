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
    pub reason_codes: serde_json::Value,
    pub not_run_gates: serde_json::Value,
    pub created_at: OffsetDateTime,
    pub updated_at: OffsetDateTime,
    pub decided_at: Option<OffsetDateTime>,
}

pub const RUN_COLS: &str = "id, submission_id, run_number, trigger, requested_by, challenge_tier, tier, \
    stage, decision, accepted, score_milli, change_class, candidate_name, backend_family, manifest, \
    build_outputs, verified_surface, formal_cache_key, benchmark, evidence_graph, reason_codes, \
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
    pub challenge_tier: Tier,
    /// Only `formal` challenges have an official ranked board.
    pub official: bool,
    /// Ranked entries: tier=formal (challenge *and* effective), decision ADMITTED,
    /// accepted=true, not revoked, with a score; ordered by score desc.
    pub ranked: Vec<LeaderboardEntry>,
    /// Every submission with labels (rank set only for ranked entries).
    pub all_submissions: Vec<LeaderboardEntry>,
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
) -> LeaderboardEntry {
    let bench = run.and_then(|r| r.benchmark.as_ref());
    LeaderboardEntry {
        rank: None,
        submission_id: b.sub.id.clone(),
        agent: b.sub.agent_handle.clone(),
        candidate_name: run.map(|r| r.candidate_name.clone()).unwrap_or_default(),
        backend_family: run.map(|r| r.backend_family.clone()).unwrap_or_default(),
        tier: run.map(|r| r.tier).unwrap_or(chal.tier),
        decision: run.and_then(|r| r.decision),
        accepted: run.and_then(|r| r.accepted),
        score_milli: run.and_then(|r| r.score_milli),
        prove_median_ns: bench
            .and_then(|b| weighted_geomean(b.classes.iter().map(|c| (c.weight_ppm, c.median_ns)))),
        verify_median_ns: bench.and_then(|b| {
            weighted_geomean(b.classes.iter().map(|c| (c.weight_ppm, c.verify_median_ns)))
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
    }
}

/// Compute the leaderboard from submission bundles of one challenge.
/// The ranked board uses each submission's latest *decided* run, so a rerun in
/// progress does not hide an existing result.
pub fn compute_leaderboard(
    challenge_id: &str,
    chal: &arena_types::ChallengeDefinition,
    bundles: &[SubmissionBundle],
) -> Leaderboard {
    // A run whose formal gates were reused from a revoked submission carries
    // that submission's (now withdrawn) evidence: it is not rankable either.
    let revoked: std::collections::HashSet<&str> = bundles
        .iter()
        .filter(|b| b.revocation.is_some())
        .map(|b| b.sub.id.as_str())
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
            rankable(chal.tier, r, b.revocation.is_some() || tainted)
                .then(|| (entry(b, Some(r), chal), b.sub.created_at))
        })
        .collect();
    ranked.sort_by(|(a, at), (b, bt)| {
        b.score_milli
            .cmp(&a.score_milli)
            .then(at.cmp(bt))
            .then(a.submission_id.cmp(&b.submission_id))
    });
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
            let mut e = entry(b, b.latest_decided_run().or(b.latest_run()), chal);
            e.rank = rank_of.get(b.sub.id.as_str()).copied();
            e
        })
        .collect();
    Leaderboard {
        challenge_id: challenge_id.to_string(),
        challenge_tier: chal.tier,
        official: chal.tier == Tier::Formal,
        ranked,
        all_submissions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

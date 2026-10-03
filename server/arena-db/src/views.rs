//! Read models: submission views and leaderboards.

use crate::{from_json, from_json_opt, parse_enum, rfc3339, DbError};
use arena_jobs::BuildOutputs;
use arena_types::{
    challenge::Tier, BenchmarkResult, CandidateManifest, ChangeClass, Decision, Digest,
    EvidenceGraph, GateResult, LeaderboardEntry, ObligationId, ReasonCode, Revocation, Stage,
    SubmissionView, VerifiedSurface,
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

const SUB_COLS: &str = "s.id, s.agent_id, a.handle AS agent_handle, s.challenge_id, s.package_digest, \
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

pub async fn submission<'e>(ex: impl PgExecutor<'e>, id: &str) -> Result<Option<SubmissionRow>, DbError> {
    Ok(sqlx::query_as(&format!(
        "SELECT {SUB_COLS} FROM submissions s JOIN agents a ON a.id = s.agent_id WHERE s.id = $1"
    ))
    .bind(id)
    .fetch_optional(ex)
    .await?)
}

pub async fn run<'e>(ex: impl PgExecutor<'e>, id: &str) -> Result<Option<Run>, DbError> {
    let r: Option<RunRowRaw> = sqlx::query_as(&format!("SELECT {RUN_COLS} FROM runs WHERE id = $1"))
        .bind(id)
        .fetch_optional(ex)
        .await?;
    r.map(Run::try_from).transpose()
}

/// Lock a run row for the rest of the transaction (serializes pipeline transitions per run).
pub async fn run_for_update(conn: &mut sqlx::PgConnection, id: &str) -> Result<Option<Run>, DbError> {
    let r: Option<RunRowRaw> =
        sqlx::query_as(&format!("SELECT {RUN_COLS} FROM runs WHERE id = $1 FOR UPDATE"))
            .bind(id)
            .fetch_optional(&mut *conn)
            .await?;
    r.map(Run::try_from).transpose()
}

pub async fn runs_of<'e>(ex: impl PgExecutor<'e>, submission_ids: &[String]) -> Result<Vec<Run>, DbError> {
    let rows: Vec<RunRowRaw> = sqlx::query_as(&format!(
        "SELECT {RUN_COLS} FROM runs WHERE submission_id = ANY($1) ORDER BY submission_id, run_number"
    ))
    .bind(submission_ids)
    .fetch_all(ex)
    .await?;
    rows.into_iter().map(Run::try_from).collect()
}

pub async fn gates_of<'e>(ex: impl PgExecutor<'e>, run_ids: &[String]) -> Result<HashMap<String, Vec<GateResult>>, DbError> {
    let rows: Vec<(String, serde_json::Value)> =
        sqlx::query_as("SELECT run_id, result FROM gate_results WHERE run_id = ANY($1) ORDER BY id")
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
        .map(|(s, reason, by, at)| (s, Revocation { reason, revoked_by: by, revoked_at: rfc3339(at) }))
        .collect())
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
    pub revocation: Option<Revocation>,
}

impl SubmissionBundle {
    pub fn latest_run(&self) -> Option<&Run> {
        self.runs.last()
    }
    pub fn latest_decided_run(&self) -> Option<&Run> {
        self.runs.iter().rev().find(|r| r.decision.is_some())
    }

    /// Public view of the latest run.
    pub fn view(&self, challenge_tier: Tier) -> SubmissionView {
        let s = &self.sub;
        let run = self.latest_run();
        let gates = run
            .and_then(|r| self.gates.get(&r.id))
            .map(|g| g.iter().cloned().map(public_gate).collect())
            .unwrap_or_default();
        SubmissionView {
            id: s.id.clone(),
            challenge_id: s.challenge_id.clone(),
            agent: s.agent_handle.clone(),
            candidate_name: run.map(|r| r.candidate_name.clone()).unwrap_or_default(),
            backend_family: run.map(|r| r.backend_family.clone()).unwrap_or_default(),
            parent: s.parent_id.clone(),
            tier: run.map(|r| r.tier).unwrap_or(challenge_tier),
            package_digest: Digest::try_from(s.package_digest.clone()).expect("checked by DB constraint"),
            stage: run.map(|r| r.stage).unwrap_or(Stage::Received),
            decision: run.and_then(|r| r.decision),
            accepted: run.and_then(|r| r.accepted),
            score_milli: run.and_then(|r| r.score_milli),
            change_class: run.and_then(|r| r.change_class),
            gates,
            reason_codes: run.map(|r| r.reason_codes.clone()).unwrap_or_default(),
            benchmark: run.and_then(|r| r.benchmark.clone()),
            evidence_graph: run.and_then(|r| r.evidence_graph.clone()),
            revoked: self.revocation.clone(),
            created_at: rfc3339(s.created_at),
            updated_at: rfc3339(run.map(|r| r.updated_at).unwrap_or(s.created_at)),
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

async fn assemble(pool: &PgPool, subs: Vec<SubmissionRow>) -> Result<Vec<SubmissionBundle>, DbError> {
    let ids: Vec<String> = subs.iter().map(|s| s.id.clone()).collect();
    let runs = runs_of(pool, &ids).await?;
    let run_ids: Vec<String> = runs.iter().map(|r| r.id.clone()).collect();
    let mut gates = gates_of(pool, &run_ids).await?;
    let mut revs = revocations_of(pool, &ids).await?;
    let mut by_sub: HashMap<String, Vec<Run>> = HashMap::new();
    for r in runs {
        by_sub.entry(r.submission_id.clone()).or_default().push(r);
    }
    Ok(subs
        .into_iter()
        .map(|sub| {
            let runs = by_sub.remove(&sub.id).unwrap_or_default();
            let g = runs.iter().filter_map(|r| gates.remove_entry(&r.id)).collect();
            let revocation = revs.remove(&sub.id);
            SubmissionBundle { sub, runs, gates: g, revocation }
        })
        .collect())
}

pub async fn bundle(pool: &PgPool, id: &str) -> Result<Option<SubmissionBundle>, DbError> {
    let Some(s) = submission(pool, id).await? else { return Ok(None) };
    Ok(assemble(pool, vec![s]).await?.pop())
}

pub async fn list_bundles(pool: &PgPool, f: &SubmissionFilter) -> Result<Vec<SubmissionBundle>, DbError> {
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

#[derive(Clone, Debug, Serialize)]
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

fn entry(b: &SubmissionBundle, run: Option<&Run>, chal: &arena_types::ChallengeDefinition) -> LeaderboardEntry {
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
        prove_median_ns: bench.and_then(|b| weighted_geomean(b.classes.iter().map(|c| (c.weight_ppm, c.median_ns)))),
        verify_median_ns: bench
            .and_then(|b| weighted_geomean(b.classes.iter().map(|c| (c.weight_ppm, c.verify_median_ns)))),
        proof_bytes: bench.and_then(|b| b.classes.iter().map(|c| c.proof_bytes_max).max()),
        peak_rss_bytes: bench.and_then(|b| b.classes.iter().map(|c| c.peak_rss_bytes).max()),
        hardware_profile: bench
            .map(|b| b.hardware_profile.clone())
            .unwrap_or_else(|| chal.hardware_profile.id.clone()),
        scope: chal.semantic_scope.name.clone(),
        security_profile: chal.security_profile.id.clone(),
        submitted_at: rfc3339(b.sub.created_at),
        revoked: b.revocation.is_some(),
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
    let mut ranked: Vec<(LeaderboardEntry, OffsetDateTime)> = bundles
        .iter()
        .filter_map(|b| {
            let r = b.latest_decided_run()?;
            rankable(chal.tier, r, b.revocation.is_some()).then(|| (entry(b, Some(r), chal), b.sub.created_at))
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
    let rank_of: HashMap<&str, u32> =
        ranked.iter().map(|e| (e.submission_id.as_str(), e.rank.unwrap())).collect();
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
        assert_eq!(weighted_geomean([(500_000, 100), (500_000, 400)].into_iter()), Some(200));
        assert_eq!(weighted_geomean([(1, 0)].into_iter()), None);
        assert_eq!(weighted_geomean(std::iter::empty()), None);
    }
}

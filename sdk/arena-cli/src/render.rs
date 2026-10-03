//! Human-readable rendering of API objects. `--json` bypasses all of this.

use arena_types::{GateStatus, LeaderboardEntry, SubmissionView};
use serde_json::Value;

fn s<T: serde::Serialize>(x: &T) -> String {
    match serde_json::to_value(x) {
        Ok(Value::String(s)) => s,
        Ok(Value::Null) => "-".into(),
        Ok(v) => v.to_string(),
        Err(_) => "?".into(),
    }
}

pub fn score(milli: Option<u64>) -> String {
    milli
        .map(|m| format!("{}.{:03}", m / 1000, m % 1000))
        .unwrap_or_else(|| "-".into())
}

fn ns_ms(ns: Option<u64>) -> String {
    ns.map(|n| format!("{:.3}", n as f64 / 1e6))
        .unwrap_or_else(|| "-".into())
}

pub fn progress_line(v: &Value) -> String {
    let get = |k: &str| {
        v.get(k)
            .map(|x| {
                x.as_str()
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| x.to_string())
            })
            .unwrap_or_else(|| "-".into())
    };
    let gates = v
        .get("gates")
        .and_then(|g| g.as_array())
        .map(|g| g.len())
        .unwrap_or(0);
    format!(
        "{} stage={} decision={} gates={}",
        get("id"),
        get("stage"),
        get("decision"),
        gates
    )
}

pub fn submission(v: &Value) -> String {
    let Ok(sv) = serde_json::from_value::<SubmissionView>(v.clone()) else {
        return format!("{}\n", serde_json::to_string_pretty(v).unwrap_or_default());
    };
    let mut o = String::new();
    o.push_str(&format!("submission  {}\n", sv.id));
    o.push_str(&format!("challenge   {}\n", sv.challenge_id));
    o.push_str(&format!(
        "candidate   {} ({}) by {}\n",
        sv.candidate_name, sv.backend_family, sv.agent
    ));
    o.push_str(&format!(
        "tier        {}{}\n",
        s(&sv.tier),
        if sv.tier != arena_types::challenge::Tier::Formal {
            "  (NOT an official formal result)"
        } else {
            ""
        }
    ));
    if let Some(p) = &sv.parent {
        o.push_str(&format!(
            "parent      {p}  change_class={}\n",
            s(&sv.change_class)
        ));
    }
    o.push_str(&format!("package     {}\n", sv.package_digest));
    o.push_str(&format!("stage       {}\n", s(&sv.stage)));
    o.push_str(&format!(
        "decision    {}  accepted={}\n",
        s(&sv.decision),
        s(&sv.accepted)
    ));
    o.push_str(&format!("score       {}\n", score(sv.score_milli)));
    if !sv.reason_codes.is_empty() {
        o.push_str(&format!(
            "reasons     {}\n",
            sv.reason_codes.iter().map(s).collect::<Vec<_>>().join(", ")
        ));
    }
    if let Some(r) = &sv.revoked {
        o.push_str(&format!(
            "REVOKED     {} ({} by {})\n",
            r.reason, r.revoked_at, r.revoked_by
        ));
    }
    if !sv.gates.is_empty() {
        o.push_str("gates:\n");
        for g in &sv.gates {
            let mark = match g.status {
                GateStatus::Pass => "PASS",
                GateStatus::Fail => "FAIL",
                GateStatus::Unknown => "UNKNOWN",
                GateStatus::NotApplicable => "N/A",
            };
            o.push_str(&format!(
                "  [{mark:<7}] {:<28}{}{}{}\n",
                s(&g.gate),
                if g.mandatory { "" } else { " (optional)" },
                if g.reason_codes.is_empty() {
                    String::new()
                } else {
                    format!(
                        " {}",
                        g.reason_codes.iter().map(s).collect::<Vec<_>>().join(",")
                    )
                },
                g.reused_from
                    .as_ref()
                    .map(|r| format!(" reused from {r}"))
                    .unwrap_or_default()
            ));
            for line in g.summary.lines().take(8) {
                o.push_str(&format!("             {line}\n"));
            }
        }
    }
    if let Some(b) = &sv.benchmark {
        o.push_str(&format!(
            "benchmark ({} / suite {}):\n",
            b.hardware_profile, b.suite_revision
        ));
        for c in &b.classes {
            o.push_str(&format!(
                "  {:<24} w={:>7}ppm prove_med={}ms (base {}ms) verify_med={}ms proof<={}B rss={}B\n",
                c.class_id,
                c.weight_ppm,
                ns_ms(Some(c.median_ns)),
                ns_ms(Some(c.baseline_ns)),
                ns_ms(Some(c.verify_median_ns)),
                c.proof_bytes_max,
                c.peak_rss_bytes
            ));
        }
        if let Some(ci) = b.score_ci_milli {
            o.push_str(&format!(
                "  score {} ± {}\n",
                score(b.score_milli),
                score(Some(ci))
            ));
        }
    }
    if let Some(eg) = &sv.evidence_graph {
        let missing: Vec<_> = eg.missing_edges().collect();
        if !missing.is_empty() {
            o.push_str("missing evidence edges:\n");
            for e in missing {
                o.push_str(&format!(
                    "  {} -> {} ({}) {}\n",
                    e.from, e.to, e.kind, e.note
                ));
            }
        }
    }
    o
}

pub fn leaderboard(challenge: &str, entries: &[Value]) -> String {
    let mut o = format!("leaderboard {challenge}\n");
    let parsed: Vec<LeaderboardEntry> = entries
        .iter()
        .filter_map(|e| serde_json::from_value(e.clone()).ok())
        .collect();
    if parsed.len() != entries.len() {
        o.push_str("(some entries could not be parsed; use --json)\n");
    }
    o.push_str(&format!(
        "{:>4} {:>10} {:<24} {:<20} {:<16} {:<12} {:>10} {:>10} {:>10} {}\n",
        "rank",
        "score",
        "submission",
        "candidate",
        "backend",
        "tier",
        "prove_ms",
        "verify_ms",
        "proof_B",
        "agent"
    ));
    for e in &parsed {
        o.push_str(&format!(
            "{:>4} {:>10} {:<24} {:<20} {:<16} {:<12} {:>10} {:>10} {:>10} {}{}\n",
            e.rank.map(|r| r.to_string()).unwrap_or_else(|| "-".into()),
            score(e.score_milli),
            e.submission_id,
            e.candidate_name,
            e.backend_family,
            s(&e.tier),
            ns_ms(e.prove_median_ns),
            ns_ms(e.verify_median_ns),
            e.proof_bytes
                .map(|b| b.to_string())
                .unwrap_or_else(|| "-".into()),
            e.agent,
            if e.revoked { "  REVOKED" } else { "" }
        ));
    }
    o
}

pub fn challenges(items: &[Value]) -> String {
    let mut o = String::new();
    for it in items {
        let def = it.get("definition").unwrap_or(it);
        let id = it
            .get("id")
            .and_then(|x| x.as_str())
            .map(|s| s.to_string())
            .or_else(|| {
                serde_json::from_value::<arena_types::ChallengeDefinition>(def.clone())
                    .ok()
                    .and_then(|d| d.id().ok())
            })
            .unwrap_or_else(|| "?".into());
        let f = |k: &str| {
            def.get(k)
                .and_then(|x| x.as_str())
                .unwrap_or("-")
                .to_string()
        };
        o.push_str(&format!(
            "{id}  {}  tier={}  season={}\n",
            f("name"),
            f("tier"),
            f("season")
        ));
    }
    if items.is_empty() {
        o.push_str("(no challenges)\n");
    }
    o
}

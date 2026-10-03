//! Writes JSON Schemas for the frozen contracts to `common/schemas/`.
use arena_types::*;
use std::path::Path;

fn write<T: schemars::JsonSchema>(dir: &Path, name: &str) {
    let schema = schemars::schema_for!(T);
    let path = dir.join(format!("{name}.schema.json"));
    std::fs::write(&path, serde_json::to_string_pretty(&schema).unwrap() + "\n").unwrap();
    println!("wrote {}", path.display());
}

fn main() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../schemas");
    std::fs::create_dir_all(&dir).unwrap();
    write::<ChallengeDefinition>(&dir, "challenge");
    write::<CandidateManifest>(&dir, "candidate");
    write::<SecurityProfile>(&dir, "security-profile");
    write::<security::Assumption>(&dir, "assumption");
    write::<SubmissionView>(&dir, "submission");
    write::<LeaderboardEntry>(&dir, "leaderboard-entry");
    write::<EvidenceGraph>(&dir, "evidence-graph");
    write::<GateResult>(&dir, "gate-result");
    write::<VerifiedSurface>(&dir, "verified-surface");
}

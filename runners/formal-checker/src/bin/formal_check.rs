//! `formal-check` — run the formal checker on one candidate `formal/` tree.
//!
//! ```text
//! ARENA_DEV_UNSAFE=1 formal-check --formal path/to/formal --certificate Candidate.certificate \
//!     --trusted NAME=DIR[@Mod.Prefix,...] [--trusted ...] --expected expected.json [--policy policy.json] \
//!     [--native-model Candidate.Model.verify@Candidate.Model] [--candidate-native-binary FILE]
//!     [--work DIR] [--cache DIR] [--out report.json]
//! ```
//! `expected.json` is a `TemplateExpected` (`module`, `decl`, `template`, `data`).
use arena_formal_checker::*;
use std::path::PathBuf;

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().skip(1);
    let (mut formal, mut cert, mut expected, mut policy, mut out) = (None, None, None, None, None);
    let mut trusted = Vec::new();
    let mut route = native::VerifierRoute::Standard;
    let mut cand_bin: Option<arena_types::Digest> = None;
    let mut work = std::env::temp_dir().join(format!("formal-check-{}", std::process::id()));
    let mut cache = toolchain::fc_home().join("ref-cache");
    while let Some(a) = args.next() {
        let mut v = || args.next().ok_or_else(|| anyhow::anyhow!("missing value for {a}"));
        match a.as_str() {
            "--formal" => formal = Some(PathBuf::from(v()?)),
            "--certificate" => cert = Some(v()?),
            "--expected" => expected = Some(PathBuf::from(v()?)),
            "--policy" => policy = Some(PathBuf::from(v()?)),
            "--out" => out = Some(PathBuf::from(v()?)),
            "--work" => work = PathBuf::from(v()?),
            "--cache" => cache = PathBuf::from(v()?),
            "--native-model" => {
                let s = v()?;
                let (d, m) = s.split_once('@').ok_or_else(|| anyhow::anyhow!("--native-model DECL@MODULE"))?;
                route = native::VerifierRoute::NativeLean(native::NativeLeanRoute::new(d, m));
            }
            "--candidate-native-binary" => {
                cand_bin = Some(digest::sha256_file(std::path::Path::new(&v()?))?);
            }
            "--trusted" => {
                let s = v()?;
                let (n, d) = s.split_once('=').ok_or_else(|| anyhow::anyhow!("--trusted NAME=DIR[@Mod.Prefix,...]"))?;
                let (d, include) = match d.split_once('@') {
                    Some((d, inc)) => (d, Some(inc.split(',').map(String::from).collect())),
                    None => (d, None),
                };
                trusted.push(TrustedPackage { name: n.into(), src_root: PathBuf::from(d), include });
            }
            _ => anyhow::bail!("unknown argument {a}"),
        }
    }
    match (&mut route, cand_bin) {
        (native::VerifierRoute::NativeLean(r), Some(d)) => r.candidate_binary_digest = Some(d),
        (native::VerifierRoute::Standard, Some(_)) => route = native::VerifierRoute::CandidateNative,
        _ => {}
    }
    let expected: TemplateExpected =
        serde_json::from_slice(&std::fs::read(expected.ok_or_else(|| anyhow::anyhow!("--expected required"))?)?)?;
    let policy: Policy = match policy {
        Some(p) => serde_json::from_slice(&std::fs::read(p)?)?,
        None => Policy::default(),
    };
    let checker = FormalChecker::new(toolchain::ToolPaths::discover()?, Box::new(BwrapDevRunner::new()?));
    let req = CheckRequest {
        formal_dir: formal.ok_or_else(|| anyhow::anyhow!("--formal required"))?,
        certificate: cert.unwrap_or_else(|| "Candidate.certificate".into()),
        trusted,
        expected: &expected,
        challenge_digest: None,
        policy,
        limits: Limits::default(),
        work_dir: work,
        cache_dir: cache,
        route,
    };
    let report = checker.check(&req);
    let json = serde_json::to_string_pretty(&report)?;
    match out {
        Some(p) => std::fs::write(p, json)?,
        None => println!("{json}"),
    }
    Ok(())
}

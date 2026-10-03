//! `formal-check` — run the formal checker on one candidate `formal/` tree.
//!
//! ```text
//! ARENA_DEV_UNSAFE=1 formal-check --formal path/to/formal --certificate Candidate.certificate \
//!     --trusted NAME=DIR [--trusted ...] --expected expected.json [--policy policy.json] \
//!     [--work DIR] [--cache DIR] [--out report.json]
//! ```
//! `expected.json` is a `TemplateExpected` (`module`, `decl`, `template`, `data`).
use arena_formal_checker::*;
use std::path::PathBuf;

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().skip(1);
    let (mut formal, mut cert, mut expected, mut policy, mut out) = (None, None, None, None, None);
    let mut trusted = Vec::new();
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
            "--trusted" => {
                let s = v()?;
                let (n, d) = s.split_once('=').ok_or_else(|| anyhow::anyhow!("--trusted NAME=DIR"))?;
                trusted.push(TrustedPackage { name: n.into(), src_root: PathBuf::from(d) });
            }
            _ => anyhow::bail!("unknown argument {a}"),
        }
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
    };
    let report = checker.check(&req);
    let json = serde_json::to_string_pretty(&report)?;
    match out {
        Some(p) => std::fs::write(p, json)?,
        None => println!("{json}"),
    }
    Ok(())
}

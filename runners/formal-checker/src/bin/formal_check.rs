//! `formal-check` — run the formal checker on one candidate `formal/` tree.
//!
//! ```text
//! ARENA_DEV_UNSAFE=1 formal-check --formal path/to/formal --certificate Candidate.certificate \
//!     --trusted NAME=DIR[@Mod.Prefix,...] [--trusted ...] --expected expected.json [--policy policy.json] \
//!     [--work DIR] [--cache DIR] [--out report.json]
//! ```
//! `expected.json` is a `TemplateExpected` (`module`, `decl`, `template`, `data`).
//!
//! Or, for a configured challenge (trusted packages + Expected template from
//! `runners/formal-checker/challenges/<name>.json`, data from the frozen
//! definition and the judge's artifact digests):
//! ```text
//! formal-check --formal F --challenge challenges/<id>.json \
//!     --challenge-config runners/formal-checker/challenges/<name>.json --repo-root <clean checkout> \
//!     --public-digest <hex> --verifier-digest <hex> [--emit-expected out.lean]
//! ```
use arena_formal_checker::*;
use std::path::PathBuf;

fn main() -> anyhow::Result<()> {
    if std::env::args().nth(1).as_deref() == Some("--print-image-digest") {
        // Dev checker "image": toolchain + tool pins + bytes of every helper binary.
        println!("{}", toolchain::ToolPaths::discover()?.image_digest()?);
        return Ok(());
    }
    let mut args = std::env::args().skip(1);
    let (mut formal, mut cert, mut expected, mut policy, mut out) = (None, None, None, None, None);
    let mut trusted = Vec::new();
    let (mut chal, mut chal_cfg, mut repo_root, mut pub_d, mut ver_d, mut emit) = (None, None, None, None, None, None);
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
            "--challenge" => chal = Some(PathBuf::from(v()?)),
            "--challenge-config" => chal_cfg = Some(PathBuf::from(v()?)),
            "--repo-root" => repo_root = Some(PathBuf::from(v()?)),
            "--public-digest" => pub_d = Some(v()?),
            "--verifier-digest" => ver_d = Some(v()?),
            "--emit-expected" => emit = Some(PathBuf::from(v()?)),
            "--cache" => cache = PathBuf::from(v()?),
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
    let mut policy: Policy = match policy {
        Some(p) => serde_json::from_slice(&std::fs::read(p)?)?,
        None => Policy::default(),
    };
    let expected: TemplateExpected = match (expected, chal_cfg) {
        (Some(e), None) => serde_json::from_slice(&std::fs::read(e)?)?,
        (None, Some(cfg_path)) => {
            let cfg = ChallengeFormalConfig::load(&cfg_path)?;
            let root = repo_root.ok_or_else(|| anyhow::anyhow!("--repo-root required"))?;
            let def: arena_types::ChallengeDefinition = serde_json::from_slice(&std::fs::read(
                chal.ok_or_else(|| anyhow::anyhow!("--challenge required"))?,
            )?)?;
            let inp = ExpectedInputs::from_definition(
                &def,
                pub_d.ok_or_else(|| anyhow::anyhow!("--public-digest required"))?,
                ver_d.ok_or_else(|| anyhow::anyhow!("--verifier-digest required"))?,
            )?;
            trusted.extend(cfg.trusted_packages(&root));
            policy.reserved_prefixes.extend(cfg.reserved_prefixes.iter().cloned());
            policy.axiom_allowlist = def.toolchain_policy.axiom_allowlist.clone();
            cfg.expected(&root, &inp)?
        }
        _ => anyhow::bail!("give exactly one of --expected or --challenge-config"),
    };
    if let Some(p) = emit {
        std::fs::write(&p, expected.render()?)?;
        eprintln!("wrote {}", p.display());
        if formal.is_none() {
            return Ok(());
        }
    }
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

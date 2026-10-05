//! `formal-check` — run the formal checker on one candidate `formal/` tree.
//!
//! ```text
//! ARENA_DEV_UNSAFE=1 formal-check --formal path/to/formal --certificate Candidate.certificate \
//!     --trusted NAME=DIR[@Mod.Prefix,...] [--trusted ...] --expected expected.json [--policy policy.json] \
//!     [--native-model Candidate.Model.verify@Candidate.Model] [--candidate-native-binary FILE]
//!     [--work DIR] [--cache DIR] [--out report.json]
//! ```
//! `--native-model` selects the native-lean route (the Expected template must
//! then define `fun model => …` and use `{{bin_digest}}`/`{{toolchain_id}}`);
//! `--candidate-native-binary` without it = candidate-built binary (rejected).
//! `expected.json` is a `TemplateExpected` (`module`, `decl`, `template`, `data`).
//!
//! Or, for a configured challenge (trusted packages + Expected template from
//! `runners/formal-checker/challenges/<name>.json`, data from the frozen
//! definition and the judge's artifact digests):
//! ```text
//! formal-check --formal F --challenge challenges/<id>.json \
//!     --challenge-config runners/formal-checker/challenges/<name>.json \
//!     (--trusted-store <ARENA_TRUSTED_TREES> | --repo-root <dir>) \
//!     --public-digest <hex> --verifier-digest <hex> [--emit-expected out.lean]
//! ```
//! The trusted packages and templates come from the challenge's pinned
//! trusted tree (`formal_spec.tree_digest`): `--trusted-store` copies it from
//! the frozen-tree store and re-verifies the copy (as the worker does);
//! `--repo-root` is accepted only if its `formal-core/` + `spec/lean/` hash
//! to the pin (so a drifted checkout is refused, never silently used).
use arena_formal_checker::*;
use std::path::PathBuf;

fn main() -> anyhow::Result<()> {
    let all: Vec<String> = std::env::args().collect();
    if all.get(1).map(String::as_str) == Some(HELPER_ARG) {
        std::process::exit(arena_sandbox::helper::helper_main(&all[2..]));
    }
    if std::env::args().nth(1).as_deref() == Some("--print-image-digest") {
        // Dev checker "image": toolchain + tool pins + bytes of every helper binary.
        println!("{}", toolchain::ToolPaths::discover()?.image_digest()?);
        return Ok(());
    }
    let mut args = std::env::args().skip(1);
    let (mut formal, mut cert, mut expected, mut policy, mut out) = (None, None, None, None, None);
    let mut trusted = Vec::new();
    let mut route = native::VerifierRoute::Standard;
    let mut cand_bin: Option<arena_types::Digest> = None;
    let (mut chal, mut chal_cfg, mut repo_root, mut pub_d, mut ver_d, mut emit) =
        (None, None, None, None, None, None);
    let mut trusted_store: Option<PathBuf> = None;
    let mut trusted_tree: Option<arena_types::Digest> = None;
    let mut work = std::env::temp_dir().join(format!("formal-check-{}", std::process::id()));
    let mut cache = toolchain::fc_home().join("ref-cache");
    while let Some(a) = args.next() {
        let mut v = || {
            args.next()
                .ok_or_else(|| anyhow::anyhow!("missing value for {a}"))
        };
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
            "--trusted-store" => trusted_store = Some(PathBuf::from(v()?)),
            "--public-digest" => pub_d = Some(v()?),
            "--verifier-digest" => ver_d = Some(v()?),
            "--emit-expected" => emit = Some(PathBuf::from(v()?)),
            "--cache" => cache = PathBuf::from(v()?),
            "--native-model" => {
                let s = v()?;
                let (d, m) = s
                    .split_once('@')
                    .ok_or_else(|| anyhow::anyhow!("--native-model DECL@MODULE"))?;
                route = native::VerifierRoute::NativeLean(native::NativeLeanRoute::new(d, m));
            }
            "--candidate-native-binary" => {
                cand_bin = Some(digest::sha256_file(std::path::Path::new(&v()?))?);
            }
            "--trusted" => {
                let s = v()?;
                let (n, d) = s
                    .split_once('=')
                    .ok_or_else(|| anyhow::anyhow!("--trusted NAME=DIR[@Mod.Prefix,...]"))?;
                let (d, include) = match d.split_once('@') {
                    Some((d, inc)) => (d, Some(inc.split(',').map(String::from).collect())),
                    None => (d, None),
                };
                trusted.push(TrustedPackage {
                    name: n.into(),
                    src_root: PathBuf::from(d),
                    include,
                });
            }
            _ => anyhow::bail!("unknown argument {a}"),
        }
    }
    match (&mut route, cand_bin) {
        (native::VerifierRoute::NativeLean(r), Some(d)) => r.candidate_binary_digest = Some(d),
        (native::VerifierRoute::Standard, Some(_)) => {
            route = native::VerifierRoute::CandidateNative
        }
        _ => {}
    }
    let mut policy: Policy = match policy {
        Some(p) => serde_json::from_slice(&std::fs::read(p)?)?,
        None => Policy::default(),
    };
    let expected: TemplateExpected = match (expected, chal_cfg) {
        (Some(e), None) => serde_json::from_slice(&std::fs::read(e)?)?,
        (None, Some(cfg_path)) => {
            let cfg = ChallengeFormalConfig::load(&cfg_path)?;
            let def: arena_types::ChallengeDefinition = serde_json::from_slice(&std::fs::read(
                chal.ok_or_else(|| anyhow::anyhow!("--challenge required"))?,
            )?)?;
            let pin = def.semantic_scope.formal_spec.tree_digest.clone();
            let root = match (trusted_store, repo_root) {
                (Some(store), None) => {
                    let root = work.with_extension("trusted-tree");
                    let _ = std::fs::remove_dir_all(&root);
                    arena_types::trusted_tree::materialize(&store, &pin, &root)
                        .map_err(|e| anyhow::anyhow!("pinned trusted tree: {e}"))?;
                    root
                }
                (None, Some(root)) => {
                    let got = arena_types::trusted_tree::digest_of(&root)?;
                    if got != pin {
                        anyhow::bail!(
                            "{}: formal-core + spec/lean hash to {got}, but the challenge pins {pin} \
                             (use --trusted-store with the frozen tree)",
                            root.display()
                        );
                    }
                    root
                }
                _ => anyhow::bail!("give exactly one of --trusted-store or --repo-root"),
            };
            trusted_tree = Some(pin);
            let inp = ExpectedInputs::from_definition(
                &def,
                pub_d.ok_or_else(|| anyhow::anyhow!("--public-digest required"))?,
                match (&route, ver_d) {
                    (native::VerifierRoute::NativeLean(_), _) => String::new(),
                    (_, d) => d.ok_or_else(|| anyhow::anyhow!("--verifier-digest required"))?,
                },
            )?;
            trusted.extend(cfg.trusted_packages(&root));
            policy
                .reserved_prefixes
                .extend(cfg.reserved_prefixes.iter().cloned());
            policy.axiom_allowlist = def.toolchain_policy.axiom_allowlist.clone();
            if matches!(route, native::VerifierRoute::NativeLean(_)) {
                cfg.expected_native_lean(&root, &inp)?
            } else {
                cfg.expected(&root, &inp)?
            }
        }
        _ => anyhow::bail!("give exactly one of --expected or --challenge-config"),
    };
    if let Some(p) = emit {
        // native-lean: the binary digest is only known after the judge build.
        let extra = if matches!(route, native::VerifierRoute::NativeLean(_)) {
            std::collections::BTreeMap::from([
                ("bin_digest".to_string(), LeanValue::Bytes("00".repeat(32))),
                (
                    "toolchain_id".to_string(),
                    LeanValue::Str("<judge build>".into()),
                ),
            ])
        } else {
            Default::default()
        };
        std::fs::write(&p, expected.render_with(&extra)?)?;
        eprintln!("wrote {}", p.display());
        if formal.is_none() {
            return Ok(());
        }
    }
    let helper = arena_sandbox::HelperCommand {
        exe: std::env::current_exe()?,
        prefix_args: vec![HELPER_ARG.into()],
    };
    let runner = SandboxRunner::bwrap_dev(helper, work.with_extension("sandbox"))?;
    let checker = FormalChecker::new(toolchain::ToolPaths::discover()?, Box::new(runner));
    let req = CheckRequest {
        formal_dir: formal.ok_or_else(|| anyhow::anyhow!("--formal required"))?,
        certificate: cert.unwrap_or_else(|| "Candidate.certificate".into()),
        trusted,
        expected: &expected,
        challenge_digest: None,
        trusted_tree,
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

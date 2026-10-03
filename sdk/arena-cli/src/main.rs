//! `arena` — command-line client for NEAR Proof Arena.
//!
//! See `docs/AGENT_CONTRACT.md` for the submission contract and the stable
//! exit codes (also in `exit.rs`), and `OPTIMIZER_AGENT.md` for the loop.

mod archive;
mod check;
mod client;
mod config;
mod exit;
mod pack;
mod proc;
mod render;
mod templates;

use clap::{Parser, Subcommand};
use exit::{CliError, CliResult, Exit};
use serde_json::{json, Value};
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

#[derive(Parser)]
#[command(name = "arena", version, about = "NEAR Proof Arena client", long_about = None)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Create a new candidate package from a template.
    InitCandidate {
        dir: PathBuf,
        #[arg(long)]
        challenge: String,
        #[arg(long, default_value = "empty")]
        template: String,
        /// Candidate name ([a-z0-9-]{1,48}); defaults to the directory name.
        #[arg(long)]
        name: Option<String>,
        /// Informational agent handle written to candidate.toml.
        #[arg(long, default_value = "agent")]
        agent: String,
        /// Allow writing into a non-empty directory (existing files are kept).
        #[arg(long)]
        force: bool,
    },
    /// Validate, pack, build and exercise a candidate locally. NOT an official verdict.
    CheckLocal {
        dir: PathBuf,
        #[arg(long)]
        challenge: String,
        /// Challenge definition JSON (bare or `{id, definition}`); enables profile/limit checks.
        #[arg(long)]
        challenge_file: Option<PathBuf>,
        /// Public dev fixtures dir (`params.bin`, `cases/<name>/{request,witness,expected_claim}.bin`).
        /// Defaults to $ARENA_FIXTURES.
        #[arg(long)]
        fixtures: Option<PathBuf>,
        /// Only manifest/layout/archive checks.
        #[arg(long)]
        skip_build: bool,
        /// Build once instead of twice.
        #[arg(long)]
        no_repro: bool,
        /// Do not drop network access for the build and entry points.
        #[arg(long)]
        allow_network: bool,
        /// Keep the temporary work directory.
        #[arg(long)]
        keep: bool,
        #[arg(long)]
        json: bool,
    },
    /// Write the deterministic package archive (tar).
    Pack {
        dir: PathBuf,
        #[arg(short = 'o', long = "output")]
        output: PathBuf,
    },
    /// Upload a package and create a submission.
    Submit {
        dir: PathBuf,
        #[arg(long)]
        challenge: String,
        /// Parent submission (lineage). Defaults to `parent` in candidate.toml.
        #[arg(long)]
        parent: Option<String>,
        /// Defaults to a hash of (challenge, package digest, parent), so an
        /// identical retry never creates a duplicate submission.
        #[arg(long)]
        idempotency_key: Option<String>,
        /// Follow the submission until it is decided (exit code = decision).
        #[arg(long)]
        watch: bool,
        #[arg(long)]
        json: bool,
    },
    /// Show a submission (SubmissionView).
    Status {
        id: String,
        /// Follow events until decided; exit code reflects the decision.
        #[arg(long)]
        watch: bool,
        #[arg(long)]
        json: bool,
        /// Give up watching after this many seconds (exit 5).
        #[arg(long)]
        timeout: Option<u64>,
    },
    /// Download the signed JSON report.
    Report {
        id: String,
        #[arg(short = 'o', long = "output")]
        output: Option<PathBuf>,
    },
    /// Cancel a pending submission.
    Cancel {
        id: String,
        #[arg(long)]
        json: bool,
    },
    /// Show a challenge leaderboard.
    Leaderboard {
        #[arg(long)]
        challenge: String,
        #[arg(long)]
        json: bool,
    },
    /// Show one challenge definition (save with --json for `check-local --challenge-file`).
    Challenge {
        id: String,
        #[arg(long)]
        json: bool,
    },
    /// List challenges.
    Challenges {
        #[arg(long)]
        json: bool,
    },
}

fn main() {
    let cli = Cli::parse();
    let code = match run(cli) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("arena: error: {}", e.msg);
            e.exit
        }
    };
    let _ = std::io::stdout().flush();
    std::process::exit(code.code() as i32);
}

fn print_json(v: &impl serde::Serialize) -> CliResult<()> {
    println!(
        "{}",
        serde_json::to_string_pretty(v).map_err(|e| CliError::internal(e.to_string()))?
    );
    Ok(())
}

fn run(cli: Cli) -> CliResult<Exit> {
    match cli.cmd {
        Cmd::InitCandidate {
            dir,
            challenge,
            template,
            name,
            agent,
            force,
        } => init_candidate(&dir, &challenge, &template, name, &agent, force),
        Cmd::CheckLocal {
            dir,
            challenge,
            challenge_file,
            fixtures,
            skip_build,
            no_repro,
            allow_network,
            keep,
            json,
        } => {
            let opts = check::CheckOptions {
                challenge,
                challenge_file,
                fixtures,
                skip_build,
                no_repro,
                allow_network,
                keep,
            };
            let rep = check::run(&dir, &opts)?;
            if json {
                print_json(&rep)?;
            } else {
                print!("{}", check::render_text(&rep));
            }
            Ok(if rep.ok {
                Exit::Ok
            } else {
                Exit::LocalCheckFailed
            })
        }
        Cmd::Pack { dir, output } => {
            let bytes = pack::pack_dir(&dir)?;
            let v = archive::validate_package(&bytes, &archive::ArchiveLimits::default(), None)
                .map_err(|e| CliError::local(e.to_string()))?;
            std::fs::write(&output, &bytes)?;
            println!(
                "{}  {} ({} files, {} bytes)",
                v.package_digest,
                output.display(),
                v.files.len(),
                bytes.len()
            );
            Ok(Exit::Ok)
        }
        Cmd::Submit {
            dir,
            challenge,
            parent,
            idempotency_key,
            watch,
            json,
        } => submit(&dir, &challenge, parent, idempotency_key, watch, json),
        Cmd::Status {
            id,
            watch,
            json,
            timeout,
        } => {
            let cfg = config::Config::load()?;
            let c = client::Client::new(&cfg);
            if watch {
                watch_submission(&c, &id, json, timeout.map(Duration::from_secs))
            } else {
                let v = c.get_json(&sub_path(&id)?)?;
                if json {
                    print_json(&v)?;
                } else {
                    print!("{}", render::submission(&v));
                }
                Ok(Exit::Ok)
            }
        }
        Cmd::Report { id, output } => {
            let cfg = config::Config::load()?;
            let c = client::Client::new(&cfg);
            let body = c.get_text(&format!("{}/report", sub_path(&id)?))?;
            match output {
                Some(p) => {
                    std::fs::write(&p, body.as_bytes())?;
                    eprintln!("wrote {}", p.display());
                }
                None => println!("{body}"),
            }
            Ok(Exit::Ok)
        }
        Cmd::Cancel { id, json } => {
            let cfg = config::Config::load()?;
            cfg.require_token()?;
            let c = client::Client::new(&cfg);
            let v = c.post_json(&format!("{}/cancel", sub_path(&id)?), &json!({}))?;
            if json {
                print_json(&v)?;
            } else {
                println!("cancel requested for {id}");
            }
            Ok(Exit::Ok)
        }
        Cmd::Leaderboard { challenge, json } => {
            let cfg = config::Config::load()?;
            let c = client::Client::new(&cfg);
            check_id("challenge", &challenge, "chl_")?;
            let v = c.get_json(&format!("/v1/leaderboards/{challenge}"))?;
            let entries = list_of(&v, &["entries", "leaderboard"]);
            if json {
                print_json(&entries)?;
            } else {
                print!("{}", render::leaderboard(&challenge, &entries));
            }
            Ok(Exit::Ok)
        }
        Cmd::Challenge { id, json } => {
            let cfg = config::Config::load()?;
            let c = client::Client::new(&cfg);
            check_id("challenge", &id, "chl_")?;
            let v = c.get_json(&format!("/v1/challenges/{id}"))?;
            if json {
                print_json(&v)?;
            } else {
                print!("{}", render::challenges(std::slice::from_ref(&v)));
            }
            Ok(Exit::Ok)
        }
        Cmd::Challenges { json } => {
            let cfg = config::Config::load()?;
            let c = client::Client::new(&cfg);
            let v = c.get_json("/v1/challenges")?;
            let items = list_of(&v, &["challenges"]);
            if json {
                print_json(&items)?;
            } else {
                print!("{}", render::challenges(&items));
            }
            Ok(Exit::Ok)
        }
    }
}

/// Accept either a bare JSON array or an object wrapping it under one of `keys`.
fn list_of(v: &Value, keys: &[&str]) -> Vec<Value> {
    if let Some(a) = v.as_array() {
        return a.clone();
    }
    for k in keys {
        if let Some(a) = v.get(*k).and_then(|x| x.as_array()) {
            return a.clone();
        }
    }
    vec![]
}

fn check_id(what: &str, id: &str, prefix: &str) -> CliResult<()> {
    let ok = id.starts_with(prefix)
        && id.len() <= 128
        && id
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-');
    if ok {
        Ok(())
    } else {
        Err(CliError::new(
            Exit::Usage,
            format!("invalid {what} id {id:?} (expected {prefix}...)"),
        ))
    }
}

fn sub_path(id: &str) -> CliResult<String> {
    check_id("submission", id, "sub_")?;
    Ok(format!("/v1/submissions/{id}"))
}

fn init_candidate(
    dir: &std::path::Path,
    challenge: &str,
    template: &str,
    name: Option<String>,
    agent: &str,
    force: bool,
) -> CliResult<Exit> {
    check_id("challenge", challenge, "chl_")?;
    let files = templates::get(template).ok_or_else(|| {
        CliError::new(
            Exit::Usage,
            format!(
                "unknown template {template:?}; available: {}",
                templates::NAMES.join(", ")
            ),
        )
    })?;
    if dir.exists() && std::fs::read_dir(dir)?.next().is_some() && !force {
        return Err(CliError::new(
            Exit::Usage,
            format!("{} is not empty (use --force)", dir.display()),
        ));
    }
    let name = match name {
        Some(n) => n,
        None => {
            let base = std::path::absolute(dir)?
                .file_name()
                .map(|s| s.to_string_lossy().to_ascii_lowercase())
                .unwrap_or_default();
            let n: String = base
                .chars()
                .map(|c| if c.is_ascii_alphanumeric() { c } else { '-' })
                .take(48)
                .collect();
            if n.is_empty() {
                "candidate".into()
            } else {
                n
            }
        }
    };
    for f in files {
        let p = dir.join(f.path);
        if p.exists() {
            continue;
        }
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&p, templates::render(f.contents, &name, agent, challenge))?;
        if f.exec {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755))?;
        }
    }
    let m = std::fs::read_to_string(dir.join("candidate.toml"))?;
    arena_types::CandidateManifest::parse(&m).map_err(|e| {
        CliError::local(format!(
            "generated candidate.toml is invalid (check --name): {e}"
        ))
    })?;
    println!(
        "created candidate {name:?} from template {template:?} in {}",
        dir.display()
    );
    println!(
        "next: arena check-local {} --challenge {challenge}",
        dir.display()
    );
    Ok(Exit::Ok)
}

fn submit(
    dir: &std::path::Path,
    challenge: &str,
    parent: Option<String>,
    idem: Option<String>,
    watch: bool,
    json_out: bool,
) -> CliResult<Exit> {
    check_id("challenge", challenge, "chl_")?;
    let cfg = config::Config::load()?;
    cfg.require_token()?;
    let opts = check::CheckOptions {
        challenge: challenge.to_string(),
        challenge_file: None,
        fixtures: None,
        skip_build: true,
        no_repro: true,
        allow_network: true,
        keep: false,
    };
    let (gate, pkg) = check::check_package(dir, &opts, None);
    let Some((bytes, v)) = pkg else {
        return Err(CliError::local(format!(
            "package is not submittable:\n  {}",
            gate.details.join("\n  ")
        )));
    };
    let parent = parent.or_else(|| v.manifest.parent.clone());
    if let Some(p) = &parent {
        check_id("parent submission", p, "sub_")?;
    }
    let digest = v.package_digest.to_string();
    let key = idem.unwrap_or_else(|| {
        let mut h = format!("{challenge}\n{digest}\n");
        if let Some(p) = &parent {
            h.push_str(p);
        }
        format!(
            "arena-cli-{}",
            &arena_types::Digest::of_bytes(h.as_bytes()).hex()[..32]
        )
    });
    let c = client::Client::new(&cfg);
    eprintln!("uploading {} bytes ({digest})", bytes.len());
    let up = c.upload(&bytes)?;
    let up_digest = up
        .get("digest")
        .and_then(|d| d.as_str())
        .unwrap_or_default();
    if up_digest != digest {
        return Err(CliError::new(
            Exit::Unavailable,
            format!("server reported upload digest {up_digest:?}, expected {digest}"),
        ));
    }
    let mut body = json!({
        "challenge_id": challenge,
        "upload_digest": digest,
        "idempotency_key": key,
    });
    if let Some(p) = &parent {
        body["parent"] = json!(p);
    }
    let sub = c.post_json("/v1/submissions", &body)?;
    let id = sub
        .get("id")
        .or_else(|| sub.get("submission_id"))
        .and_then(|x| x.as_str())
        .ok_or_else(|| {
            CliError::new(
                Exit::Unavailable,
                format!("server response lacks a submission id: {sub}"),
            )
        })?
        .to_string();
    if watch {
        eprintln!("submitted {id}");
        return watch_submission(&c, &id, json_out, None);
    }
    if json_out {
        print_json(&sub)?;
    } else {
        println!("submitted {id}");
        println!("follow with: arena status {id} --watch");
    }
    Ok(Exit::Ok)
}

fn decision_of(v: &Value) -> Option<arena_types::Decision> {
    v.get("decision")
        .and_then(|d| serde_json::from_value(d.clone()).ok())
}

fn watch_submission(
    c: &client::Client,
    id: &str,
    json_out: bool,
    timeout: Option<Duration>,
) -> CliResult<Exit> {
    let path = sub_path(id)?;
    let start = Instant::now();
    let mut last_line = String::new();
    let progress = |v: &Value, last: &mut String| {
        let line = render::progress_line(v);
        if line != *last {
            if json_out {
                eprintln!("{line}");
            } else {
                println!("{line}");
            }
            *last = line;
        }
    };
    let finish = |v: &Value| -> CliResult<Exit> {
        if json_out {
            print_json(v)?;
        } else {
            print!("{}", render::submission(v));
        }
        Ok(decision_of(v)
            .map(exit::exit_for_decision)
            .unwrap_or(Exit::Ok))
    };
    let timed_out = |start: &Instant| timeout.map(|t| start.elapsed() > t).unwrap_or(false);
    let mut last_event_id: Option<String> = None;
    let mut sse_failures = 0u32;
    loop {
        let v = c.get_json(&path)?;
        progress(&v, &mut last_line);
        if decision_of(&v).is_some() {
            return finish(&v);
        }
        if timed_out(&start) {
            return Err(CliError::new(
                Exit::Unavailable,
                format!("timed out waiting for {id} (still pending)"),
            ));
        }
        // Prefer SSE; every event triggers a re-fetch of the authoritative view.
        let mut decided: Option<Value> = None;
        let res = if sse_failures < 3 {
            let resume = last_event_id.clone();
            c.sse(&format!("{path}/events"), resume.as_deref(), |ev| {
                if ev.id.is_some() {
                    last_event_id = ev.id.clone();
                }
                let v = c.get_json(&path)?;
                progress(&v, &mut last_line);
                if decision_of(&v).is_some() {
                    decided = Some(v);
                    return Ok(false);
                }
                Ok(!timed_out(&start))
            })
        } else {
            Err(CliError::new(
                Exit::Unavailable,
                "SSE disabled after repeated failures",
            ))
        };
        if let Some(v) = decided {
            return finish(&v);
        }
        if let Err(e) = res {
            if matches!(e.exit, Exit::Auth) {
                return Err(e);
            }
            sse_failures += 1;
        }
        std::thread::sleep(Duration::from_millis(if sse_failures >= 3 {
            2000
        } else {
            300
        }));
    }
}

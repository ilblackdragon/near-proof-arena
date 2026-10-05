use anyhow::{bail, Context, Result};
use arena_admin::challenge_file::{
    self, check_supersession, identity, load_definition, sign_and_write,
};
use arena_admin::{policy, GovernedSet, Keypair, PublicKey};
use clap::{Parser, Subcommand};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

/// NEAR Proof Arena governance CLI.
#[derive(Parser)]
#[command(name = "arena-admin", version)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Generate an ed25519 governance keypair. The private key is written
    /// 0600 and never inside a git working tree.
    Keygen {
        #[arg(long)]
        private: PathBuf,
        #[arg(long)]
        public: PathBuf,
        #[arg(long)]
        label: String,
        /// Mark the key as dev-only (cannot sign formal-tier challenges).
        #[arg(long)]
        dev_only: bool,
        /// Permit writing the private key below a directory that contains a
        /// `.git` (e.g. a stray `git init` in a home directory). Never use
        /// this for a path inside the arena repository.
        #[arg(long)]
        allow_inside_git_tree: bool,
    },
    /// Print the canonical (JCS) bytes of a challenge definition.
    Canonicalize { def: PathBuf },
    /// Print the challenge id and full digest of a definition.
    Id { def: PathBuf },
    /// Policy-check an (unsigned) draft definition.
    Check {
        def: PathBuf,
        #[arg(long, default_value = "security")]
        security_dir: PathBuf,
    },
    /// Validate all governed files under security/.
    CheckGoverned {
        #[arg(long, default_value = "security")]
        security_dir: PathBuf,
    },
    /// Policy-check, sign and write challenges/<id>.json + <id>.sig.
    Sign {
        def: PathBuf,
        #[arg(long)]
        key: PathBuf,
        #[arg(long, default_value = "challenges")]
        challenges_dir: PathBuf,
        #[arg(long, default_value = "security")]
        security_dir: PathBuf,
    },
    /// Verify signed challenge files (id, signature, governed profile, policy).
    Verify {
        files: Vec<PathBuf>,
        /// Trusted governance public key(s).
        #[arg(long = "pubkey", required = true)]
        pubkeys: Vec<PathBuf>,
        #[arg(long, default_value = "security")]
        security_dir: PathBuf,
        /// Verify every challenges/chl_*.json in this directory.
        #[arg(long)]
        all_in: Option<PathBuf>,
    },
    /// Sign a successor challenge that supersedes an existing one. The old
    /// file is kept (historical rankings stay attached to it).
    Supersede {
        #[arg(long)]
        old: PathBuf,
        /// Draft for the new definition; `supersedes` is set to the old id if null.
        #[arg(long)]
        draft: PathBuf,
        #[arg(long)]
        key: PathBuf,
        #[arg(long = "pubkey", required = true)]
        pubkeys: Vec<PathBuf>,
        #[arg(long, default_value = "challenges")]
        challenges_dir: PathBuf,
        #[arg(long, default_value = "security")]
        security_dir: PathBuf,
        #[arg(long)]
        allow_downgrade: bool,
    },
    /// Compute the TreeDigest of a directory (docs/CONTRACTS.md §1).
    TreeDigest { dir: PathBuf },
    /// Publish the frozen trusted tree (formal-core + spec/lean) of a git
    /// commit into the judge's trusted-tree store as `<store>/<hex>/`. The
    /// digest is recomputed from the extracted files and must equal the pin
    /// of every `--challenge` (and every `--expect`).
    FreezeTrusted {
        /// Commit (or ref) whose tracked formal-core/ + spec/lean/ to freeze.
        #[arg(long)]
        commit: String,
        /// The trusted-tree store (`ARENA_TRUSTED_TREES`).
        #[arg(long)]
        store: PathBuf,
        /// Repository to read the commit from.
        #[arg(long, default_value = ".")]
        repo: PathBuf,
        /// Challenge file(s) whose `formal_spec.tree_digest` must match.
        #[arg(long = "challenge")]
        challenges: Vec<PathBuf>,
        /// Expected TreeDigest(s) (`sha256:<hex>`).
        #[arg(long)]
        expect: Vec<String>,
    },
    /// Registration gate: each challenge's pinned trusted tree is in the
    /// store and its files hash to the pin (demo tier: not required).
    CheckTrusted {
        #[arg(long)]
        store: PathBuf,
        #[arg(required = true)]
        files: Vec<PathBuf>,
    },
}

fn print_findings(f: &policy::Findings) {
    for w in &f.warnings {
        eprintln!("warning: {w}");
    }
    for e in &f.errors {
        eprintln!("error: {e}");
    }
}

fn load_keys(paths: &[PathBuf]) -> Result<Vec<PublicKey>> {
    paths
        .iter()
        .map(|p| PublicKey::load(p).with_context(|| p.display().to_string()))
        .collect()
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Keygen {
            private,
            public,
            label,
            dev_only,
            allow_inside_git_tree,
        } => {
            if public.exists() {
                bail!("{} exists", public.display());
            }
            let kp = Keypair::generate(dev_only, &label);
            if allow_inside_git_tree {
                if let Some(repo) = arena_admin::keys::inside_git_worktree(&private) {
                    if repo.join("Cargo.toml").exists() || repo.join("challenges").exists() {
                        bail!("--allow-inside-git-tree cannot be used inside a source repository ({})", repo.display());
                    }
                    eprintln!(
                        "warning: private key placed below git tree {} (override given)",
                        repo.display()
                    );
                }
            }
            kp.write_private(&private, allow_inside_git_tree)?;
            let pubf = kp.public_file();
            fs::write(&public, serde_json::to_string_pretty(&pubf)? + "\n")?;
            println!("key_id {}", pubf.key_id);
            println!(
                "private key: {} (0600) — move to offline storage/HSM; never commit",
                private.display()
            );
            println!("public key:  {}", public.display());
        }
        Cmd::Canonicalize { def } => {
            let d = load_definition(&def)?;
            std::io::stdout().write_all(&identity(&d)?.jcs)?;
        }
        Cmd::Id { def } => {
            let d = load_definition(&def)?;
            let i = identity(&d)?;
            println!("{}\n{}", i.id, i.digest);
        }
        Cmd::Check { def, security_dir } => {
            let gov = GovernedSet::load(&security_dir)?;
            let d = load_definition(&def)?;
            let f = policy::check_definition(&d, &gov);
            print_findings(&f);
            if !f.ok() {
                bail!("{} policy error(s)", f.errors.len());
            }
            println!("OK {}", identity(&d)?.id);
        }
        Cmd::CheckGoverned { security_dir } => {
            let gov = GovernedSet::load(&security_dir)?;
            println!(
                "OK {} profile(s), {} assumption(s)",
                gov.profiles.len(),
                gov.assumptions.len()
            );
            for (id, a) in &gov.assumptions {
                if a.lean_decl_digest.is_none() {
                    eprintln!("warning: assumption {id} not pinned to a formal-core declaration digest yet");
                }
            }
        }
        Cmd::Sign {
            def,
            key,
            challenges_dir,
            security_dir,
        } => {
            let gov = GovernedSet::load(&security_dir)?;
            let kp = Keypair::load_private(&key)?;
            let d = load_definition(&def)?;
            let (ident, f) = sign_and_write(&d, &kp, &gov, &challenges_dir)?;
            print_findings(&f);
            let pk = PublicKey::parse(&serde_json::to_string(&kp.public_file())?)?;
            let (jp, _) = challenge_file::paths_for(&challenges_dir, &ident.id);
            challenge_file::verify_file(&jp, &[pk], &gov)?;
            println!("signed {} ({})", jp.display(), ident.digest);
        }
        Cmd::Verify {
            mut files,
            pubkeys,
            security_dir,
            all_in,
        } => {
            let gov = GovernedSet::load(&security_dir)?;
            let keys = load_keys(&pubkeys)?;
            if let Some(dir) = all_in {
                files.extend(challenge_files(&dir)?);
            }
            if files.is_empty() {
                bail!("no challenge files given");
            }
            let mut failed = 0;
            for f in &files {
                match challenge_file::verify_file(f, &keys, &gov) {
                    Ok(v) => {
                        print_findings(&v.findings);
                        println!("OK   {} tier={:?} name={}", v.id, v.def.tier, v.def.name);
                    }
                    Err(e) => {
                        failed += 1;
                        println!("FAIL {}: {e:#}", f.display());
                    }
                }
            }
            if failed > 0 {
                bail!("{failed} challenge file(s) failed verification");
            }
        }
        Cmd::Supersede {
            old,
            draft,
            key,
            pubkeys,
            challenges_dir,
            security_dir,
            allow_downgrade,
        } => {
            let gov = GovernedSet::load(&security_dir)?;
            let keys = load_keys(&pubkeys)?;
            let old_v = challenge_file::verify_file(&old, &keys, &gov)
                .context("superseded challenge must verify")?;
            let mut new = load_definition(&draft)?;
            if new.supersedes.is_none() {
                new.supersedes = Some(old_v.id.clone());
            }
            let f = check_supersession(&old_v.def, &old_v.id, &new, allow_downgrade);
            print_findings(&f);
            if !f.ok() {
                bail!("supersession check failed");
            }
            let kp = Keypair::load_private(&key)?;
            let (ident, pf) = sign_and_write(&new, &kp, &gov, &challenges_dir)?;
            print_findings(&pf);
            println!("{} supersedes {} (old file retained)", ident.id, old_v.id);
        }
        Cmd::TreeDigest { dir } => {
            println!("{}", challenge_file::tree_digest(&dir)?);
        }
        Cmd::FreezeTrusted {
            commit,
            store,
            repo,
            challenges,
            expect,
        } => {
            let mut pins: Vec<arena_types::Digest> = Vec::new();
            for e in expect {
                pins.push(
                    e.clone()
                        .try_into()
                        .map_err(|x: String| anyhow::anyhow!("--expect {e}: {x}"))?,
                );
            }
            for c in &challenges {
                let def = load_definition(c).with_context(|| c.display().to_string())?;
                pins.push(def.semantic_scope.formal_spec.tree_digest.clone());
            }
            if pins.is_empty() {
                bail!("give --challenge and/or --expect: a trusted tree is frozen for a pin");
            }
            let f = arena_admin::trusted::freeze(&repo, &commit, &store, &pins)?;
            println!(
                "{} {} (commit {}{})",
                f.digest,
                f.dir.display(),
                f.commit,
                if f.existed {
                    ", already published; re-verified"
                } else {
                    ""
                }
            );
        }
        Cmd::CheckTrusted { store, files } => {
            let mut bad = 0;
            for p in &files {
                let res = load_definition(p)
                    .and_then(|def| arena_admin::trusted::check_available(&store, &def));
                match res {
                    Ok(Some(dir)) => println!("OK   {}: {}", p.display(), dir.display()),
                    Ok(None) => {
                        println!("OK   {}: demo tier, no trusted tree required", p.display())
                    }
                    Err(e) => {
                        bad += 1;
                        println!("FAIL {}: {e:#}", p.display());
                    }
                }
            }
            if bad > 0 {
                bail!("{bad} challenge(s) without their pinned trusted tree");
            }
        }
    }
    Ok(())
}

fn challenge_files(dir: &Path) -> Result<Vec<PathBuf>> {
    let mut v: Vec<PathBuf> = fs::read_dir(dir)?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.extension().and_then(|x| x.to_str()) == Some("json")
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with("chl_"))
        })
        .collect();
    v.sort();
    Ok(v)
}

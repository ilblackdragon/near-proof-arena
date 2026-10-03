//! `arena-server serve` configuration (environment contract: docs/DEPLOYMENT.md §2).

use arena_orchestrator::signer::ReportSigner;
use ed25519_dalek::VerifyingKey;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};

#[derive(clap::Args, Debug, Clone)]
pub struct ServeArgs {
    /// Development mode (same as ARENA_ENV=dev): loopback-only listeners,
    /// ephemeral report key and generated dev governance key if none configured.
    #[arg(long)]
    pub dev: bool,
    /// `dev` or `production`. Required (no default) unless `--dev` is given.
    #[arg(long = "env", env = "ARENA_ENV")]
    pub arena_env: Option<String>,
    /// Public API listener.
    #[arg(long, env = "ARENA_BIND_ADDR", default_value = "127.0.0.1:8471")]
    pub bind: String,
    /// Internal worker API listener.
    #[arg(
        long,
        env = "ARENA_WORKER_API_BIND_ADDR",
        default_value = "127.0.0.1:8472"
    )]
    pub worker_bind: String,
    /// `arena_api` role.
    #[arg(long, env = "ARENA_DATABASE_URL")]
    pub database_url: String,
    /// Optional separate role for the worker gateway (defaults to ARENA_DATABASE_URL).
    #[arg(long, env = "ARENA_WORKER_GATEWAY_DATABASE_URL")]
    pub worker_gateway_database_url: Option<String>,
    /// Optional separate role for admin endpoints (defaults to ARENA_DATABASE_URL).
    #[arg(long, env = "ARENA_ADMIN_DATABASE_URL")]
    pub admin_database_url: Option<String>,
    #[arg(long, env = "ARENA_OBJECT_STORE_DIR")]
    pub object_store_dir: PathBuf,
    /// Signed challenge definitions (`<id>.json` + `<id>.sig`), registered at startup.
    #[arg(long, env = "ARENA_CHALLENGES_DIR")]
    pub challenges_dir: Option<PathBuf>,
    /// ed25519 report signing key: PKCS#8 PEM or 64-hex seed. Control plane only.
    #[arg(long, env = "ARENA_REPORT_SIGNING_KEY_FILE")]
    pub report_signing_key_file: Option<PathBuf>,
    /// Trusted governance public keys (hex or base64, comma separated).
    #[arg(long, env = "ARENA_GOVERNANCE_PUBKEYS", value_delimiter = ',')]
    pub governance_pubkeys: Vec<String>,
    /// Governance public key files (comma separated): `arena-governance-pubkey-v1`
    /// JSON (as in `challenges/governance-*.pub`), SPKI PEM blocks, or hex lines.
    #[arg(long, env = "ARENA_GOVERNANCE_PUBKEY_FILE", value_delimiter = ',')]
    pub governance_pubkey_file: Vec<PathBuf>,
    /// Governed `security/` directory (profiles + assumptions). When set, every
    /// challenge must also pass the governance policy (tools/arena-admin).
    #[arg(long, env = "ARENA_SECURITY_DIR")]
    pub security_dir: Option<PathBuf>,
    /// Hardened config (TOML) required for any non-loopback listener.
    #[arg(long, env = "ARENA_HARDENED_CONFIG")]
    pub hardened_config: Option<PathBuf>,
    #[command(flatten)]
    pub limits: LimitArgs,
}

#[derive(clap::Args, Debug, Clone)]
pub struct LimitArgs {
    #[arg(long, env = "ARENA_MAX_UPLOAD_BYTES", default_value_t = 256 << 20)]
    pub max_upload_bytes: u64,
    #[arg(long, env = "ARENA_MAX_ARTIFACT_BYTES", default_value_t = 2 << 30)]
    pub max_artifact_bytes: u64,
    #[arg(long, env = "ARENA_QUOTA_SUBMISSIONS_PER_DAY", default_value_t = 50)]
    pub submissions_per_day: i64,
    #[arg(long, env = "ARENA_QUOTA_UPLOAD_BYTES_PER_DAY", default_value_t = 4 << 30)]
    pub upload_bytes_per_day: i64,
    #[arg(long, env = "ARENA_QUOTA_ACTIVE_RUNS", default_value_t = 4)]
    pub active_runs: i64,
    #[arg(long, env = "ARENA_RATE_LIMIT_PER_MINUTE", default_value_t = 120)]
    pub rate_per_minute: u32,
    #[arg(long, env = "ARENA_JOB_MAX_ATTEMPTS", default_value_t = 3)]
    pub max_attempts: i32,
    #[arg(long, env = "ARENA_RETRY_BACKOFF_SECS", default_value_t = 5)]
    pub retry_backoff_secs: u64,
    #[arg(long, env = "ARENA_LEASE_SECS", default_value_t = 300)]
    pub lease_secs: u64,
}

/// Hardened configuration file. Its presence (with explicit acknowledgements)
/// is required before any listener binds a non-loopback address.
#[derive(serde::Deserialize, Debug, Clone, Default)]
#[serde(deny_unknown_fields)]
pub struct HardenedConfig {
    /// Must be `true` to allow non-loopback listeners.
    pub allow_non_loopback_bind: bool,
    /// Why non-loopback exposure is safe here (logged at startup), e.g.
    /// "container netns; host publishes on loopback only".
    pub justification: String,
    /// Production: the public listener sits behind a TLS-terminating proxy.
    #[serde(default)]
    pub behind_tls_proxy: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Env {
    Dev,
    Production,
}

/// Validated startup decisions.
pub struct Resolved {
    pub env: Env,
    pub bind: SocketAddr,
    pub worker_bind: SocketAddr,
    pub signer: ReportSigner,
    pub governance_keys: Vec<VerifyingKey>,
    pub dev_only_keys: Vec<VerifyingKey>,
    pub governed: Option<arena_admin::GovernedSet>,
}

/// Parse a listener address. Only IP literals are accepted (no hostnames, so
/// `127.evil.com`/`localhost.evil` can never be mistaken for loopback);
/// `localhost` is mapped to 127.0.0.1.
pub fn parse_bind(s: &str) -> Result<SocketAddr, String> {
    let s2 = s
        .strip_prefix("localhost:")
        .map(|p| format!("127.0.0.1:{p}"));
    s2.as_deref()
        .unwrap_or(s)
        .parse::<SocketAddr>()
        .map_err(|_| {
            format!("bind address {s:?} must be an IP literal with port (e.g. 127.0.0.1:8471)")
        })
}

pub fn check_binds(
    env: Env,
    binds: &[(&str, SocketAddr)],
    hardened: Option<&HardenedConfig>,
) -> Result<(), String> {
    for (name, addr) in binds {
        if addr.ip().is_loopback() {
            continue;
        }
        let Some(h) = hardened else {
            return Err(format!(
                "{name} would bind non-loopback address {addr}; refusing without a hardened config \
                 (ARENA_HARDENED_CONFIG with allow_non_loopback_bind = true)"
            ));
        };
        if !h.allow_non_loopback_bind || h.justification.trim().is_empty() {
            return Err(format!(
                "{name} would bind {addr}; hardened config must set allow_non_loopback_bind = true and a justification"
            ));
        }
        if env == Env::Production && *name == "public API" && !h.behind_tls_proxy {
            return Err(
                "production public API on a non-loopback address requires behind_tls_proxy = true"
                    .into(),
            );
        }
        tracing::warn!(%addr, justification = %h.justification, "{name} bound to a non-loopback address");
    }
    Ok(())
}

/// Parse governance keys; returns `(key, dev_only)` pairs.
pub fn parse_pubkeys_text(text: &str) -> Result<Vec<(VerifyingKey, bool)>, String> {
    use ed25519_dalek::pkcs8::DecodePublicKey;
    if text.trim_start().starts_with('{') {
        let k = arena_admin::PublicKey::parse(text)
            .map_err(|e| format!("governance key file: {e:#}"))?;
        return Ok(vec![(k.key, k.file.dev_only)]);
    }
    let mut keys = Vec::new();
    let mut rest = text;
    while let Some(start) = rest.find("-----BEGIN PUBLIC KEY-----") {
        let end_marker = "-----END PUBLIC KEY-----";
        let end = rest[start..]
            .find(end_marker)
            .ok_or("unterminated PEM block")?
            + start
            + end_marker.len();
        keys.push((
            VerifyingKey::from_public_key_pem(&rest[start..end])
                .map_err(|e| format!("pem: {e}"))?,
            false,
        ));
        rest = &rest[end..];
    }
    if keys.is_empty() {
        for line in text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
        {
            keys.push((arena_db::challenge::parse_pubkey(line)?, false));
        }
    }
    Ok(keys)
}

/// Load (or create) the dev-only governance key stored next to the object store.
fn dev_governance_key(store_dir: &Path) -> Result<VerifyingKey, String> {
    use ed25519_dalek::pkcs8::DecodePrivateKey;
    let path = store_dir.join("dev-governance-signing.pem");
    if !path.exists() {
        let (pem, _) = ReportSigner::generate_pem();
        write_secret(&path, &pem)?;
    }
    let pem = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
    let k = ed25519_dalek::SigningKey::from_pkcs8_pem(&pem).map_err(|e| e.to_string())?;
    tracing::warn!(path = %path.display(), "DEV: using generated governance key (sign challenges with `arena-server sign-challenge --key {}`)", path.display());
    Ok(k.verifying_key())
}

pub fn write_secret(path: &Path, content: &str) -> Result<(), String> {
    use std::io::Write;
    let mut o = std::fs::OpenOptions::new();
    o.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        o.mode(0o600);
    }
    let mut f = o
        .open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    f.write_all(content.as_bytes()).map_err(|e| e.to_string())
}

impl ServeArgs {
    pub fn resolve(&self) -> Result<Resolved, String> {
        let env = match (self.dev, self.arena_env.as_deref()) {
            (true, None | Some("dev")) => Env::Dev,
            (true, Some(other)) => return Err(format!("--dev conflicts with ARENA_ENV={other}")),
            (false, Some("dev")) => Env::Dev,
            (false, Some("production")) => Env::Production,
            (false, Some(other)) => {
                return Err(format!(
                    "ARENA_ENV must be dev or production, got {other:?}"
                ))
            }
            (false, None) => {
                return Err("ARENA_ENV is required (dev or production), or pass --dev".into())
            }
        };
        if env == Env::Production && std::env::var_os("ARENA_DEV_UNSAFE").is_some() {
            return Err("ARENA_DEV_UNSAFE must not be set in production".into());
        }
        if env == Env::Production
            && std::env::var("ARENA_SECRETS_ORIGIN").as_deref() == Ok("dev-generator")
        {
            return Err("dev-generated secrets (ARENA_SECRETS_ORIGIN=dev-generator) are refused in production".into());
        }
        let bind = parse_bind(&self.bind)?;
        let worker_bind = parse_bind(&self.worker_bind)?;
        let hardened: Option<HardenedConfig> = match &self.hardened_config {
            Some(p) => Some(
                toml::from_str(
                    &std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?,
                )
                .map_err(|e| format!("{}: {e}", p.display()))?,
            ),
            None => None,
        };
        check_binds(
            env,
            &[("public API", bind), ("worker API", worker_bind)],
            hardened.as_ref(),
        )?;

        // ---- report signing key (never leaves this process)
        let inline = std::env::var("ARENA_REPORT_SIGNING_KEY").ok();
        let signer = match (&self.report_signing_key_file, inline, env) {
            (_, Some(_), Env::Production) => {
                return Err("inline ARENA_REPORT_SIGNING_KEY is refused in production; use ARENA_REPORT_SIGNING_KEY_FILE".into())
            }
            (Some(p), _, Env::Production) => ReportSigner::from_file(p)?,
            (Some(p), _, Env::Dev) => match ReportSigner::from_file(p) {
                Ok(s) => s,
                Err(e) if e.contains("group/others") => {
                    tracing::warn!("DEV: {e}; loading anyway");
                    ReportSigner::from_text(&std::fs::read_to_string(p).map_err(|e| e.to_string())?)?
                }
                Err(e) => return Err(e),
            },
            (None, Some(k), Env::Dev) => ReportSigner::from_text(&k)?,
            (None, None, Env::Dev) => {
                tracing::warn!("DEV: no report signing key configured; using an ephemeral key");
                ReportSigner::ephemeral()
            }
            (None, None, Env::Production) => return Err("ARENA_REPORT_SIGNING_KEY_FILE is required in production".into()),
        };

        // ---- governance keys
        let mut governance_keys = Vec::new();
        for k in self
            .governance_pubkeys
            .iter()
            .filter(|k| !k.trim().is_empty())
        {
            governance_keys.push(arena_db::challenge::parse_pubkey(k)?);
        }
        let mut dev_only_keys = Vec::new();
        for p in &self.governance_pubkey_file {
            let text = std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?;
            for (k, dev_only) in parse_pubkeys_text(&text)? {
                if dev_only {
                    if env == Env::Production {
                        return Err(format!(
                            "{}: dev-only governance key refused in production",
                            p.display()
                        ));
                    }
                    dev_only_keys.push(k);
                }
                governance_keys.push(k);
            }
        }
        let governed = match &self.security_dir {
            Some(d) => Some(
                arena_admin::GovernedSet::load(d).map_err(|e| format!("{}: {e:#}", d.display()))?,
            ),
            None => {
                tracing::warn!("ARENA_SECURITY_DIR not set: challenge governance policy checks are skipped (signature checks still apply)");
                None
            }
        };
        if governance_keys.is_empty() {
            match env {
                Env::Production => {
                    return Err("governance public keys are required (ARENA_GOVERNANCE_PUBKEYS or ARENA_GOVERNANCE_PUBKEY_FILE)".into())
                }
                Env::Dev => {
                    std::fs::create_dir_all(&self.object_store_dir).map_err(|e| e.to_string())?;
                    governance_keys.push(dev_governance_key(&self.object_store_dir)?);
                }
            }
        }
        Ok(Resolved {
            env,
            bind,
            worker_bind,
            signer,
            governance_keys,
            dev_only_keys,
            governed,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bind_parsing_rejects_hostnames() {
        assert!(parse_bind("127.0.0.1:8471").unwrap().ip().is_loopback());
        assert!(parse_bind("[::1]:8471").unwrap().ip().is_loopback());
        assert!(parse_bind("localhost:8471").unwrap().ip().is_loopback());
        assert!(parse_bind("127.evil.com:8471").is_err());
        assert!(parse_bind("localhost.evil:8471").is_err());
        assert!(parse_bind("127.0.0.999:8471").is_err());
        assert!(parse_bind("0.0.0.0").is_err());
    }
    #[test]
    fn non_loopback_requires_hardened_config() {
        let any = parse_bind("0.0.0.0:8471").unwrap();
        let lo = parse_bind("127.0.0.1:8471").unwrap();
        assert!(check_binds(Env::Dev, &[("public API", lo)], None).is_ok());
        assert!(check_binds(Env::Dev, &[("public API", any)], None).is_err());
        let weak = HardenedConfig {
            allow_non_loopback_bind: true,
            justification: " ".into(),
            behind_tls_proxy: false,
        };
        assert!(check_binds(Env::Dev, &[("public API", any)], Some(&weak)).is_err());
        let ok = HardenedConfig {
            justification: "container netns".into(),
            ..weak.clone()
        };
        assert!(check_binds(Env::Dev, &[("public API", any)], Some(&ok)).is_ok());
        assert!(check_binds(Env::Production, &[("public API", any)], Some(&ok)).is_err());
        assert!(check_binds(Env::Production, &[("worker API", any)], Some(&ok)).is_ok());
        let tls = HardenedConfig {
            behind_tls_proxy: true,
            ..ok
        };
        assert!(check_binds(Env::Production, &[("public API", any)], Some(&tls)).is_ok());
    }
}

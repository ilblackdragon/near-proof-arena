//! Worker configuration: environment variables, optionally a TOML file
//! (`ARENA_WORKER_CONFIG`) with the same keys in lowercase without the
//! `ARENA_` prefix (`server_url`, `worker_token_file`, ...). Environment
//! wins over the file.
//!
//! The worker holds **only** a worker bearer token. It refuses to start if
//! database credentials are visible to it (env or config file).

use crate::jobs::JobKind;
use arena_sandbox::Mount;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Duration;

/// Environment variables that indicate database credentials.
pub const FORBIDDEN_ENV: &[&str] = &[
    "DATABASE_URL",
    "ARENA_DATABASE_URL",
    "ARENA_DB_URL",
    "PGPASSWORD",
    "PGPASSFILE",
    "PGUSER",
    "PGHOST",
    "PGDATABASE",
    "PGSERVICE",
    "PGSERVICEFILE",
];

#[derive(Clone, Debug)]
pub struct WorkerConfig {
    pub server_url: String,
    pub token: String,
    pub worker_id: String,
    pub work_dir: PathBuf,
    pub backend: String,
    pub kinds: Vec<JobKind>,
    pub poll_interval: Duration,
    pub heartbeat_interval: Duration,
    pub build_mounts: Vec<Mount>,
    pub build_path: Option<String>,
    pub build_env: Vec<(String, String)>,
    pub images_dir: Option<PathBuf>,
    /// Pinned build toolchain image (TreeDigest).
    pub toolchain_image: Option<arena_types::Digest>,
    pub bench_cpus: Option<Vec<u32>>,
    pub keep_workdirs: bool,
    /// Directories holding public fixtures, matched to challenges by TreeDigest.
    pub fixtures_dirs: Vec<PathBuf>,
    /// DEV ONLY: cap on benchmark batch sizes (recorded in results).
    pub bench_batch_cap: Option<u32>,
    /// Judge-sampled conformance cases per job.
    pub conformance_samples: usize,
    /// Clean checkout with the trusted Lean packages (enables FORMAL_CHECK).
    pub formal_repo: Option<PathBuf>,
    /// `arena-formal-challenge-v1` configs (default `<repo>/runners/formal-checker/challenges`).
    pub formal_configs_dir: Option<PathBuf>,
    /// Installed lean-checker images (firecracker).
    pub lean_checker_images: Option<PathBuf>,
    /// Judge `npai-verify` (default: next to the worker binary, if present).
    pub npai_verify: Option<PathBuf>,
    /// Lean reference interpreter for npai shadow checks.
    pub interp_ref: Option<PathBuf>,
    /// `near-arena-oracle` binary + workload generator specs dir (NEAR oracle).
    pub near_oracle: Option<PathBuf>,
    pub workload_generators: Option<PathBuf>,
    pub lease_seconds: u32,
}

#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("refusing to start: database credentials visible to the worker ({0}); workers hold a worker token only")]
    DbCredentials(String),
    #[error("missing config: {0}")]
    Missing(&'static str),
    #[error("invalid config {0}: {1}")]
    Invalid(&'static str, String),
}

/// Source of key/value settings (env + file), injectable for tests.
pub struct Settings {
    env: BTreeMap<String, String>,
    file: BTreeMap<String, String>,
}

impl Settings {
    pub fn from_process() -> Result<Self, ConfigError> {
        let env: BTreeMap<String, String> = std::env::vars().collect();
        let file = match env.get("ARENA_WORKER_CONFIG") {
            Some(p) => {
                let text = std::fs::read_to_string(p)
                    .map_err(|e| ConfigError::Invalid("ARENA_WORKER_CONFIG", e.to_string()))?;
                parse_file(&text)?
            }
            None => BTreeMap::new(),
        };
        Ok(Settings { env, file })
    }

    pub fn new(
        env: BTreeMap<String, String>,
        file_toml: Option<&str>,
    ) -> Result<Self, ConfigError> {
        Ok(Settings {
            env,
            file: file_toml.map(parse_file).transpose()?.unwrap_or_default(),
        })
    }

    fn get(&self, key: &str) -> Option<String> {
        if let Some(v) = self.env.get(key) {
            return Some(v.clone());
        }
        let fk = key.trim_start_matches("ARENA_").to_ascii_lowercase();
        self.file.get(&fk).cloned()
    }
}

fn parse_file(text: &str) -> Result<BTreeMap<String, String>, ConfigError> {
    let v: toml::Table =
        toml::from_str(text).map_err(|e| ConfigError::Invalid("config file", e.to_string()))?;
    let mut out = BTreeMap::new();
    for (k, v) in v {
        let s = match v {
            toml::Value::String(s) => s,
            toml::Value::Integer(i) => i.to_string(),
            toml::Value::Boolean(b) => b.to_string(),
            other => {
                return Err(ConfigError::Invalid(
                    "config file",
                    format!("{k}: unsupported value {other}"),
                ))
            }
        };
        out.insert(k, s);
    }
    Ok(out)
}

fn looks_like_db_url(v: &str) -> bool {
    let l = v.to_ascii_lowercase();
    l.starts_with("postgres://") || l.starts_with("postgresql://") || l.contains("password=")
}

impl WorkerConfig {
    pub fn load(s: &Settings) -> Result<Self, ConfigError> {
        for k in FORBIDDEN_ENV {
            if s.env.contains_key(*k) {
                return Err(ConfigError::DbCredentials(format!("env {k}")));
            }
        }
        for (k, v) in s
            .env
            .iter()
            .filter(|(k, _)| k.starts_with("ARENA_"))
            .chain(s.file.iter())
        {
            if looks_like_db_url(v) || k.to_ascii_lowercase().contains("database") {
                return Err(ConfigError::DbCredentials(k.clone()));
            }
        }
        let server_url = s
            .get("ARENA_SERVER_URL")
            .ok_or(ConfigError::Missing("ARENA_SERVER_URL"))?;
        let token = match (
            s.get("ARENA_WORKER_TOKEN"),
            s.get("ARENA_WORKER_TOKEN_FILE"),
        ) {
            (Some(t), _) => t,
            (None, Some(f)) => std::fs::read_to_string(&f)
                .map_err(|e| ConfigError::Invalid("ARENA_WORKER_TOKEN_FILE", e.to_string()))?
                .trim()
                .to_string(),
            (None, None) => {
                return Err(ConfigError::Missing(
                    "ARENA_WORKER_TOKEN or ARENA_WORKER_TOKEN_FILE",
                ))
            }
        };
        if token.is_empty() {
            return Err(ConfigError::Missing("worker token is empty"));
        }
        let worker_id = s
            .get("ARENA_WORKER_ID")
            .unwrap_or_else(|| format!("{}-{}", hostname(), std::process::id()));
        // Explicit kinds win; otherwise worker classes (deploy/hardened
        // systemd `arena-worker@<class>`, compose ARENA_WORKER_CLASSES).
        let class_kinds = match s.get("ARENA_WORKER_CLASSES").or_else(|| s.get("ARENA_WORKER_CLASS")) {
            None => None,
            Some(v) => {
                let mut out: Vec<JobKind> = vec![];
                for c in v.split(',').map(str::trim).filter(|c| !c.is_empty()) {
                    let ks: &[JobKind] = match c {
                        "build" => &[JobKind::Validate, JobKind::Build],
                        "formal" => &[JobKind::FormalCheck],
                        "oracle" | "exec" | "conformance" => &[JobKind::Conformance, JobKind::Adversarial],
                        "bench" | "gpu" => &[JobKind::Benchmark],
                        "all" => &JobKind::ALL,
                        other => return Err(ConfigError::Invalid("ARENA_WORKER_CLASS", other.to_string())),
                    };
                    for k in ks {
                        if !out.contains(k) {
                            out.push(*k);
                        }
                    }
                }
                Some(out)
            }
        };
        let kinds = match s.get("ARENA_WORKER_KINDS") {
            None => class_kinds.unwrap_or_else(|| JobKind::ALL.to_vec()),
            Some(v) => v
                .split(',')
                .map(|k| {
                    k.trim()
                        .to_ascii_uppercase()
                        .parse::<JobKind>()
                        .map_err(|_| ConfigError::Invalid("ARENA_WORKER_KINDS", k.to_string()))
                })
                .collect::<Result<_, _>>()?,
        };
        let build_mounts = match s.get("ARENA_BUILD_MOUNTS") {
            None => vec![],
            Some(v) => v
                .split(',')
                .filter(|x| !x.trim().is_empty())
                .map(|m| {
                    let (h, g) = m
                        .split_once(':')
                        .ok_or_else(|| ConfigError::Invalid("ARENA_BUILD_MOUNTS", m.to_string()))?;
                    Ok(Mount {
                        host: PathBuf::from(h.trim()),
                        guest: g.trim().to_string(),
                    })
                })
                .collect::<Result<_, ConfigError>>()?,
        };
        let build_env = match s.get("ARENA_BUILD_ENV") {
            None => vec![],
            Some(v) => v
                .split(',')
                .filter(|x| !x.trim().is_empty())
                .map(|kv| {
                    let (k, val) = kv
                        .split_once('=')
                        .ok_or_else(|| ConfigError::Invalid("ARENA_BUILD_ENV", kv.to_string()))?;
                    if !arena_sandbox::ENV_ALLOWLIST.contains(&k.trim()) {
                        return Err(ConfigError::Invalid(
                            "ARENA_BUILD_ENV",
                            format!("{k} not in sandbox env allowlist"),
                        ));
                    }
                    Ok((k.trim().to_string(), val.to_string()))
                })
                .collect::<Result<_, ConfigError>>()?,
        };
        let bench_cpus = match s.get("ARENA_BENCH_CPUS") {
            None => None,
            Some(v) => Some(
                v.split(',')
                    .map(|c| {
                        c.trim()
                            .parse::<u32>()
                            .map_err(|e| ConfigError::Invalid("ARENA_BENCH_CPUS", e.to_string()))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        };
        let ms = |key: &'static str, default: u64| -> Result<Duration, ConfigError> {
            Ok(Duration::from_millis(match s.get(key) {
                Some(v) => v.parse().map_err(|e: std::num::ParseIntError| {
                    ConfigError::Invalid(key, e.to_string())
                })?,
                None => default,
            }))
        };
        Ok(WorkerConfig {
            server_url,
            token,
            worker_id,
            work_dir: PathBuf::from(
                s.get("ARENA_WORK_DIR")
                    .unwrap_or_else(|| "/var/tmp/arena-worker".into()),
            ),
            // `ARENA_SANDBOX` is the name deploy/ and arena-guard use.
            backend: s
                .get("ARENA_SANDBOX_BACKEND")
                .or_else(|| s.get("ARENA_SANDBOX"))
                .unwrap_or_else(|| "bwrap-dev".into()),
            kinds,
            poll_interval: ms("ARENA_POLL_MS", 2000)?,
            heartbeat_interval: ms("ARENA_HEARTBEAT_MS", 10_000)?,
            build_mounts,
            build_path: s.get("ARENA_BUILD_PATH"),
            build_env,
            images_dir: s.get("ARENA_IMAGES_DIR").map(PathBuf::from),
            toolchain_image: match s.get("ARENA_BUILD_TOOLCHAIN_IMAGE") {
                None => None,
                Some(v) => Some(
                    arena_types::Digest::try_from(v)
                        .map_err(|e| ConfigError::Invalid("ARENA_BUILD_TOOLCHAIN_IMAGE", e))?,
                ),
            },
            bench_cpus,
            keep_workdirs: s.get("ARENA_KEEP_WORKDIRS").as_deref() == Some("1"),
            fixtures_dirs: s
                .get("ARENA_FIXTURES_DIRS")
                .map(|v| {
                    v.split(',')
                        .filter(|x| !x.trim().is_empty())
                        .map(|x| PathBuf::from(x.trim()))
                        .collect()
                })
                .unwrap_or_default(),
            bench_batch_cap: match s.get("ARENA_DEV_BENCH_BATCH_CAP") {
                None => None,
                Some(v) => Some(v.parse().map_err(|e: std::num::ParseIntError| {
                    ConfigError::Invalid("ARENA_DEV_BENCH_BATCH_CAP", e.to_string())
                })?),
            },
            conformance_samples: match s.get("ARENA_CONFORMANCE_SAMPLES") {
                None => 8,
                Some(v) => v.parse().map_err(|e: std::num::ParseIntError| {
                    ConfigError::Invalid("ARENA_CONFORMANCE_SAMPLES", e.to_string())
                })?,
            },
            formal_repo: s.get("ARENA_FORMAL_REPO").map(PathBuf::from),
            formal_configs_dir: s.get("ARENA_FORMAL_CONFIGS_DIR").map(PathBuf::from),
            lean_checker_images: s.get("ARENA_LEAN_CHECKER_IMAGES").map(PathBuf::from),
            npai_verify: s.get("ARENA_NPAI_VERIFY").map(PathBuf::from).or_else(|| {
                let p = std::env::current_exe().ok()?.with_file_name("npai-verify");
                p.is_file().then_some(p)
            }),
            interp_ref: s.get("ARENA_INTERP_REF").map(PathBuf::from),
            near_oracle: s.get("ARENA_NEAR_ORACLE").map(PathBuf::from),
            workload_generators: s.get("ARENA_WORKLOAD_GENERATORS").map(PathBuf::from),
            lease_seconds: match s.get("ARENA_LEASE_SECONDS") {
                None => 300,
                Some(v) => v.parse().map_err(|e: std::num::ParseIntError| {
                    ConfigError::Invalid("ARENA_LEASE_SECONDS", e.to_string())
                })?,
            },
        })
    }
}

fn hostname() -> String {
    std::fs::read_to_string("/proc/sys/kernel/hostname")
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|_| "worker".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn env(kv: &[(&str, &str)]) -> BTreeMap<String, String> {
        kv.iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }
    #[test]
    fn loads_minimal() {
        let s = Settings::new(
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
            ]),
            None,
        )
        .unwrap();
        let c = WorkerConfig::load(&s).unwrap();
        assert_eq!(c.kinds.len(), 6);
        assert_eq!(c.backend, "bwrap-dev");
    }
    #[test]
    fn file_and_env_precedence() {
        let s = Settings::new(
            env(&[("ARENA_WORKER_TOKEN", "t"), ("ARENA_WORKER_KINDS", "build,benchmark")]),
            Some("server_url = \"http://file\"\nworker_kinds = \"validate\"\nbuild_mounts = \"/opt/x:/opt/rust\"\n"),
        )
        .unwrap();
        let c = WorkerConfig::load(&s).unwrap();
        assert_eq!(c.server_url, "http://file");
        assert_eq!(c.kinds, vec![JobKind::Build, JobKind::Benchmark]);
        assert_eq!(c.build_mounts[0].guest, "/opt/rust");
    }
    #[test]
    fn refuses_db_credentials() {
        for bad in [
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("DATABASE_URL", "postgres://a:b@h/db"),
            ]),
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("PGPASSWORD", "x"),
            ]),
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("ARENA_EXTRA", "postgresql://u@h/db"),
            ]),
        ] {
            let s = Settings::new(bad, None).unwrap();
            assert!(matches!(
                WorkerConfig::load(&s),
                Err(ConfigError::DbCredentials(_))
            ));
        }
        let s = Settings::new(
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
            ]),
            Some("database_url = \"x\""),
        )
        .unwrap();
        assert!(matches!(
            WorkerConfig::load(&s),
            Err(ConfigError::DbCredentials(_))
        ));
    }
    #[test]
    fn classes_and_sandbox_alias() {
        let s = Settings::new(
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("ARENA_WORKER_CLASSES", "build,formal,oracle,bench"),
                ("ARENA_SANDBOX", "firecracker"),
            ]),
            None,
        )
        .unwrap();
        let c = WorkerConfig::load(&s).unwrap();
        assert_eq!(c.backend, "firecracker");
        assert_eq!(c.kinds.len(), 6);
        let s = Settings::new(env(&[("ARENA_SERVER_URL", "http://x"), ("ARENA_WORKER_TOKEN", "t"), ("ARENA_WORKER_CLASS", "bench")]), None).unwrap();
        assert_eq!(WorkerConfig::load(&s).unwrap().kinds, vec![JobKind::Benchmark]);
        let s = Settings::new(env(&[("ARENA_SERVER_URL", "http://x"), ("ARENA_WORKER_TOKEN", "t"), ("ARENA_WORKER_CLASS", "nope")]), None).unwrap();
        assert!(WorkerConfig::load(&s).is_err());
    }

    #[test]
    fn build_env_must_be_allowlisted() {
        let s = Settings::new(
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("ARENA_BUILD_ENV", "LD_PRELOAD=/x"),
            ]),
            None,
        )
        .unwrap();
        assert!(WorkerConfig::load(&s).is_err());
    }
}

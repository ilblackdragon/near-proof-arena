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
    /// Host CPUs for the candidate runs of BUILD, CONFORMANCE and ADVERSARIAL
    /// (`ARENA_RUN_CPUS`). On firecracker the VM gets one vCPU per listed CPU;
    /// unset means the backend default (firecracker: 1 vCPU).
    pub run_cpus: Option<Vec<u32>>,
    pub keep_workdirs: bool,
    /// Directories holding public fixtures, matched to challenges by TreeDigest.
    pub fixtures_dirs: Vec<PathBuf>,
    /// DEV ONLY: cap on benchmark batch sizes (recorded in results).
    pub bench_batch_cap: Option<u32>,
    /// Judge-sampled conformance cases per job.
    pub conformance_samples: usize,
    /// Legacy `ARENA_FORMAL_REPO` (a working checkout as the trusted base):
    /// refused at startup if set.
    pub formal_repo: Option<PathBuf>,
    /// Frozen trusted-tree store (`ARENA_TRUSTED_TREES`).
    pub trusted_trees: Option<PathBuf>,
    /// `arena-formal-challenge-v1` configs (enables FORMAL_CHECK).
    pub formal_configs_dir: Option<PathBuf>,
    /// Installed lean-checker images (firecracker).
    pub lean_checker_images: Option<PathBuf>,
    /// Judge `npai-verify` (default: next to the worker binary, if present).
    pub npai_verify: Option<PathBuf>,
    /// Lean reference interpreter for npai shadow checks.
    pub interp_ref: Option<PathBuf>,
    /// `near-arena-oracle` binary + workload generator specs dirs (NEAR
    /// oracles v1 and v2; `ARENA_WORKLOAD_GENERATORS`, comma-separated).
    pub near_oracle: Option<PathBuf>,
    /// `near-arena-claim-v3` oracle binaries by tool name
    /// (`crate::oracle::NEAR_V3_TOOLS`): `ARENA_NEAR_ORACLE_V3`
    /// (`near-arena-oracle-v3`, D0), `ARENA_NEAR_ORACLE_V3_D1`
    /// (`near-arena-oracle-v3-d1`, D1/D2), `ARENA_NEAR_ORACLE_V3_D3`
    /// (`near-arena-oracle-v3-d3`, D3α). Each generator spec in
    /// `ARENA_WORKLOAD_GENERATORS` names its tool; a challenge whose specs
    /// need a tool not configured here fails closed.
    pub near_oracle_v3: BTreeMap<String, PathBuf>,
    pub workload_generators: Vec<PathBuf>,
    /// Judge-only held-out set directories (`ARENA_HELDOUT_DIRS`), matched to
    /// `workload_suite.heldout_commitment` by TreeDigest. When set, committed
    /// held-out sets are mandatory on this worker (fail closed).
    pub heldout_dirs: Vec<PathBuf>,
    /// Judge-only season secret (`ARENA_SEASON_SECRET_FILE`, hex, mode 0600)
    /// keying workload sampling (BENCHMARK_SPEC §11.1), and the commitment
    /// governance published for it (`ARENA_SEASON_SECRET_COMMIT`, optional).
    pub season_secret_file: Option<PathBuf>,
    pub season_secret_commit: Option<String>,
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
        let class_kinds = match s
            .get("ARENA_WORKER_CLASSES")
            .or_else(|| s.get("ARENA_WORKER_CLASS"))
        {
            None => None,
            Some(v) => {
                let mut out: Vec<JobKind> = vec![];
                for c in v.split(',').map(str::trim).filter(|c| !c.is_empty()) {
                    let ks: &[JobKind] = match c {
                        "build" => &[JobKind::Validate, JobKind::Build],
                        "formal" => &[JobKind::FormalCheck],
                        "oracle" | "exec" | "conformance" => {
                            &[JobKind::Conformance, JobKind::Adversarial]
                        }
                        "bench" | "gpu" => &[JobKind::Benchmark],
                        "all" => &JobKind::ALL,
                        other => {
                            return Err(ConfigError::Invalid(
                                "ARENA_WORKER_CLASS",
                                other.to_string(),
                            ))
                        }
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
            Some(v) => {
                Some(parse_cpu_list(&v).map_err(|e| ConfigError::Invalid("ARENA_BENCH_CPUS", e))?)
            }
        };
        let run_cpus = match s.get("ARENA_RUN_CPUS") {
            None => None,
            Some(v) => {
                Some(parse_cpu_list(&v).map_err(|e| ConfigError::Invalid("ARENA_RUN_CPUS", e))?)
            }
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
            run_cpus,
            keep_workdirs: s.get("ARENA_KEEP_WORKDIRS").as_deref() == Some("1"),
            fixtures_dirs: dir_list(s.get("ARENA_FIXTURES_DIRS")),
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
            trusted_trees: s.get("ARENA_TRUSTED_TREES").map(PathBuf::from),
            formal_configs_dir: s.get("ARENA_FORMAL_CONFIGS_DIR").map(PathBuf::from),
            lean_checker_images: s.get("ARENA_LEAN_CHECKER_IMAGES").map(PathBuf::from),
            npai_verify: s.get("ARENA_NPAI_VERIFY").map(PathBuf::from).or_else(|| {
                let p = std::env::current_exe().ok()?.with_file_name("npai-verify");
                p.is_file().then_some(p)
            }),
            interp_ref: s.get("ARENA_INTERP_REF").map(PathBuf::from),
            near_oracle: s.get("ARENA_NEAR_ORACLE").map(PathBuf::from),
            near_oracle_v3: crate::oracle::NEAR_V3_TOOLS
                .iter()
                .filter_map(|t| s.get(t.env).map(|p| (t.name.to_string(), PathBuf::from(p))))
                .collect(),
            workload_generators: dir_list(s.get("ARENA_WORKLOAD_GENERATORS")),
            heldout_dirs: dir_list(s.get("ARENA_HELDOUT_DIRS")),
            season_secret_file: s.get("ARENA_SEASON_SECRET_FILE").map(PathBuf::from),
            season_secret_commit: s.get("ARENA_SEASON_SECRET_COMMIT"),
            lease_seconds: match s.get("ARENA_LEASE_SECONDS") {
                None => 300,
                Some(v) => v.parse().map_err(|e: std::num::ParseIntError| {
                    ConfigError::Invalid("ARENA_LEASE_SECONDS", e.to_string())
                })?,
            },
        })
    }
}

/// A comma-separated directory list (empty entries ignored).
fn dir_list(v: Option<String>) -> Vec<PathBuf> {
    v.map(|v| {
        v.split(',')
            .filter(|x| !x.trim().is_empty())
            .map(|x| PathBuf::from(x.trim()))
            .collect()
    })
    .unwrap_or_default()
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
    fn near_v3_oracle_binaries_by_tool() {
        let base = [
            ("ARENA_SERVER_URL", "http://x"),
            ("ARENA_WORKER_TOKEN", "t"),
        ];
        let c = WorkerConfig::load(&Settings::new(env(&base), None).unwrap()).unwrap();
        assert!(c.near_oracle_v3.is_empty());
        let mut kv = base.to_vec();
        kv.push(("ARENA_NEAR_ORACLE_V3", "/b/near-arena-oracle-v3"));
        let c = WorkerConfig::load(&Settings::new(env(&kv), None).unwrap()).unwrap();
        assert_eq!(
            c.near_oracle_v3,
            BTreeMap::from([(
                "near-arena-oracle-v3".to_string(),
                PathBuf::from("/b/near-arena-oracle-v3")
            )])
        );
        kv.push(("ARENA_NEAR_ORACLE_V3_D1", "/b/d1"));
        kv.push(("ARENA_NEAR_ORACLE_V3_D3", "/b/d3"));
        let c = WorkerConfig::load(&Settings::new(env(&kv), None).unwrap()).unwrap();
        assert_eq!(
            c.near_oracle_v3["near-arena-oracle-v3-d1"],
            PathBuf::from("/b/d1")
        );
        assert_eq!(
            c.near_oracle_v3["near-arena-oracle-v3-d3"],
            PathBuf::from("/b/d3")
        );
        assert_eq!(c.near_oracle_v3.len(), 3);
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
        let s = Settings::new(
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("ARENA_WORKER_CLASS", "bench"),
            ]),
            None,
        )
        .unwrap();
        assert_eq!(
            WorkerConfig::load(&s).unwrap().kinds,
            vec![JobKind::Benchmark]
        );
        let s = Settings::new(
            env(&[
                ("ARENA_SERVER_URL", "http://x"),
                ("ARENA_WORKER_TOKEN", "t"),
                ("ARENA_WORKER_CLASS", "nope"),
            ]),
            None,
        )
        .unwrap();
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

/// `"8-15,24,26"` -> `[8..=15, 24, 26]` (comma-separated CPU ids and
/// inclusive ranges, as in cgroup `cpuset` / systemd `AllowedCPUs=`).
pub fn parse_cpu_list(v: &str) -> Result<Vec<u32>, String> {
    let mut out = vec![];
    for part in v.split(',').map(str::trim).filter(|p| !p.is_empty()) {
        let num = |x: &str| x.trim().parse::<u32>().map_err(|e| format!("{x:?}: {e}"));
        match part.split_once('-') {
            Some((a, b)) => {
                let (a, b) = (num(a)?, num(b)?);
                if a > b || b - a > 4096 {
                    return Err(format!("bad cpu range {part:?}"));
                }
                out.extend(a..=b);
            }
            None => out.push(num(part)?),
        }
    }
    if out.is_empty() {
        return Err("empty cpu list".into());
    }
    Ok(out)
}

#[cfg(test)]
mod cpu_list_tests {
    use super::parse_cpu_list;
    #[test]
    fn ranges_and_singles() {
        assert_eq!(
            parse_cpu_list("8-11, 24,26").unwrap(),
            vec![8, 9, 10, 11, 24, 26]
        );
        assert_eq!(parse_cpu_list("3").unwrap(), vec![3]);
        assert!(parse_cpu_list("").is_err());
        assert!(parse_cpu_list("5-2").is_err());
        assert!(parse_cpu_list("x").is_err());
    }
}

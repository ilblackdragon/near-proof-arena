//! Client configuration: `ARENA_URL`, `ARENA_TOKEN`, or
//! `~/.config/arena/config.toml` (`$XDG_CONFIG_HOME/arena/config.toml`;
//! `ARENA_CONFIG` overrides the path). Environment wins over the file.
//!
//! ```toml
//! url = "https://arena.example.org"
//! token = "agt_..."
//! ```

use crate::exit::{CliError, CliResult, Exit};
use serde::Deserialize;
use std::path::PathBuf;

pub const DEFAULT_URL: &str = "http://127.0.0.1:8471";

#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct FileConfig {
    url: Option<String>,
    token: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub url: String,
    pub token: Option<String>,
}

fn config_path() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("ARENA_CONFIG") {
        return Some(PathBuf::from(p));
    }
    if let Some(x) = std::env::var_os("XDG_CONFIG_HOME").filter(|x| !x.is_empty()) {
        return Some(PathBuf::from(x).join("arena/config.toml"));
    }
    std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".config/arena/config.toml"))
}

impl Config {
    pub fn load() -> CliResult<Config> {
        let file = match config_path() {
            Some(p) if p.exists() => {
                let s = std::fs::read_to_string(&p)?;
                toml::from_str::<FileConfig>(&s).map_err(|e| {
                    CliError::new(
                        Exit::Auth,
                        format!("invalid config file {}: {e}", p.display()),
                    )
                })?
            }
            _ => FileConfig::default(),
        };
        let env = |k: &str| std::env::var(k).ok().filter(|v| !v.is_empty());
        let url = env("ARENA_URL")
            .or(file.url)
            .unwrap_or_else(|| DEFAULT_URL.to_string());
        let token = env("ARENA_TOKEN").or(file.token);
        Ok(Config {
            url: url.trim_end_matches('/').to_string(),
            token,
        })
    }

    pub fn require_token(&self) -> CliResult<&str> {
        self.token.as_deref().ok_or_else(|| {
            CliError::new(
                Exit::Auth,
                "no agent token: set ARENA_TOKEN or `token` in ~/.config/arena/config.toml",
            )
        })
    }
}

//! Running candidate executables locally with a wall-clock timeout, a cleared
//! environment, and (when the kernel allows unprivileged user namespaces) no
//! network. This approximates — but is NOT — the judge sandbox.

use std::io::Read;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

pub const OUTPUT_TRUNC: usize = 64 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExitKind {
    Exited(i32),
    Signaled(i32),
    TimedOut,
    SpawnFailed(String),
}

#[derive(Debug, Clone)]
pub struct Outcome {
    pub exit: ExitKind,
    pub wall: Duration,
    pub stdout: String,
    pub stderr: String,
}

impl Outcome {
    pub fn code(&self) -> Option<i32> {
        match self.exit {
            ExitKind::Exited(c) => Some(c),
            _ => None,
        }
    }
    pub fn describe(&self) -> String {
        match &self.exit {
            ExitKind::Exited(c) => format!("exit {c}"),
            ExitKind::Signaled(s) => format!("killed by signal {s}"),
            ExitKind::TimedOut => "timed out".into(),
            ExitKind::SpawnFailed(e) => format!("could not start: {e}"),
        }
    }
    /// Last few lines of stderr (or stdout) for diagnostics.
    pub fn tail(&self) -> String {
        let src = if self.stderr.trim().is_empty() {
            &self.stdout
        } else {
            &self.stderr
        };
        let lines: Vec<&str> = src.lines().collect();
        let start = lines.len().saturating_sub(12);
        lines[start..].join("\n")
    }
}

#[derive(Clone, Debug)]
pub struct Runner {
    /// Prefix argv used to drop network access (`unshare -r -n --`), if available.
    pub netns_prefix: Option<Vec<String>>,
    pub base_env: Vec<(String, String)>,
}

impl Runner {
    pub fn detect(allow_network: bool) -> Runner {
        let netns_prefix = if allow_network {
            None
        } else {
            let ok = Command::new("unshare")
                .args(["-r", "-n", "--", "true"])
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
            ok.then(|| vec!["unshare".into(), "-r".into(), "-n".into(), "--".into()])
        };
        let mut base_env = vec![
            (
                "PATH".to_string(),
                std::env::var("PATH").unwrap_or_else(|_| "/usr/bin:/bin".into()),
            ),
            ("LANG".into(), "C.UTF-8".into()),
            ("LC_ALL".into(), "C.UTF-8".into()),
            ("TZ".into(), "UTC".into()),
            ("SOURCE_DATE_EPOCH".into(), "0".into()),
        ];
        // Let rustup / elan proxies find their installed toolchains; the judge
        // image ships its own pinned toolchains instead.
        let home = std::env::var("HOME").unwrap_or_default();
        for (k, default) in [("RUSTUP_HOME", ".rustup"), ("ELAN_HOME", ".elan")] {
            let v = std::env::var(k).ok().or_else(|| {
                let p = Path::new(&home).join(default);
                p.exists().then(|| p.to_string_lossy().into_owned())
            });
            if let Some(v) = v {
                base_env.push((k.to_string(), v));
            }
        }
        if let Ok(v) = std::env::var("RUSTUP_TOOLCHAIN") {
            base_env.push(("RUSTUP_TOOLCHAIN".into(), v));
        }
        Runner {
            netns_prefix,
            base_env,
        }
    }

    pub fn network_isolated(&self) -> bool {
        self.netns_prefix.is_some()
    }

    /// Run `argv` in `cwd` with a fresh `HOME` (= `home`) and a timeout.
    pub fn run(
        &self,
        argv: &[String],
        cwd: &Path,
        home: &Path,
        extra_env: &[(&str, String)],
        timeout: Duration,
    ) -> Outcome {
        let mut full: Vec<String> = self.netns_prefix.clone().unwrap_or_default();
        full.extend(argv.iter().cloned());
        let mut cmd = Command::new(&full[0]);
        cmd.args(&full[1..])
            .current_dir(cwd)
            .env_clear()
            .envs(self.base_env.iter().map(|(k, v)| (k.as_str(), v.as_str())))
            .env("HOME", home)
            .env("TMPDIR", home)
            .envs(extra_env.iter().map(|(k, v)| (*k, v.as_str())))
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .process_group(0);
        let start = Instant::now();
        let mut child = match cmd.spawn() {
            Ok(c) => c,
            Err(e) => {
                return Outcome {
                    exit: ExitKind::SpawnFailed(e.to_string()),
                    wall: start.elapsed(),
                    stdout: String::new(),
                    stderr: String::new(),
                }
            }
        };
        let pid = child.id();
        let out_h = drain(child.stdout.take());
        let err_h = drain(child.stderr.take());
        let mut timed_out = false;
        let status = loop {
            match child.try_wait() {
                Ok(Some(s)) => break Some(s),
                Ok(None) => {}
                Err(_) => break None,
            }
            if start.elapsed() > timeout {
                timed_out = true;
                kill_group(pid);
                break child.wait().ok();
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        let wall = start.elapsed();
        // Kill stragglers left in the process group so pipes close.
        kill_group(pid);
        let stdout = out_h.join().unwrap_or_default();
        let stderr = err_h.join().unwrap_or_default();
        let exit = if timed_out {
            ExitKind::TimedOut
        } else {
            match status {
                Some(s) => match (s.code(), s.signal()) {
                    (Some(c), _) => ExitKind::Exited(c),
                    (None, Some(sig)) => ExitKind::Signaled(sig),
                    _ => ExitKind::Signaled(0),
                },
                None => ExitKind::SpawnFailed("wait failed".into()),
            }
        };
        Outcome {
            exit,
            wall,
            stdout,
            stderr,
        }
    }
}

fn drain<R: Read + Send + 'static>(r: Option<R>) -> std::thread::JoinHandle<String> {
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(mut r) = r {
            let mut chunk = [0u8; 8192];
            while let Ok(n) = r.read(&mut chunk) {
                if n == 0 {
                    break;
                }
                if buf.len() < OUTPUT_TRUNC {
                    let take = n.min(OUTPUT_TRUNC - buf.len());
                    buf.extend_from_slice(&chunk[..take]);
                }
            }
        }
        String::from_utf8_lossy(&buf).into_owned()
    })
}

fn kill_group(pid: u32) {
    let _ = Command::new("kill")
        .args(["-KILL", "--", &format!("-{pid}")])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn timeout_and_exit_codes() {
        let r = Runner::detect(true);
        let d = tempfile::tempdir().unwrap();
        let o = r.run(
            &["sh".into(), "-c".into(), "exit 7".into()],
            d.path(),
            d.path(),
            &[],
            Duration::from_secs(10),
        );
        assert_eq!(o.exit, ExitKind::Exited(7));
        let o = r.run(
            &["sh".into(), "-c".into(), "sleep 30".into()],
            d.path(),
            d.path(),
            &[],
            Duration::from_millis(200),
        );
        assert_eq!(o.exit, ExitKind::TimedOut);
        assert!(o.wall < Duration::from_secs(10));
        let o = r.run(
            &["sh".into(), "-c".into(), "echo $FOO$HOME".into()],
            d.path(),
            d.path(),
            &[],
            Duration::from_secs(10),
        );
        assert_eq!(o.stdout.trim(), d.path().to_str().unwrap());
    }
}

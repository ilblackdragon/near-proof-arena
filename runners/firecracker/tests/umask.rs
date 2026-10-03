//! Image content must not depend on the host's umask or file owner.
//!
//! Runs in its own test binary because it sets the process umask to 0077
//! (as on the live deploy where a 0600 `build.sh` produced an image the guest
//! could not read, and the cache, keyed by TreeDigest, kept serving it).
//! The VM part is gated by `ARENA_FC_TESTS=1`.

use arena_firecracker::images::{self, TreeLimits};
use arena_firecracker::*;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

fn deps() -> PathBuf {
    std::env::var_os("ARENA_FC_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/data/illia/nearproof-deps/firecracker"))
}

/// A tree as written under umask 0077: dirs 0700, files 0600/0700.
fn hostile_modes_tree(root: &Path) {
    fs::create_dir_all(root.join("sub/deeper")).unwrap();
    fs::write(root.join("data.txt"), "data").unwrap();
    fs::write(root.join("sub/deeper/notes"), "deep").unwrap();
    fs::write(root.join("build.sh"), "#!/bin/sh\necho built\n").unwrap();
    for (p, m) in [
        ("data.txt", 0o600),
        ("sub/deeper/notes", 0o600),
        ("build.sh", 0o700),
    ] {
        fs::set_permissions(root.join(p), fs::Permissions::from_mode(m)).unwrap();
    }
    for d in ["sub/deeper", "sub", ""] {
        fs::set_permissions(root.join(d), fs::Permissions::from_mode(0o700)).unwrap();
    }
}

fn debugfs_stat(image: &Path, path: &str) -> String {
    let o = Command::new("debugfs")
        .args(["-R", &format!("stat \"{path}\"")])
        .arg(image)
        .output()
        .unwrap();
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn mode_owner(stat: &str) -> (String, String, String) {
    let field = |k: &str| {
        let i = stat.find(k).unwrap_or_else(|| panic!("{k} not in {stat}")) + k.len();
        stat[i..].split_whitespace().next().unwrap().to_string()
    };
    (field("Mode:"), field("User:"), field("Group:"))
}

#[test]
fn umask_0077_trees_give_normalized_images_and_readable_guests() {
    unsafe { libc::umask(0o077) };
    let base = deps().join("work-tests");
    fs::create_dir_all(&base).unwrap();
    let t = tempfile::tempdir_in(&base).unwrap();
    let src = t.path().join("src");
    hostile_modes_tree(&src);

    // 1. staged + imaged content is normalized: dirs 0755, files 0644/0755,
    //    every inode root:root
    let st = images::stage_tree(&src, &t.path().join("stage"), &TreeLimits::default()).unwrap();
    let img = t.path().join("x.ext4");
    images::build_ro_image(&st, &img).unwrap();
    for (p, want) in [
        ("/", "0755"),
        ("/sub", "0755"),
        ("/sub/deeper", "0755"),
        ("/data.txt", "0644"),
        ("/sub/deeper/notes", "0644"),
        ("/build.sh", "0755"),
    ] {
        let (mode, uid, gid) = mode_owner(&debugfs_stat(&img, p));
        assert_eq!(
            (mode.as_str(), uid.as_str(), gid.as_str()),
            (want, "0", "0"),
            "{p}"
        );
    }
    // same TreeDigest from a tree with ordinary modes => identical image bytes
    let src2 = t.path().join("src2");
    hostile_modes_tree(&src2);
    for (p, m) in [
        ("data.txt", 0o644),
        ("sub/deeper/notes", 0o664),
        ("build.sh", 0o775),
        ("sub", 0o775),
    ] {
        fs::set_permissions(src2.join(p), fs::Permissions::from_mode(m)).unwrap();
    }
    let st2 = images::stage_tree(&src2, &t.path().join("stage2"), &TreeLimits::default()).unwrap();
    assert_eq!(st.digest, st2.digest);
    let img2 = t.path().join("y.ext4");
    images::build_ro_image(&st2, &img2).unwrap();
    for p in ["/", "/sub", "/data.txt", "/build.sh", "/sub/deeper/notes"] {
        assert_eq!(
            mode_owner(&debugfs_stat(&img, p)),
            mode_owner(&debugfs_stat(&img2, p)),
            "{p}"
        );
    }

    // 2. the guest (uid 1000) can read, list and execute it
    if std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1") {
        eprintln!("VM part skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let cfg = FirecrackerConfig::from_deps_dir(&deps(), &base).unwrap();
    let sb = FirecrackerSandbox::new(cfg).unwrap();
    let mut req = RunRequest::new(
        sb.rootfs_digest().clone(),
        vec![
            "/bin/sh".into(),
            "-c".into(),
            "cat /in/pkg/data.txt /in/pkg/sub/deeper/notes; echo; ls /in/pkg/sub; /in/pkg/build.sh; \
             stat -c '%a %u' /in/pkg /in/pkg/data.txt /in/pkg/build.sh"
                .into(),
        ],
        t.path().join("out"),
    );
    req.ro_mounts = vec![RoMount {
        host_path: src.clone(),
        guest_path: "/in/pkg".into(),
    }];
    req.wall_timeout = Duration::from_secs(30);
    let o = sb.run_native(&req).unwrap();
    assert_eq!(
        o.exit,
        Exit::Exited(0),
        "{}",
        String::from_utf8_lossy(&o.stderr_trunc)
    );
    assert_eq!(
        String::from_utf8_lossy(&o.stdout_trunc),
        "datadeep\ndeeper\nbuilt\n755 0\n644 0\n755 0\n"
    );
}

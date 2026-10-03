//! Archive member path normalization and validation.

use unicode_normalization::UnicodeNormalization;

/// Maximum path length in bytes (CONTRACTS §3).
pub const MAX_PATH_BYTES: usize = 255;

/// Normalize a raw tar member path into the canonical relative form used by
/// the tree digest (`a/b/c`, no leading `./`, no trailing `/`).
///
/// Returns `Ok(None)` for the archive root itself (`.` or `./`), which some
/// tar producers emit and which carries no information.
pub fn normalize(raw: &[u8]) -> Result<Option<String>, String> {
    if raw.len() > MAX_PATH_BYTES + 2 {
        return Err(format!("path longer than {MAX_PATH_BYTES} bytes"));
    }
    let s = std::str::from_utf8(raw).map_err(|_| "path is not valid UTF-8".to_string())?;
    if s.starts_with('/') {
        return Err(format!("absolute path {s:?}"));
    }
    let mut p = s;
    if let Some(rest) = p.strip_prefix("./") {
        p = rest;
    }
    if p.is_empty() || p == "." {
        return Ok(None);
    }
    if let Some(rest) = p.strip_suffix('/') {
        p = rest;
    }
    check_relpath(p)?;
    Ok(Some(p.to_string()))
}

/// Validate an already-normalized relative path (used for archive members
/// and for on-disk trees).
pub fn check_relpath(p: &str) -> Result<(), String> {
    if p.is_empty() {
        return Err("empty path".into());
    }
    if p.len() > MAX_PATH_BYTES {
        return Err(format!("path longer than {MAX_PATH_BYTES} bytes"));
    }
    if p.starts_with('/') {
        return Err(format!("absolute path {p:?}"));
    }
    for c in p.chars() {
        if c.is_control() || c == '\\' {
            return Err(format!("forbidden character {c:?} in path {p:?}"));
        }
    }
    for comp in p.split('/') {
        match comp {
            "" => return Err(format!("empty path component in {p:?}")),
            "." | ".." => return Err(format!("dot component in {p:?}")),
            _ => {}
        }
    }
    Ok(())
}

/// Key under which two paths are considered colliding on case-insensitive
/// and/or normalizing filesystems (macOS, Windows): NFC + lowercase.
pub fn collision_key(p: &str) -> String {
    p.nfc().collect::<String>().to_lowercase()
}

/// All strict ancestors of `p` (`a/b/c` -> `a`, `a/b`).
pub fn ancestors(p: &str) -> impl Iterator<Item = &str> {
    p.match_indices('/').map(move |(i, _)| &p[..i])
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn normalizes() {
        assert_eq!(normalize(b"./a/b/").unwrap().as_deref(), Some("a/b"));
        assert_eq!(normalize(b"./").unwrap(), None);
        assert_eq!(normalize(b".").unwrap(), None);
        assert_eq!(normalize(b"a").unwrap().as_deref(), Some("a"));
    }
    #[test]
    fn rejects() {
        for bad in [
            &b"/etc/passwd"[..],
            b"../x",
            b"a/../../x",
            b"a//b",
            b"a/./b",
            b"./../x",
            b"a\\b",
            b"a\nb",
            b"\xff\xfe",
            b"a/\0b",
        ] {
            assert!(
                normalize(bad).is_err(),
                "{:?}",
                String::from_utf8_lossy(bad)
            );
        }
        assert!(normalize("a".repeat(256).as_bytes()).is_err());
        assert!(normalize("a".repeat(255).as_bytes()).is_ok());
    }
    #[test]
    fn collisions() {
        assert_eq!(collision_key("README.md"), collision_key("readme.MD"));
        // U+00E9 vs e + U+0301
        assert_eq!(collision_key("caf\u{e9}"), collision_key("cafe\u{301}"));
    }
    #[test]
    fn ancestors_ok() {
        assert_eq!(ancestors("a/b/c").collect::<Vec<_>>(), vec!["a", "a/b"]);
        assert_eq!(ancestors("a").count(), 0);
    }
}

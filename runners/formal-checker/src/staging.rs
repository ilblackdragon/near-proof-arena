//! Stage A preparation (trusted, static): validate the candidate `formal/`
//! tree, reject forbidden Lake features, take only `.lean` sources, compute
//! module names and a judge-owned build order. Nothing here executes or
//! elaborates candidate content.

use crate::findings::{Finding, Scope};
use arena_types::ReasonCode;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub const MAX_FILES: usize = 4096;
pub const MAX_FILE_BYTES: u64 = 8 << 20;
pub const MAX_TOTAL_BYTES: u64 = 64 << 20;

/// Lake configuration keys that are never acceptable in a candidate lakefile.
pub const FORBIDDEN_LAKE_KEYS: &[&str] = &[
    "extern_lib",
    "externLib",
    "script",
    "target",
    "lean_exe",
    "moreLeanArgs",
    "weakLeanArgs",
    "moreServerArgs",
    "moreServerOptions",
    "moreGlobalServerArgs",
    "plugins",
    "dynlibs",
    "precompileModules",
    "moreLinkArgs",
    "moreLinkObjs",
    "moreLinkLibs",
    "weakLinkArgs",
    "nativeFacets",
    "input_file",
    "input_dir",
    "post_update",
];

/// Tokens that make a `lakefile.lean` unacceptable (it is never executed; we
/// only refuse configurations that ask for native code or build-time code).
const FORBIDDEN_LAKEFILE_LEAN_TOKENS: &[&str] = &[
    "extern_lib",
    "script",
    "target",
    "lean_exe",
    "moreLeanArgs",
    "weakLeanArgs",
    "moreServerArgs",
    "moreServerOptions",
    "moreGlobalServerArgs",
    "plugins",
    "dynlibs",
    "precompileModules",
    "moreLinkArgs",
    "moreLinkObjs",
    "moreLinkLibs",
    "weakLinkArgs",
    "nativeFacets",
    "input_file",
    "input_dir",
    "post_update",
    "run_cmd",
    "#eval",
    "initialize",
    "builtin_initialize",
    "unsafe",
    "elab",
    "macro",
    "syntax",
    "IO",
    "meta",
];

const ALLOWED_TOML_TOP: &[&str] = &[
    "name",
    "version",
    "defaultTargets",
    "testDriver",
    "lintDriver",
    "description",
    "keywords",
    "license",
    "licenseFiles",
    "readmeFile",
    "homepage",
    "reservoir",
    "leanOptions",
    "lean_lib",
    "require",
    "srcDir",
    "buildDir",
    "leanLibDir",
    "packagesDir",
    "versionTags",
];
const ALLOWED_TOML_LIB: &[&str] = &[
    "name",
    "roots",
    "globs",
    "srcDir",
    "leanOptions",
    "defaultFacets",
    "libName",
];
const ALLOWED_TOML_REQUIRE: &[&str] = &[
    "name", "scope", "git", "rev", "path", "version", "source", "subDir",
];
/// leanOptions a candidate may *declare* (we never apply candidate options anyway).
const ALLOWED_LEAN_OPTION_PREFIXES: &[&str] = &[
    "autoImplicit",
    "relaxedAutoImplicit",
    "pp.",
    "linter.",
    "maxHeartbeats",
    "maxRecDepth",
    "weak.linter.",
];

#[derive(Clone, Debug)]
pub struct StagingPolicy {
    /// Module-name prefixes owned by the judge (trusted packages, Expected,
    /// audit) — a candidate source file may not live there.
    pub reserved_prefixes: Vec<String>,
    /// Toolchain module prefixes a candidate may import.
    pub toolchain_prefixes: Vec<String>,
    /// Package names a candidate lakefile may `require` (we supply them pinned).
    pub allowed_requires: Vec<String>,
    /// Modules available from the judge's trusted build (importable).
    pub trusted_modules: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct CandidateModule {
    pub name: String,
    pub rel_path: String,
    pub imports: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Staged {
    /// Candidate modules in a valid build order.
    pub modules: Vec<CandidateModule>,
    pub findings: Vec<Finding>,
    pub warnings: Vec<String>,
}

pub fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    cs.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
}

pub fn has_prefix(module: &str, prefix: &str) -> bool {
    module == prefix || module.starts_with(&format!("{prefix}."))
}

fn manifest(findings: &mut Vec<Finding>, msg: String) {
    findings.push(Finding::new(ReasonCode::ManifestInvalid, Scope::All, msg));
}

/// Strip Lean comments (`--` and nested `/- -/`) and the contents of string
/// literals (replaced by spaces) so token scans see only code.
pub fn strip_lean_comments(src: &str) -> String {
    let b: Vec<char> = src.chars().collect();
    let mut out = String::with_capacity(src.len());
    let (mut i, mut depth, mut in_str) = (0usize, 0usize, false);
    while i < b.len() {
        let c = b[i];
        let n = b.get(i + 1).copied();
        if depth > 0 {
            if c == '/' && n == Some('-') {
                depth += 1;
                i += 2;
            } else if c == '-' && n == Some('/') {
                depth -= 1;
                i += 2;
                out.push(' ');
            } else {
                if c == '\n' {
                    out.push('\n');
                }
                i += 1;
            }
            continue;
        }
        if in_str {
            if c == '\\' {
                i += 2;
                out.push(' ');
                continue;
            }
            if c == '"' {
                in_str = false;
                out.push('"');
            } else {
                out.push(if c == '\n' { '\n' } else { ' ' });
            }
            i += 1;
            continue;
        }
        if c == '"' {
            in_str = true;
            out.push('"');
            i += 1;
        } else if c == '-' && n == Some('-') {
            while i < b.len() && b[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && n == Some('-') {
            depth = 1;
            i += 2;
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

fn tokens(code: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for c in code.chars() {
        if c.is_alphanumeric()
            || c == '_'
            || c == '.'
            || c == '\''
            || c == '#'
            || c == '«'
            || c == '»'
        {
            cur.push(c);
        } else {
            if !cur.is_empty() {
                toks.push(std::mem::take(&mut cur));
            }
            if !c.is_whitespace() {
                toks.push(c.to_string());
            }
        }
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    toks
}

/// Parse the import header of a Lean file. Returns (imports, uses_prelude).
pub fn parse_header(src: &str) -> Result<(Vec<String>, bool), String> {
    let code = strip_lean_comments(src);
    let toks = tokens(&code);
    let mut imports = Vec::new();
    let mut prelude = false;
    let mut i = 0;
    if toks.first().map(String::as_str) == Some("module") {
        i += 1;
    }
    if toks.get(i).map(String::as_str) == Some("prelude") {
        prelude = true;
        i += 1;
    }
    loop {
        let mut j = i;
        while matches!(
            toks.get(j).map(String::as_str),
            Some("public") | Some("meta")
        ) {
            j += 1;
        }
        if toks.get(j).map(String::as_str) != Some("import") {
            break;
        }
        j += 1;
        if toks.get(j).map(String::as_str) == Some("all") {
            j += 1;
        }
        let m = toks.get(j).ok_or("import without module")?;
        if !m.split('.').all(is_ident) {
            return Err(format!("unsupported import syntax: {m:?}"));
        }
        imports.push(m.clone());
        i = j + 1;
    }
    Ok((imports, prelude))
}

pub fn check_lakefile_toml(src: &str, policy: &StagingPolicy, f: &mut Vec<Finding>) {
    let v: toml::Value = match toml::from_str(src) {
        Ok(v) => v,
        Err(e) => return manifest(f, format!("lakefile.toml does not parse: {e}")),
    };
    let Some(top) = v.as_table() else {
        return manifest(f, "lakefile.toml: not a table".into());
    };
    let check_opts = |opts: &toml::Value, f: &mut Vec<Finding>| {
        if let Some(t) = opts.as_table() {
            for k in t.keys() {
                if !ALLOWED_LEAN_OPTION_PREFIXES
                    .iter()
                    .any(|p| k.starts_with(p))
                {
                    manifest(f, format!("lakefile.toml: leanOptions.{k} not allowed"));
                }
            }
        } else if let Some(arr) = opts.as_array() {
            for o in arr {
                let k = o.get("name").and_then(|n| n.as_str()).unwrap_or("?");
                if !ALLOWED_LEAN_OPTION_PREFIXES
                    .iter()
                    .any(|p| k.starts_with(p))
                {
                    manifest(f, format!("lakefile.toml: leanOptions {k} not allowed"));
                }
            }
        }
    };
    for (k, val) in top {
        if FORBIDDEN_LAKE_KEYS.contains(&k.as_str()) {
            manifest(f, format!("lakefile.toml: forbidden feature `{k}`"));
            continue;
        }
        if !ALLOWED_TOML_TOP.contains(&k.as_str()) {
            manifest(f, format!("lakefile.toml: unknown/unsupported key `{k}`"));
            continue;
        }
        match k.as_str() {
            "leanOptions" => check_opts(val, f),
            "lean_lib" => {
                for lib in val.as_array().into_iter().flatten() {
                    for (lk, lv) in lib.as_table().into_iter().flatten() {
                        if FORBIDDEN_LAKE_KEYS.contains(&lk.as_str()) {
                            manifest(
                                f,
                                format!("lakefile.toml: forbidden lean_lib feature `{lk}`"),
                            );
                        } else if !ALLOWED_TOML_LIB.contains(&lk.as_str()) {
                            manifest(f, format!("lakefile.toml: unsupported lean_lib key `{lk}`"));
                        } else if lk == "leanOptions" {
                            check_opts(lv, f);
                        }
                    }
                }
            }
            "require" => {
                for req in val.as_array().into_iter().flatten() {
                    let name = req.get("name").and_then(|n| n.as_str()).unwrap_or("");
                    if !policy.allowed_requires.iter().any(|a| a == name) {
                        manifest(
                            f,
                            format!("lakefile.toml: require `{name}` is not allowlisted"),
                        );
                    }
                    for rk in req.as_table().into_iter().flatten().map(|(k, _)| k) {
                        if !ALLOWED_TOML_REQUIRE.contains(&rk.as_str()) {
                            manifest(f, format!("lakefile.toml: unsupported require key `{rk}`"));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

pub fn check_lakefile_lean(src: &str, policy: &StagingPolicy, f: &mut Vec<Finding>) {
    // Raw scan for dynlib/plugin flags, even inside strings.
    for needle in ["--load-dynlib", "--plugin", "-Dtrust", "debug.skipKernelTC"] {
        if src.contains(needle) {
            manifest(f, format!("lakefile.lean: forbidden flag `{needle}`"));
        }
    }
    let code = strip_lean_comments(src);
    let toks = tokens(&code);
    let mut seen = BTreeSet::new();
    for t in &toks {
        let head = t.split('.').next().unwrap_or("");
        for bad in FORBIDDEN_LAKEFILE_LEAN_TOKENS {
            if (t == bad || head == *bad) && seen.insert(*bad) {
                manifest(f, format!("lakefile.lean: forbidden feature `{bad}`"));
            }
        }
    }
    for (i, t) in toks.iter().enumerate() {
        if t == "require" {
            let name = toks
                .get(i + 1)
                .map(|s| s.trim_matches(|c| c == '«' || c == '»'))
                .unwrap_or("");
            // `require "scope" / "name"` form
            let name = if name == "\"" {
                toks.iter()
                    .skip(i + 1)
                    .filter(|x| x.as_str() != "\"" && x.as_str() != "/")
                    .nth(1)
                    .map(String::as_str)
                    .unwrap_or("")
            } else {
                name
            };
            if !policy.allowed_requires.iter().any(|a| a == name) {
                manifest(
                    f,
                    format!("lakefile.lean: require `{name}` is not allowlisted"),
                );
            }
        }
    }
}

fn walk(
    root: &Path,
    dir: &Path,
    out: &mut Vec<(String, PathBuf, u64)>,
    f: &mut Vec<Finding>,
    w: &mut Vec<String>,
) {
    let rd = match std::fs::read_dir(dir) {
        Ok(r) => r,
        Err(e) => {
            return f.push(Finding::new(
                ReasonCode::ArchiveUnsafe,
                Scope::All,
                format!("unreadable dir: {e}"),
            ))
        }
    };
    let mut ents: Vec<_> = rd.filter_map(Result::ok).collect();
    ents.sort_by_key(|e| e.file_name());
    for e in ents {
        let p = e.path();
        let rel = match p.strip_prefix(root).ok().and_then(|r| r.to_str()) {
            Some(r) => r.to_string(),
            None => {
                f.push(Finding::new(
                    ReasonCode::ArchiveUnsafe,
                    Scope::All,
                    "non-UTF-8 path".into(),
                ));
                continue;
            }
        };
        let ft = match e.file_type() {
            Ok(t) => t,
            Err(_) => continue,
        };
        if ft.is_symlink() {
            f.push(Finding::new(
                ReasonCode::ArchiveUnsafe,
                Scope::All,
                format!("symlink in formal tree: {rel}"),
            ));
        } else if ft.is_dir() {
            let name = e.file_name();
            if matches!(
                name.to_str(),
                Some(".lake" | ".git" | "build" | "lake-packages")
            ) {
                w.push(format!(
                    "ignored directory {rel}/ (prebuilt or VCS data is never used)"
                ));
                continue;
            }
            walk(root, &p, out, f, w);
        } else if ft.is_file() {
            let len = e.metadata().map(|m| m.len()).unwrap_or(u64::MAX);
            out.push((rel, p, len));
        } else {
            f.push(Finding::new(
                ReasonCode::ArchiveUnsafe,
                Scope::All,
                format!("special file: {rel}"),
            ));
        }
    }
}

/// Validate a candidate `formal/` tree and copy its `.lean` sources into `dest`.
pub fn stage_candidate(
    formal: &Path,
    dest: &Path,
    policy: &StagingPolicy,
) -> std::io::Result<Staged> {
    let mut st = Staged::default();
    let mut files = Vec::new();
    walk(
        formal,
        formal,
        &mut files,
        &mut st.findings,
        &mut st.warnings,
    );
    if files.len() > MAX_FILES {
        manifest(
            &mut st.findings,
            format!("too many files ({})", files.len()),
        );
        return Ok(st);
    }
    let total: u64 = files.iter().map(|x| x.2).sum();
    if total > MAX_TOTAL_BYTES {
        manifest(
            &mut st.findings,
            format!("formal tree too large ({total} bytes)"),
        );
        return Ok(st);
    }
    let mut mods: BTreeMap<String, CandidateModule> = BTreeMap::new();
    for (rel, path, len) in &files {
        let fname = rel.rsplit('/').next().unwrap_or(rel);
        if *len > MAX_FILE_BYTES {
            manifest(&mut st.findings, format!("{rel}: file too large"));
            continue;
        }
        match rel.as_str() {
            "lakefile.toml" => {
                let s = std::fs::read_to_string(path).unwrap_or_default();
                check_lakefile_toml(&s, policy, &mut st.findings);
                continue;
            }
            "lakefile.lean" => {
                let s = std::fs::read_to_string(path).unwrap_or_default();
                check_lakefile_lean(&s, policy, &mut st.findings);
                continue;
            }
            "lean-toolchain" => {
                let s = std::fs::read_to_string(path).unwrap_or_default();
                if s.trim() != crate::toolchain::lean_toolchain() {
                    st.warnings.push(format!(
                        "candidate lean-toolchain {:?} ignored; judge uses {}",
                        s.trim(),
                        crate::toolchain::lean_toolchain()
                    ));
                }
                continue;
            }
            "lake-manifest.json" => {
                st.warnings
                    .push("lake-manifest.json ignored (judge supplies pinned dependencies)".into());
                continue;
            }
            _ => {}
        }
        if let Some(stem) = rel.strip_suffix(".lean") {
            let comps: Vec<&str> = stem.split('/').collect();
            if !comps.iter().all(|c| is_ident(c)) {
                manifest(
                    &mut st.findings,
                    format!("{rel}: not a valid Lean module path"),
                );
                continue;
            }
            let name = comps.join(".");
            let reserved = policy
                .reserved_prefixes
                .iter()
                .chain(policy.toolchain_prefixes.iter())
                .find(|p| has_prefix(&name, p));
            if let Some(p) = reserved {
                st.findings.push(Finding::new(
                    ReasonCode::ShadowedDefinition,
                    Scope::All,
                    format!("candidate ships module {name} inside judge-owned namespace {p}"),
                ));
                continue;
            }
            let src = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(_) => {
                    manifest(&mut st.findings, format!("{rel}: not UTF-8"));
                    continue;
                }
            };
            let (imports, prelude) = match parse_header(&src) {
                Ok(x) => x,
                Err(e) => {
                    manifest(&mut st.findings, format!("{rel}: {e}"));
                    continue;
                }
            };
            if prelude {
                manifest(
                    &mut st.findings,
                    format!("{rel}: `prelude` modules are not allowed"),
                );
                continue;
            }
            let target = dest.join(rel);
            std::fs::create_dir_all(target.parent().unwrap())?;
            std::fs::write(&target, src.as_bytes())?;
            mods.insert(
                name.clone(),
                CandidateModule {
                    name,
                    rel_path: rel.clone(),
                    imports,
                },
            );
        } else {
            let lower = fname.to_ascii_lowercase();
            let prebuilt = [
                ".olean",
                ".ilean",
                ".olean.server",
                ".olean.private",
                ".ir",
                ".c",
                ".o",
                ".so",
                ".a",
                ".dylib",
                ".dll",
                ".trace",
                ".hash",
            ]
            .iter()
            .any(|s| lower.ends_with(s));
            if prebuilt {
                st.warnings.push(format!(
                    "prebuilt artifact {rel} ignored (judge rebuilds from source)"
                ));
            } else if !(lower.ends_with(".md")
                || lower.starts_with("license")
                || lower == ".gitignore"
                || lower.ends_with(".txt"))
            {
                st.warnings.push(format!("non-Lean file {rel} ignored"));
            }
        }
    }
    // Resolve imports.
    for m in mods.values() {
        for imp in &m.imports {
            let ok = mods.contains_key(imp)
                || policy.trusted_modules.iter().any(|t| t == imp)
                || policy.toolchain_prefixes.iter().any(|p| has_prefix(imp, p));
            if !ok {
                manifest(
                    &mut st.findings,
                    format!(
                        "{}: import {imp} is not a candidate, trusted or toolchain module",
                        m.name
                    ),
                );
            }
        }
    }
    // Topological order (deterministic).
    let mut order = Vec::new();
    let mut state: BTreeMap<&str, u8> = BTreeMap::new();
    fn visit<'a>(
        n: &'a str,
        mods: &'a BTreeMap<String, CandidateModule>,
        state: &mut BTreeMap<&'a str, u8>,
        order: &mut Vec<String>,
    ) -> Result<(), String> {
        match state.get(n) {
            Some(2) => return Ok(()),
            Some(1) => return Err(format!("import cycle through {n}")),
            _ => {}
        }
        state.insert(n, 1);
        for imp in &mods[n].imports {
            if mods.contains_key(imp.as_str()) {
                visit(imp, mods, state, order)?;
            }
        }
        state.insert(n, 2);
        order.push(n.to_string());
        Ok(())
    }
    for n in mods.keys() {
        if let Err(e) = visit(n, &mods, &mut state, &mut order) {
            manifest(&mut st.findings, e);
            return Ok(st);
        }
    }
    if mods.is_empty() {
        st.findings.push(Finding::new(
            ReasonCode::CertificateMissing,
            Scope::All,
            "no .lean sources in formal tree".into(),
        ));
    }
    st.modules = order.into_iter().map(|n| mods[&n].clone()).collect();
    Ok(st)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn pol() -> StagingPolicy {
        StagingPolicy {
            reserved_prefixes: vec!["ArenaCore".into()],
            toolchain_prefixes: vec!["Init".into(), "Lean".into()],
            allowed_requires: vec!["arena-core".into()],
            trusted_modules: vec!["ArenaCore.Admission".into()],
        }
    }
    #[test]
    fn header() {
        let (i, p) = parse_header("/- c -/ module\n-- x\npublic import A.B\nimport all C import D\ntheorem x : True := by\n import").unwrap();
        assert_eq!(i, vec!["A.B", "C", "D"]);
        assert!(!p);
    }
    #[test]
    fn toml_rules() {
        let mut f = vec![];
        check_lakefile_toml("name = \"x\"\nmoreLeanArgs = [\"--load-dynlib=x.so\"]\n[[require]]\nname = \"mathlib\"\n", &pol(), &mut f);
        assert_eq!(f.len(), 2, "{f:?}");
        let mut f = vec![];
        check_lakefile_toml(
            "name = \"x\"\n[[lean_lib]]\nname = \"Candidate\"\nprecompileModules = true\n",
            &pol(),
            &mut f,
        );
        assert_eq!(f.len(), 1);
        let mut f = vec![];
        check_lakefile_toml(
            "name = \"x\"\n[[require]]\nname = \"arena-core\"\n[[lean_lib]]\nname = \"C\"\n",
            &pol(),
            &mut f,
        );
        assert!(f.is_empty(), "{f:?}");
    }
    #[test]
    fn lean_rules() {
        let mut f = vec![];
        check_lakefile_lean("import Lake\nopen Lake DSL\npackage x\n-- extern_lib in comment is fine\nlean_lib Candidate\n", &pol(), &mut f);
        assert!(f.is_empty(), "{f:?}");
        let mut f = vec![];
        check_lakefile_lean("import Lake\nopen Lake DSL\npackage x\nextern_lib ffi pkg := do pure default\nscript foo do return 0\n", &pol(), &mut f);
        assert_eq!(f.len(), 2, "{f:?}");
    }
}

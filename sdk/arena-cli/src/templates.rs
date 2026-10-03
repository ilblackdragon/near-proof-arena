//! Candidate templates embedded at compile time from `sdk/templates/`.
//! Placeholders: `{{NAME}}`, `{{AGENT}}`, `{{CHALLENGE}}`.
//!
//! When adding a file to a template, add it to the list below (the
//! `templates_list_complete` test fails otherwise).

pub struct TemplateFile {
    pub path: &'static str,
    pub contents: &'static str,
    pub exec: bool,
}

macro_rules! tf {
    ($tpl:literal, $path:literal, $exec:expr) => {
        TemplateFile {
            path: $path,
            contents: include_str!(concat!("../../templates/", $tpl, "/", $path)),
            exec: $exec,
        }
    };
}

pub const EMPTY: &[TemplateFile] = &[
    tf!("empty", "README.md", false),
    tf!("empty", "build-recipe/build.sh", true),
    tf!("empty", "candidate.toml", false),
    tf!("empty", "dependency-locks/Cargo.lock", false),
    tf!("empty", "dependency-locks/README.md", false),
    tf!("empty", "formal/Candidate.lean", false),
    tf!("empty", "formal/Candidate/Certificate.lean", false),
    tf!("empty", "formal/README.md", false),
    tf!("empty", "formal/lakefile.lean", false),
    tf!("empty", "formal/lean-toolchain", false),
    tf!("empty", "source/.cargo/config.toml", false),
    tf!("empty", "source/Cargo.lock", false),
    tf!("empty", "source/Cargo.toml", false),
    tf!("empty", "source/src/bin/prepare.rs", false),
    tf!("empty", "source/src/bin/prove.rs", false),
    tf!("empty", "source/src/bin/verify.rs", false),
    tf!("empty", "source/src/lib.rs", false),
    tf!("empty", "source/vendor/README.md", false),
];

pub fn get(name: &str) -> Option<&'static [TemplateFile]> {
    match name {
        "empty" => Some(EMPTY),
        _ => None,
    }
}

pub const NAMES: &[&str] = &["empty"];

pub fn render(s: &str, name: &str, agent: &str, challenge: &str) -> String {
    s.replace("{{NAME}}", name)
        .replace("{{AGENT}}", agent)
        .replace("{{CHALLENGE}}", challenge)
}

#[cfg(test)]
mod tests {
    #[test]
    fn templates_list_complete() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../templates/empty");
        let mut on_disk = Vec::new();
        fn walk(r: &std::path::Path, d: &std::path::Path, out: &mut Vec<String>) {
            for e in std::fs::read_dir(d).unwrap().flatten() {
                if e.path().is_dir() {
                    walk(r, &e.path(), out);
                } else {
                    out.push(
                        e.path()
                            .strip_prefix(r)
                            .unwrap()
                            .to_string_lossy()
                            .into_owned(),
                    );
                }
            }
        }
        walk(&root, &root, &mut on_disk);
        on_disk.sort();
        let listed: Vec<String> = super::EMPTY.iter().map(|f| f.path.to_string()).collect();
        assert_eq!(on_disk, listed);
    }
}

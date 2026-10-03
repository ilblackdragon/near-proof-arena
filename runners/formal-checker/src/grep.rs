//! Supplementary source scan. Produces *warnings only*; it never decides a
//! gate (the decisive checks run on the kernel-rechecked environment).

use std::path::Path;

const PATTERNS: &[(&str, &str)] = &[
    ("sorry", "uses `sorry`"),
    ("admit", "uses `admit`"),
    ("axiom", "declares an axiom"),
    ("native_decide", "uses native_decide"),
    ("ofReduceBool", "references Lean.ofReduceBool"),
    ("implemented_by", "uses @[implemented_by]"),
    ("extern", "uses @[extern]"),
    ("unsafe", "uses unsafe"),
    ("partial", "uses partial"),
    ("skipKernelTC", "sets debug.skipKernelTC"),
    ("#eval", "runs #eval at elaboration time"),
    ("run_cmd", "runs run_cmd at elaboration time"),
    ("initialize", "declares an initializer"),
    ("addDecl", "adds declarations from metaprograms"),
];

pub fn scan(src_root: &Path, rel_paths: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for rel in rel_paths {
        let Ok(src) = std::fs::read_to_string(src_root.join(rel)) else { continue };
        let code = crate::staging::strip_lean_comments(&src);
        for (lineno, line) in code.lines().enumerate() {
            for (pat, what) in PATTERNS {
                let hit = line.match_indices(pat).any(|(i, _)| {
                    let before = line[..i].chars().last();
                    let after = line[i + pat.len()..].chars().next();
                    let word = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
                    !word(before) && !word(after)
                });
                if hit && out.len() < 200 {
                    out.push(format!("source scan (supplementary): {rel}:{} {what}", lineno + 1));
                }
            }
        }
    }
    out
}

//! Build helper (not shipped, not run by the judge): Lean module orders of the
//! judge's native-lean build (runners/formal-checker), so build-recipe/build.sh
//! links `out/verify` exactly as the judge does.
//!
//! * `leanorder DIR PREFIX...` — trusted modules under DIR matching a prefix,
//!   in `pipeline.rs` `topo` order (depth-first over sorted names, imports
//!   first in header order).
//! * `leanorder --closure DIR MODULE` — the candidate tree DIR (`formal/`)
//!   staged like `staging.rs` `stage_candidate` (every `.lean` file outside
//!   `.lake`/`.git`/`build`/`lake-packages`, the same depth-first topological
//!   order over the WHOLE tree), filtered to MODULE's transitive candidate
//!   import closure: the judge's `model_mods` order. Fails if MODULE is
//!   missing or a closure module imports something that is neither in the
//!   tree nor in `--trusted` modules nor `Init` (the judge's import rule for
//!   model modules) when `--trusted DIR PREFIX...` is given after MODULE.
//!
//! Header parsing mirrors `staging.rs` `parse_header` (comments and string
//! contents stripped, `module`/`prelude`/`public`/`meta`/`import all`).
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

fn die(m: &str) -> ! {
    eprintln!("leanorder: {m}");
    std::process::exit(2)
}

fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let mut es: Vec<_> = std::fs::read_dir(dir)
        .expect("read dir")
        .map(|e| e.unwrap())
        .collect();
    es.sort_by_key(|e| e.file_name());
    for e in es {
        let p = e.path();
        if p.is_dir() {
            if matches!(
                e.file_name().to_str(),
                Some(".lake" | ".git" | "build" | "lake-packages")
            ) {
                continue;
            }
            walk(root, &p, out);
        } else if p.extension().is_some_and(|x| x == "lean") {
            let rel = p.strip_prefix(root).unwrap().with_extension("");
            out.push(
                rel.components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join("."),
            );
        }
    }
}

/// `staging.rs` `strip_lean_comments`.
fn strip(src: &str) -> String {
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
        if c.is_alphanumeric() || matches!(c, '_' | '.' | '\'' | '#' | '«' | '»') {
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

/// `staging.rs` `parse_header` (imports only).
fn imports(src: &str) -> Vec<String> {
    let toks = tokens(&strip(src));
    let t = |j: usize| toks.get(j).map(String::as_str);
    let mut v = Vec::new();
    let mut i = 0;
    if t(i) == Some("module") {
        i += 1;
    }
    if t(i) == Some("prelude") {
        i += 1;
    }
    loop {
        let mut j = i;
        while matches!(t(j), Some("public") | Some("meta")) {
            j += 1;
        }
        if t(j) != Some("import") {
            break;
        }
        j += 1;
        if t(j) == Some("all") {
            j += 1;
        }
        let Some(m) = t(j) else {
            die("import without module")
        };
        v.push(m.to_string());
        i = j + 1;
    }
    v
}

fn load(root: &Path, keep: impl Fn(&str) -> bool) -> BTreeMap<String, Vec<String>> {
    let mut names = Vec::new();
    walk(root, root, &mut names);
    let mut map = BTreeMap::new();
    for n in names.into_iter().filter(|n| keep(n)) {
        let src = std::fs::read_to_string(root.join(format!("{}.lean", n.replace('.', "/"))))
            .unwrap_or_else(|e| die(&format!("{n}: {e}")));
        map.insert(n, imports(&src));
    }
    map
}

fn topo(map: &BTreeMap<String, Vec<String>>) -> Vec<String> {
    fn go(
        n: &str,
        map: &BTreeMap<String, Vec<String>>,
        st: &mut BTreeMap<String, u8>,
        out: &mut Vec<String>,
    ) {
        match st.get(n) {
            Some(2) => return,
            Some(_) => die(&format!("import cycle at {n}")),
            None => {}
        }
        st.insert(n.into(), 1);
        for i in &map[n] {
            if map.contains_key(i) {
                go(i, map, st, out);
            }
        }
        st.insert(n.into(), 2);
        out.push(n.into());
    }
    let (mut st, mut out) = (BTreeMap::new(), Vec::new());
    for n in map.keys() {
        go(n, map, &mut st, &mut out);
    }
    out
}

fn has_prefix(n: &str, p: &str) -> bool {
    n == p || n.starts_with(&format!("{p}."))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("--closure") {
        let (root, module) = match args.get(1..3) {
            Some([r, m]) => (Path::new(r), m.clone()),
            _ => die("usage: leanorder --closure DIR MODULE [--trusted TDIR PREFIX...]"),
        };
        let trusted: BTreeSet<String> = match args.get(3).map(String::as_str) {
            None => BTreeSet::new(),
            Some("--trusted") if args.len() >= 5 => {
                let pre = &args[5..];
                load(Path::new(&args[4]), |n| {
                    pre.iter().any(|p| has_prefix(n, p))
                })
                .into_keys()
                .collect()
            }
            _ => die("usage: leanorder --closure DIR MODULE [--trusted TDIR PREFIX...]"),
        };
        let map = load(root, |_| true);
        if !map.contains_key(&module) {
            die(&format!(
                "verifier model module {module} is not part of the candidate formal tree"
            ));
        }
        let mut need = BTreeSet::new();
        let mut stack = vec![module];
        while let Some(n) = stack.pop() {
            if !need.insert(n.clone()) {
                continue;
            }
            for i in &map[&n] {
                if map.contains_key(i) {
                    stack.push(i.clone());
                } else if args.len() > 3 && !trusted.contains(i) && !has_prefix(i, "Init") {
                    die(&format!(
                        "verifier model module {n} imports {i}: model modules may import only trusted modules, other model modules and Init"
                    ));
                }
            }
        }
        for n in topo(&map).into_iter().filter(|n| need.contains(n)) {
            println!("{n}");
        }
    } else {
        let Some(root) = args.first() else {
            die("usage: leanorder DIR PREFIX...")
        };
        let pre = &args[1..];
        for n in topo(&load(Path::new(root), |n| {
            pre.iter().any(|p| has_prefix(n, p))
        })) {
            println!("{n}");
        }
    }
}

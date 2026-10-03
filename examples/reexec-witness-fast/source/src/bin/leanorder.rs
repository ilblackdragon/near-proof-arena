//! Build helper (not shipped): print the Lean modules under DIR whose names
//! match one of the PREFIX arguments, in the judge's native-lean link order —
//! runners/formal-checker `topo`: depth-first over module names in sorted
//! order, imports first, in header order.
//!
//! usage: leanorder DIR PREFIX...
use std::collections::BTreeMap;
use std::path::Path;

fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let mut es: Vec<_> = std::fs::read_dir(dir).expect("read dir").map(|e| e.unwrap().path()).collect();
    es.sort();
    for p in es {
        if p.is_dir() {
            walk(root, &p, out);
        } else if p.extension().is_some_and(|x| x == "lean") {
            let rel = p.strip_prefix(root).unwrap().with_extension("");
            out.push(rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect::<Vec<_>>().join("."));
        }
    }
}

fn imports(src: &str) -> Vec<String> {
    let mut v = Vec::new();
    for line in src.lines() {
        let l = line.trim();
        if l.is_empty() || l.starts_with("--") {
            continue;
        }
        let Some(rest) = l.strip_prefix("import ") else { break };
        v.extend(rest.split_whitespace().map(String::from));
    }
    v
}

fn go(n: &str, map: &BTreeMap<String, Vec<String>>, st: &mut BTreeMap<String, u8>, out: &mut Vec<String>) {
    match st.get(n) {
        Some(2) => return,
        Some(_) => panic!("import cycle at {n}"),
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

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = Path::new(&args[0]);
    let prefixes = &args[1..];
    let mut names = Vec::new();
    walk(root, root, &mut names);
    let mut map = BTreeMap::new();
    for n in names {
        if !prefixes.iter().any(|p| n == *p || n.starts_with(&format!("{p}."))) {
            continue;
        }
        let src = std::fs::read_to_string(root.join(format!("{}.lean", n.replace('.', "/")))).unwrap();
        map.insert(n, imports(&src));
    }
    let (mut st, mut out) = (BTreeMap::new(), Vec::new());
    for n in map.keys() {
        go(n, &map, &mut st, &mut out);
    }
    for n in out {
        println!("{n}");
    }
}

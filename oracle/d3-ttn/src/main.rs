//! near-d3-ttn: trie-accounting experiment (docs/research/d3-trie-accounting.md).
//!
//! usage: near-d3-ttn [--seed N] [--shards N] [--blocks N] [--ops N] [--memtries] [--trace FILE] [--v2] [--limit-plan FILE] --out FILE
mod d3ttn;
mod judge;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |n: &str| args.iter().position(|a| a == n).map(|i| args[i + 1].clone());
    let num = |n: &str, d: u64| get(n).map(|v| v.parse().unwrap()).unwrap_or(d);
    let p = d3ttn::Params {
        seed: num("--seed", 1),
        n_shards: num("--shards", 4) as usize,
        blocks: num("--blocks", 40),
        memtries: args.iter().any(|a| a == "--memtries"),
        ops_max: num("--ops", 40) as usize,
        trace: get("--trace").map(std::path::PathBuf::from),
        v2: args.iter().any(|a| a == "--v2"),
        limit_plan: get("--limit-plan")
            .map(|f| {
                std::fs::read_to_string(f)
                    .unwrap()
                    .lines()
                    .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
                    .map(|l| {
                        let t: Vec<&str> = l.split_whitespace().collect();
                        (t[0].parse().unwrap(), t[1].parse().unwrap(), hex::decode(t[2]).unwrap(), t[3].parse().unwrap())
                    })
                    .collect()
            })
            .unwrap_or_default(),
    };
    let out = get("--out").expect("--out FILE");
    d3ttn::cmd_ttn(&p, std::path::Path::new(&out));
}

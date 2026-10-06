//! near-d3-ttn: trie-accounting experiment (docs/research/d3-trie-accounting.md).
//!
//! usage: near-d3-ttn [--seed N] [--shards N] [--blocks N] [--ops N] [--memtries] --out FILE
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
    };
    let out = get("--out").expect("--out FILE");
    d3ttn::cmd_ttn(&p, std::path::Path::new(&out));
}

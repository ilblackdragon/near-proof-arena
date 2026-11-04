//! [E2E-D D-5 .. D-7] The chunk-independent aggregation tree and the ZK wrap over it (plan §5.0.1;
//! circuit side `openvm-recursion-circuit::nv::tree`).
//!
//! `tree-prove` (D-7 shape): leaves at their own heights `h_L`, nodes at the node heights `h_N`:
//! * **leaves (level 1, geometry `leaf`)**: the chunk's template leaf (default: the *base-template
//!   leaf* `build_base_leaf`, which verifies the chunk's base proof directly; `NEARPROOF_TREE_TEMPLATE
//!   =chain`: the normaliser of the converged chain proof `L4`) at index 0, then `PAD_L` leaves up
//!   to the arity;
//! * **`P_2` (level 2, geometry `node`)**: `arity` leaves, each forced to level 1 and bound by the
//!   template set `{C_t} ∪ {C_padL}` (no BIND, so leaves keep their own, smaller heights);
//! * **`P_*` (levels >= 3, geometry `node`)**: `arity` children at the node heights; level-2 children
//!   bound by `{C_2, C_padN}`, deeper ones by BIND (child 0) and `root_i ∈ {root_0, C_padN}`;
//! * **`PAD_N`** (any level >= 2, node heights; its level is a witness): fills a level up to a
//!   multiple of the arity, so a tree over `n` leaves never proves a subtree of padding;
//! * **the wrap** (FINAL domain, zk = 6): verifies the root at the forced level `1 + depth`, its
//!   program anchored at `C_2` (depth 1) or `C_*`, and exposes `[LEVEL_WRAP, D_wrap(ctx, class)]`.
//! The node geometry may use several SHA compression instances (`sha_instances`, cap 2^22 rows each).
//!
//! The setup is a function of (the template classes, arity, depth): a template class is a pinned
//! base shape (`NEARPROOF_BASE_CLASS`, review-D6 F1), so every chunk whose base was proved at that
//! class shape has the same leaf program; the setup lists per class the base vk hash, the pinned
//! base heights and the leaf program root (no chunk names: review-D6 F2, F7).
//!
//! `tree-verify`: V_d. Packet `NPQTW02 | u64 |hint| | hint | u32 class | u32 m | u (m x 12 u32) |
//! wrap proof`; V_d recomputes `ctx` from (claim, hint, u) under class `class`'s base parameters and
//! checks `pvs = [LEVEL_WRAP, D_wrap(ctx, class)]`. Malformed input is an error (exit code 1,
//! `TREE_VERIFY_REJECT`), never a panic (review-D5).
use super::*;
use openvm_recursion_circuit::{
    nv::{
        agg::RangeStmt,
        builder::Builder,
        circuit::{program_commitment, prove_mats},
        tree::{self as t, build_base_leaf, build_node2, build_node_star, build_norm, build_pad, build_pad_node, build_wrap},
    },
    sha384::config::{Digest, F, fs_jobs, fs_jobs_reset},
};
use openvm_stark_backend::StarkProtocolConfig;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

const MAGIC: &[u8; 8] = b"NPQTW02\0";
const SETUP_VERSION: u32 = 4;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct TemplateEntry {
    /// template class index (the packet's `class`)
    pub class: u32,
    /// "base" (`build_base_leaf`) or "chain" (`build_norm` over the chain's L4)
    pub kind: String,
    /// sha256 of the class's base vk (saved form): the AIR set and base parameters (review-D6 F7)
    pub base_vk_sha256: String,
    /// the class's pinned base heights (log, tight) per base AIR: the shape class (review-D6 F1)
    pub base_heights: Vec<vd::PinnedHeight>,
    /// the anchor the normaliser binds its child by ((0, 0) for the base-template leaf)
    pub anchor: (u32, Digest),
    /// the leaf's program root (an element of `P_2`'s template set)
    pub c_norm: Digest,
}

/// A tree proof geometry: NvAir rows 2^log_rows, program 2^prog_log, SHA instances, pinned heights.
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct Geom {
    pub log_rows: usize,
    pub prog_log: usize,
    pub sha_instances: usize,
    pub heights: Vec<vd::PinnedHeight>,
}

/// Audit content of the wrap setup: everything the wrap program embeds (V_d reads none of it).
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct TreeShape {
    pub arity: usize,
    pub depth: usize,
    pub leaf: Geom,
    pub node: Geom,
    pub templates: Vec<TemplateEntry>,
    pub c_pad_leaf: Digest,
    pub c_node2: Digest,
    pub c_pad_node: Digest,
    /// `C_*` (None at depth 1: no level >= 3)
    pub c_node_star: Option<Digest>,
    pub wrap_log_rows: usize,
    pub wrap_prog_log: usize,
}

#[derive(Serialize, Deserialize)]
pub struct WrapSetup {
    pub version: u32,
    pub domain_odd_factor: usize,
    /// the D0a template's base AIR (V_d recomputes the template statement `ctx`)
    pub air_sha256: String,
    /// per template class (class order): the D0a base parameters V_d recomputes `ctx` under
    pub base_params: Vec<SystemParams>,
    pub final_vk: MultiStarkVerifyingKey<SC>,
    pub program: Vec<[u32; 4]>,
    pub level: u32,
    pub final_heights: Vec<vd::PinnedHeight>,
    pub tree: TreeShape,
}

const WRAP_LOG_ROWS: usize = 20;

fn root_of(p: &Proof<SC>) -> Digest {
    p.trace_vdata[0].as_ref().unwrap().cached_commitments[0]
}

fn template_kind_base() -> bool {
    match std::env::var("NEARPROOF_TREE_TEMPLATE").as_deref() {
        Ok("base") | Err(_) => true,
        Ok("chain") => false,
        Ok(o) => panic!("unknown NEARPROOF_TREE_TEMPLATE {o}"),
    }
}

fn env_pair(name: &str, d: (usize, usize)) -> (usize, usize) {
    std::env::var(name).ok().map_or(d, |v| {
        let x: Vec<usize> = v.split(',').map(|s| s.trim().parse().unwrap()).collect();
        (x[0], x[1])
    })
}

fn circ(k: usize, log_rows: usize, prog_log: usize, sha: usize, cap_log: usize, h: Option<&[vd::PinnedHeight]>) -> NvCircuit {
    let mut c = NvCircuit::new(k, log_rows, sha);
    c.program_part = true;
    c.prog_log = prog_log;
    c.sha_cap_log = cap_log;
    if let Some(h) = h {
        c.heights = Some(h.iter().map(|&(l, _)| 1usize << l).collect());
        c.tight_floor = Some(h.iter().map(|&(l, tt)| tt.unwrap_or(1 << l)).collect());
    }
    c
}

fn fits(nat: &[vd::PinnedHeight], pin: &[vd::PinnedHeight]) -> bool {
    nat.len() == pin.len() && nat.iter().zip(pin).all(|(a, b)| a.0 <= b.0 && a.1.unwrap_or(1 << a.0) <= b.1.unwrap_or(1 << b.0))
}

/// Per-AIR maximum of several pins (same AIR set).
fn max_pin(pins: &[Vec<vd::PinnedHeight>]) -> Vec<vd::PinnedHeight> {
    (0..pins[0].len())
        .map(|a| {
            let l = pins.iter().map(|p| p[a].0).max().unwrap();
            let t = pins.iter().map(|p| p[a].1.unwrap_or(1 << p[a].0)).max().unwrap();
            (l, Some(t))
        })
        .collect()
}

/// Grow a pin by `margin` (NvAir tight; SHA total, redistributed over `k` instances of 2^cap_log).
fn grow_pin(p: &[vd::PinnedHeight], margin: f64, k: usize, cap_log: usize) -> Vec<vd::PinnedHeight> {
    let g = |x: usize| ((x as f64 * margin).ceil() as usize).next_multiple_of(4);
    let mut out = p.to_vec();
    let t0 = g(p[0].1.unwrap()).min(1 << p[0].0);
    out[0] = (p[0].0, Some(t0));
    let idx: Vec<usize> = (0..k).map(openvm_recursion_circuit::nv::circuit::sha_air_index).collect();
    let total = g(idx.iter().map(|&a| p[a].1.unwrap()).sum());
    let cap = 1usize << cap_log;
    assert!(total <= k * cap, "SHA pin {total} above {k} instances of 2^{cap_log}");
    let mut rem = total;
    for (j, &a) in idx.iter().enumerate() {
        let t = if j + 1 < k { rem.min(cap) } else { rem }.max(4);
        rem = rem.saturating_sub(t);
        let l = p[a].0.max(t.next_power_of_two().trailing_zeros() as usize);
        out[a] = (l, Some(t.min(1 << l)));
    }
    out
}

/// The chunk's D0a template claim (statement digest of the base proof + TAPE at u).
fn d0a_claim(air: &str, public: &str, dir: &Path) -> (openvm_recursion_circuit::nv::circuit::StatementClaim, Vec<Ef>, SystemParams) {
    let (vk, p) = load_base(dir);
    let u = base_point(&vk, &p);
    let params = vk.inner.params.clone();
    let c = state::chunk_bridge::expected_claim_at(air, public, params.clone(), &u);
    (c, u, params)
}

fn vk_sha(vk: &MultiStarkVerifyingKey<SC>) -> String {
    let envelope = SavedVk { domain_odd_factor: vk.inner.params.whir.domain_odd_factor, vk: vk.clone() };
    hash(&serde_json::to_vec(&envelope).unwrap())
}

/// One template leaf candidate: the child proof it verifies and its entry (program root etc.).
struct Tmpl {
    vk: MultiStarkVerifyingKey<SC>,
    p: Proof<SC>,
    entry: TemplateEntry,
    pin: Vec<vd::PinnedHeight>,
    rows: usize,
    u: Vec<Ef>,
}

#[allow(clippy::too_many_arguments)]
fn template_of(dir: &Path, class: u32, base_tmpl: bool, chain_engine: &Sha384CpuEngine, parent: &Sha384CpuEngine, lc: &NvCircuit) -> Tmpl {
    let (bvk, bp) = load_base(dir);
    let u = base_point(&bvk, &bp);
    let base_heights = vd::proof_heights(&bp).expect("base heights");
    let base_vk_sha256 = vk_sha(&bvk);
    let (vk, p, anchor) = if base_tmpl {
        (bvk, bp, (0u32, Digest::default()))
    } else {
        let vk = read_vk(&dir.join("L4.vk.json"));
        let p = read_proof(&dir.join("L4.proof"));
        chain_engine.verify(&vk, &p).expect("template L4 proof");
        let anchor = (p.public_values[0][0].as_canonical_u32(), root_of(&p));
        (vk, p, anchor)
    };
    let (mats, b) = lc.generate_with(|b| {
        if base_tmpl {
            build_base_leaf(b, &vk, &p, F::ZERO, class);
        } else {
            build_norm(b, &vk, &p, anchor, F::ZERO, class);
        }
    });
    assert!(b.failures.is_empty(), "template leaf {}: {:?}", dir.display(), b.failures);
    let c_norm = program_commitment(parent.config(), &mats[0]);
    let (pin, _) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
    let entry = TemplateEntry { class, kind: if base_tmpl { "base" } else { "chain" }.into(), base_vk_sha256, base_heights, anchor, c_norm };
    Tmpl { vk, p, entry, pin, rows: b.instrs.len(), u }
}

/// A proof of the tree with its exposed statement and kind.
struct Item {
    vk: MultiStarkVerifyingKey<SC>,
    p: Proof<SC>,
    stmt: RangeStmt,
}

fn secs(t0: std::time::Instant) -> f64 {
    t0.elapsed().as_secs_f64()
}

pub fn tree_prove(air: &str, public: &str, out: &Path, chunk: &Path, classes: &[String], certs: &str, exclusions: &str, arity: usize, depth: usize) {
    assert!(arity >= 2 && depth >= 1);
    std::fs::create_dir_all(out).unwrap();
    let t_all = std::time::Instant::now();
    let tparams = profile::params_geom(false, certs, exclusions, profile::tree_geom());
    let cap_log = tparams.l_skip + tparams.n_stack;
    println!(
        "TREE_PARAMS n_stack={} log_blowup={} queries={:?} sha_cap_log={cap_log}",
        tparams.n_stack,
        tparams.log_blowup,
        tparams.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>()
    );
    let parent = Sha384CpuEngine::new(tparams);
    let chain_engine = Sha384CpuEngine::new(profile::params(false, certs, exclusions));
    let final_engine = Sha384CpuEngine::new_final(profile::params(true, certs, exclusions));
    let k = parent.config().params().k_whir();
    let fixed: Option<WrapSetup> = std::env::var("NEARPROOF_TREE_SETUP").ok().map(|p| serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap());
    let base_tmpl = template_kind_base();
    let margin: f64 = std::env::var("NEARPROOF_TREE_NODE_MARGIN").ok().map_or(1.10, |v| v.parse().unwrap());
    let mut seconds = serde_json::Map::new();
    let mut kinds: std::collections::BTreeMap<String, Vec<f64>> = Default::default();
    // ---- leaf geometry (a setup constant: the leaf programs depend on it)
    let (leaf_log, leaf_prog) = match &fixed {
        Some(f) => (f.tree.leaf.log_rows, f.tree.leaf.prog_log),
        None => env_pair("NEARPROOF_TREE_LEAF_GEOM", (19, 18)),
    };
    let probe_l = circ(k, leaf_log, leaf_prog, 1, cap_log, None);
    // ---- templates: one leaf program per class; the chunk's own template must equal one of them
    let mut tmpls: Vec<Tmpl> = vec![];
    for (i, dir) in classes.iter().enumerate() {
        let t0 = std::time::Instant::now();
        let tm = template_of(Path::new(dir), i as u32, base_tmpl, &chain_engine, &parent, &probe_l);
        println!("TREE_TEMPLATE class={i} kind={} rows={} pin={:?} base_vk={} s={:.1}", tm.entry.kind, tm.rows, tm.pin, &tm.entry.base_vk_sha256[..16], secs(t0));
        tmpls.push(tm);
    }
    // confirmations (review-D6 F5): every base proof given for a class (the class dir, the chunk,
    // NEARPROOF_TREE_CONFIRM dirs) must yield that class's template; count distinct base points u
    let mut confirm: Vec<Vec<Vec<Ef>>> = tmpls.iter().map(|t| vec![t.u.clone()]).collect();
    let match_class = |tm: &Tmpl, tmpls: &[Tmpl]| -> Option<usize> {
        tmpls.iter().position(|c| c.entry.c_norm == tm.entry.c_norm && c.entry.base_vk_sha256 == tm.entry.base_vk_sha256 && c.entry.base_heights == tm.entry.base_heights)
    };
    let extra: Vec<String> = std::env::var("NEARPROOF_TREE_CONFIRM").map(|v| v.split_whitespace().map(String::from).collect()).unwrap_or_default();
    for dir in &extra {
        // the class index is a program constant of the leaf: try each
        let hit = (0..tmpls.len()).find_map(|c| {
            let tm = template_of(Path::new(dir), c as u32, base_tmpl, &chain_engine, &parent, &probe_l);
            (match_class(&tm, &tmpls) == Some(c)).then_some((c, tm.u))
        });
        let (c, u) = hit.unwrap_or_else(|| panic!("confirmation {dir}: its template is no class's"));
        if !confirm[c].contains(&u) {
            confirm[c].push(u);
        }
        println!("TREE_TEMPLATE_CONFIRMED class={c} by={dir}");
    }
    let (class, target) = (0..tmpls.len())
        .find_map(|c| {
            let tm = template_of(chunk, c as u32, base_tmpl, &chain_engine, &parent, &probe_l);
            (match_class(&tm, &tmpls) == Some(c)).then_some((c, tm))
        })
        .expect("the chunk's template leaf is no class's: its base is not at a class shape");
    if !confirm[class].contains(&target.u) {
        confirm[class].push(target.u.clone());
    }
    let class = class as u32;
    let templates: Vec<TemplateEntry> = tmpls.iter().map(|t| t.entry.clone()).collect();
    let confirmed: Vec<usize> = confirm.iter().map(Vec::len).collect();
    println!("TREE_CHUNK_CLASS class={class} confirmations_per_class={confirmed:?}");
    let ctx: Vec<F> = if base_tmpl { t::ctx_of_digest(d0a_claim(air, public, chunk).0.digest()) } else { target.p.public_values[0][1..19].to_vec() };
    let done = vec![F::from_u32(t::PHASE_DONE), F::from_u32(class)];
    // ---- PAD_L
    let (mats, b) = probe_l.generate_with(|b| {
        build_pad(b, &ctx, F::ONE, &done);
    });
    let c_pad_leaf = program_commitment(parent.config(), &mats[0]);
    let (pad_pin, _) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
    println!("TREE_PAD_LEAF rows={} pin={pad_pin:?}", b.instrs.len());
    let mut set: Vec<Digest> = templates.iter().map(|t| t.c_norm).collect();
    set.push(c_pad_leaf);
    let h_l: Vec<vd::PinnedHeight> = match &fixed {
        Some(f) => {
            assert_eq!(f.tree.templates, templates, "template set differs from the fixed setup's");
            assert_eq!(f.tree.c_pad_leaf, c_pad_leaf, "PAD_L differs from the fixed setup's");
            assert_eq!((f.tree.arity, f.tree.depth), (arity, depth), "tree shape differs from the fixed setup's");
            if std::env::var("NEARPROOF_TREE_TEMPLATES_ONLY").is_ok_and(|v| v == "1") {
                println!("TREE_TEMPLATES_MATCH_FIXED_SETUP classes={}", templates.len());
                return;
            }
            f.tree.leaf.heights.clone()
        }
        None => {
            let mut pins: Vec<_> = tmpls.iter().map(|t| t.pin.clone()).collect();
            pins.push(pad_pin);
            max_pin(&pins)
        }
    };
    println!("TREE_LEAF_HEIGHTS {h_l:?}");
    drop(tmpls);
    // ---- leaves
    let lc = circ(k, leaf_log, leaf_prog, 1, cap_log, Some(&h_l));
    let mut items: Vec<Item> = vec![];
    let mut n_proofs = 0usize;
    // NEARPROOF_TREE_REUSE_LEAVES=DIR: take LEAF{i}.proof from an earlier run of the same chunk and
    // leaf setup when it is the same leaf (native verification, leaf heights, program root and
    // statement all checked); leaves do not depend on the arity or the depth (measurement aid)
    let reuse = std::env::var("NEARPROOF_TREE_REUSE_LEAVES").ok().map(std::path::PathBuf::from);
    for i in 0..arity {
        let t0 = std::time::Instant::now();
        if let Some(rd) = &reuse {
            let f = rd.join(format!("LEAF{i}.proof"));
            if f.exists() {
                let p = read_proof(&f);
                let v = read_vk(&rd.join("LEAF.vk.json"));
                let stmt = if i == 0 {
                    RangeStmt { ctx: ctx.clone(), a: F::ZERO, e: F::ONE, s_a: vec![F::from_u32(t::PHASE_INIT), F::from_u32(class)], s_e: done.clone() }
                } else {
                    RangeStmt { ctx: ctx.clone(), a: F::from_usize(i), e: F::from_usize(i + 1), s_a: done.clone(), s_e: done.clone() }
                };
                if parent.verify(&v, &p).is_ok()
                    && vd::proof_heights(&p).as_ref() == Some(&h_l)
                    && root_of(&p) == set[if i == 0 { class as usize } else { set.len() - 1 }]
                    && openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], &stmt)
                {
                    save_proof(&out.join(format!("LEAF{i}.proof")), &p);
                    if i == 0 {
                        save_vk(&out.join("LEAF.vk.json"), &v);
                    }
                    println!("TREE_LEAF {i} reused={}", f.display());
                    n_proofs += 1;
                    items.push(Item { vk: v, p, stmt });
                    continue;
                }
                println!("TREE_LEAF {i} not reusable ({})", f.display());
            }
        }
        let mut s = None;
        let (mats, b) = lc.generate_with(|b| {
            s = Some(if i == 0 {
                if base_tmpl { build_base_leaf(b, &target.vk, &target.p, F::ZERO, class) } else { build_norm(b, &target.vk, &target.p, target.entry.anchor, F::ZERO, class) }
            } else {
                build_pad(b, &ctx, F::from_usize(i), &done)
            });
        });
        assert!(b.failures.is_empty(), "leaf {i}: {:?}", b.failures);
        let (v, p, _) = prove_mats(&lc, &parent, mats, &b);
        assert_eq!(vd::proof_heights(&p).unwrap(), h_l, "leaf {i}: heights differ from the leaf pin");
        assert_eq!(root_of(&p), set[if i == 0 { class as usize } else { set.len() - 1 }], "leaf {i}: program root not its template's");
        let stmt = s.unwrap();
        assert!(openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], &stmt));
        let bytes = save_proof(&out.join(format!("LEAF{i}.proof")), &p);
        let sec = secs(t0);
        println!("TREE_LEAF {i} rows={} bytes={bytes} seconds={sec:.1}", b.instrs.len());
        seconds.insert(format!("leaf{i}"), sec.into());
        kinds.entry(if i == 0 { "leaf_template" } else { "pad_leaf" }.into()).or_default().push(sec);
        if i == 0 {
            save_vk(&out.join("LEAF.vk.json"), &v);
        }
        n_proofs += 1;
        items.push(Item { vk: v, p, stmt });
    }
    // ---- node geometry: from the first P_2 (setup creation) or the fixed setup
    let node_refs = |items: &[Item]| -> Vec<(MultiStarkVerifyingKey<SC>, Proof<SC>)> { items.iter().map(|x| (x.vk.clone(), x.p.clone())).collect() };
    let leaf_kids = node_refs(&items);
    let pre: Vec<RangeStmt> = items.iter().map(|x| x.stmt.clone()).collect();
    let gen_p2 = |c: &NvCircuit| -> std::thread::Result<(Vec<p3_matrix::dense::RowMajorMatrix<F>>, Builder, RangeStmt)> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = leaf_kids.iter().map(|(a, b)| (a, b)).collect();
            let mut s = None;
            let (m, b) = c.generate_with(|b| {
                s = Some(build_node2(b, &refs, &pre, &set));
            });
            (m, b, s.unwrap())
        }))
    };
    let node_geom: Geom = match &fixed {
        Some(f) => f.tree.node.clone(),
        None => {
            let m = if depth >= 2 { margin } else { 1.0 };
            // sizes at the largest geometry, then the smallest geometry holding them with the margin
            let maxg = circ(k, cap_log, cap_log - 1, openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES, cap_log, None);
            let (mats, b, _) = gen_p2(&maxg).unwrap_or_else(|_| panic!("P_2 does not fit even the largest node geometry"));
            let used = openvm_recursion_circuit::nv::circuit::natural_tight_heights(&mats, 2);
            let sha_used: usize = (0..openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES).map(|j| used[openvm_recursion_circuit::nv::circuit::sha_air_index(j)]).sum();
            let rows = b.instrs.len();
            drop(mats);
            let lg = |x: f64| (x.ceil() as usize).next_power_of_two().trailing_zeros() as usize;
            let mut pl = lg(rows as f64 * m).max(env_pair("NEARPROOF_TREE_NODE_GEOM", (20, 19)).1);
            let mut lr = lg(used[0] as f64 * m).max(pl + 1);
            let mut ks_ = ((sha_used as f64 * m) / (1usize << cap_log) as f64).ceil().max(1.0) as usize;
            println!("TREE_NODE2_SIZES rows={rows} nv_used={} sha_used={sha_used} -> geom=({lr},{pl},{ks_})", used[0]);
            loop {
                let c = circ(k, lr, pl, ks_, cap_log, None);
                match gen_p2(&c) {
                    Ok((mats, b, _)) => {
                        let rows = b.instrs.len();
                        let (pin, info) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
                        let sha_total: usize = (0..ks_).map(|j| pin[openvm_recursion_circuit::nv::circuit::sha_air_index(j)].1.unwrap()).sum();
                        println!("TREE_NODE2_PROBE geom=({lr},{pl},{ks_}) rows={rows} pin={pin:?} info={info:?}");
                        if (rows as f64 * m) > (1usize << pl) as f64 {
                            pl += 1;
                        } else if (pin[0].1.unwrap() as f64 * m) > (1usize << lr) as f64 {
                            lr += 1;
                        } else if (sha_total as f64 * m) > (ks_ << cap_log) as f64 {
                            ks_ += 1;
                        } else {
                            break Geom { log_rows: lr, prog_log: pl, sha_instances: ks_, heights: grow_pin(&pin, m, ks_, cap_log) };
                        }
                    }
                    Err(_) => panic!("P_2 does not fit the geometry ({lr},{pl},{ks_}) chosen from its sizes"),
                }
                assert!(lr <= cap_log && pl < lr && ks_ <= openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES, "no node geometry fits");
                if pl >= lr {
                    lr = pl + 1;
                }
            }
        }
    };
    println!("TREE_NODE_GEOM {node_geom:?}");
    let h_n = node_geom.heights.clone();
    let nc = circ(k, node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances, cap_log, Some(&h_n));
    // ---- PAD_N and P_2 program roots
    let pad_node_body = |b: &mut Builder, a: usize, level: u32| build_pad_node(b, &ctx, F::from_usize(a), &done, level);
    let (mats, b) = circ(k, node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances, cap_log, None).generate_with(|b| {
        pad_node_body(b, arity, 2);
    });
    let c_pad_node = program_commitment(parent.config(), &mats[0]);
    println!("TREE_PAD_NODE rows={}", b.instrs.len());
    // ---- levels
    let mut c_node2: Option<Digest> = None;
    let mut c_star: Option<Digest> = None;
    let mut node_rows = (0usize, 0usize);
    for lvl in 2..=depth as u32 + 1 {
        // children are at level lvl - 1: pad them to a multiple of the arity (level 1 is full)
        if lvl >= 3 {
            while items.len() % arity != 0 {
                let t0 = std::time::Instant::now();
                let a = items.last().unwrap().stmt.e.as_canonical_u32() as usize;
                let mut s = None;
                let (mats, b) = nc.generate_with(|b| {
                    s = Some(pad_node_body(b, a, lvl - 1));
                });
                assert!(b.failures.is_empty());
                let (v, p, _) = prove_mats(&nc, &parent, mats, &b);
                assert_eq!(vd::proof_heights(&p).unwrap(), h_n, "PAD_N: heights differ from the node pin");
                assert_eq!(root_of(&p), c_pad_node);
                let j = items.len();
                let bytes = save_proof(&out.join(format!("PADN{}_{j}.proof", lvl - 1)), &p);
                let sec = secs(t0);
                println!("TREE_PAD_NODE_PROVED L{}_{j} bytes={bytes} seconds={sec:.1}", lvl - 1);
                seconds.insert(format!("padn{}_{j}", lvl - 1), sec.into());
                kinds.entry("pad_node".into()).or_default().push(sec);
                n_proofs += 1;
                items.push(Item { vk: v, p, stmt: s.unwrap() });
            }
        }
        let mut next = vec![];
        for (j, grp) in items.chunks(arity).enumerate() {
            let t0 = std::time::Instant::now();
            let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = grp.iter().map(|x| (&x.vk, &x.p)).collect();
            let pre: Vec<RangeStmt> = grp.iter().map(|x| x.stmt.clone()).collect();
            let mut s = None;
            let gen_node = |c: &NvCircuit, s: &mut Option<RangeStmt>| {
                c.generate_with(|b| {
                    *s = Some(if lvl == 2 { build_node2(b, &refs, &pre, &set) } else { build_node_star(b, &refs, &pre, c_node2.unwrap(), c_pad_node) });
                })
            };
            // shape check first (natural heights at the node geometry): the pin must hold it
            let probe_n = circ(k, node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances, cap_log, None);
            let (pm, pb) = gen_node(&probe_n, &mut s);
            let (npin, info) = shape_pinned_heights(&pm, &pb, 2, FINAL_PIN_EPS_BITS);
            drop(pm);
            println!("TREE_NODE L{lvl}_{j} kind={} rows={} shape_pin={npin:?} info={info:?}", if lvl == 2 { "P2" } else { "Pstar" }, pb.instrs.len());
            assert!(fits(&npin, &h_n), "node L{lvl}_{j}: shape pin {npin:?} exceeds the node pin {h_n:?} (raise NEARPROOF_TREE_NODE_MARGIN)");
            let (mats, b) = gen_node(&nc, &mut s);
            assert!(b.failures.is_empty(), "node L{lvl}_{j}: {:?}", b.failures);
            if lvl == 2 { node_rows.0 = b.instrs.len() } else { node_rows.1 = b.instrs.len() }
            let (v, p, _) = prove_mats(&nc, &parent, mats, &b);
            assert_eq!(vd::proof_heights(&p).unwrap(), h_n);
            assert_eq!(p.public_values[0][0], F::from_u32(lvl), "node level");
            let r = root_of(&p);
            let slot = if lvl == 2 { &mut c_node2 } else { &mut c_star };
            assert!(slot.is_none_or(|c| c == r), "node programs differ within a shape");
            *slot = Some(r);
            let bytes = save_proof(&out.join(format!("NODE{lvl}_{j}.proof")), &p);
            let sec = secs(t0);
            println!("TREE_NODE_PROVED L{lvl}_{j} bytes={bytes} seconds={sec:.1}");
            seconds.insert(format!("node{lvl}_{j}"), sec.into());
            kinds.entry(if lvl == 2 { "node2" } else { "node_star" }.into()).or_default().push(sec);
            n_proofs += 1;
            if lvl == 2 && j == 0 {
                save_vk(&out.join("NODE.vk.json"), &v);
            }
            next.push(Item { vk: v, p, stmt: s.unwrap() });
        }
        items = next;
    }
    assert_eq!(items.len(), 1, "one root");
    let c_node2 = c_node2.unwrap();
    // [D-7] depth 1: the shape of a P_* over copies of the P_2 proof (statements do not chain: a
    // trace-shape measurement for the arity model, not a valid node)
    if depth == 1 && std::env::var("NEARPROOF_TREE_STAR_PROBE").is_ok_and(|v| v == "1") {
        let t0 = std::time::Instant::now();
        let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = (0..arity).map(|_| (&items[0].vk, &items[0].p)).collect();
        let pre: Vec<RangeStmt> = (0..arity).map(|_| items[0].stmt.clone()).collect();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let c = circ(k, node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances, cap_log, None);
            let (m, b) = c.generate_with(|b| {
                build_node_star(b, &refs, &pre, c_node2, c_pad_node);
            });
            let (pin, info) = shape_pinned_heights(&m, &b, 2, FINAL_PIN_EPS_BITS);
            println!("TREE_STAR_PROBE arity={arity} rows={} shape_pin={pin:?} info={info:?} fits_node_pin={} gen_s={:.1}", b.instrs.len(), fits(&pin, &h_n), secs(t0));
        }));
        if r.is_err() {
            println!("TREE_STAR_PROBE arity={arity} does not fit the node geometry {:?}", (node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances));
        }
    }
    let c_root = if depth == 1 { c_node2 } else { c_star.unwrap() };
    let root = items.pop().unwrap();
    // ---- wrap (final domain, zk-masked; heights pinned from the shape, F1(b))
    let t0 = std::time::Instant::now();
    let wrap_prog_log = std::env::var("NEARPROOF_WRAP_PROG_LOG").ok().map_or(18, |v| v.parse().unwrap());
    let mut wc = NvCircuit::new(k, WRAP_LOG_ROWS, 1);
    wc.prog_log = wrap_prog_log;
    let root_level = 1 + depth as u32;
    let wbody = |b: &mut Builder| {
        build_wrap(b, &root.vk, &root.p, root_level, c_root, &root.stmt);
    };
    let fparams = final_engine.config().params().clone();
    let wh: Vec<vd::PinnedHeight> = match &fixed {
        Some(f) => {
            assert_eq!(f.tree.c_node2, c_node2, "P_2 differs from the fixed setup's");
            assert_eq!(f.tree.c_node_star, c_star, "P_* differs from the fixed setup's");
            f.final_heights.clone()
        }
        None => {
            let (m, b) = wc.generate_with(wbody);
            let (pin, info) = shape_pinned_heights(&m, &b, fparams.l_skip, FINAL_PIN_EPS_BITS);
            println!("WRAP_SHAPE_PIN {pin:?} info={info:?}");
            pin
        }
    };
    wc.heights = Some(wh.iter().map(|&(l, _)| 1usize << l).collect());
    wc.tight_floor = Some(wh.iter().map(|&(l, tt)| tt.unwrap_or(1 << l)).collect());
    let (mats, b) = wc.generate_with(wbody);
    assert!(b.failures.is_empty(), "wrap: {:?}", b.failures);
    let wrap_rows = b.instrs.len();
    let (fv, fp, _) = prove_mats(&wc, &final_engine, mats, &b);
    assert_eq!(vd::proof_heights(&fp).as_ref(), Some(&wh), "wrap trace does not fit the pinned heights");
    let wsec = secs(t0);
    seconds.insert("wrap".into(), wsec.into());
    kinds.entry("wrap".into()).or_default().push(wsec);
    let program: Vec<[u32; 4]> = b.instrs.iter().map(|i| i.words()).collect();
    let tree = TreeShape {
        arity,
        depth,
        leaf: Geom { log_rows: leaf_log, prog_log: leaf_prog, sha_instances: 1, heights: h_l.clone() },
        node: node_geom.clone(),
        templates,
        c_pad_leaf,
        c_node2,
        c_pad_node,
        c_node_star: c_star,
        wrap_log_rows: WRAP_LOG_ROWS,
        wrap_prog_log,
    };
    let (_, base_u, _) = d0a_claim(air, public, chunk);
    let base_params: Vec<SystemParams> = classes.iter().map(|d| load_base(Path::new(d)).0.inner.params.clone()).collect();
    let setup = WrapSetup { version: SETUP_VERSION, domain_odd_factor: 15, air_sha256: hash(&std::fs::read(air).unwrap()), base_params, final_vk: fv, program, level: t::LEVEL_WRAP, final_heights: wh.clone(), tree };
    let vds = VdSetup { vk_final: setup.final_vk.clone(), program: setup.program.clone(), level: setup.level, heights: Some(wh.clone()) };
    let (claim, _, _) = d0a_claim(air, public, chunk);
    assert_eq!(t::ctx_of_digest(claim.digest()), ctx, "the template leaf's ctx is the chunk's claim digest");
    vd::verify_wrap(&vds, &final_engine, &ctx, class, &fp).expect("V_d (wrap)");
    for c in 0..setup.tree.templates.len() as u32 {
        if c != class {
            assert!(vd::verify_wrap(&vds, &final_engine, &ctx, c, &fp).is_err(), "wrong class accepted");
        }
    }
    let mut wrong = ctx.clone();
    wrong[0] += F::ONE;
    assert!(vd::verify_wrap(&vds, &final_engine, &wrong, class, &fp).is_err());
    let mut bad = vds.clone();
    bad.program[0][0] ^= 1;
    assert!(vd::verify_wrap(&bad, &final_engine, &ctx, class, &fp).is_err());
    let mut bad = vds.clone();
    bad.heights.as_mut().unwrap()[1].1 = Some(wh[1].1.unwrap() + 4);
    assert!(vd::verify_wrap(&bad, &final_engine, &ctx, class, &fp).is_err());
    let mut bad = vds.clone();
    bad.level += 1;
    assert!(vd::verify_wrap(&bad, &final_engine, &ctx, class, &fp).is_err());
    println!("WRAP_NEGATIVE_CONTROLS_OK wrong_ctx wrong_class changed_program changed_heights changed_level");
    let setup_bytes = serde_json::to_vec(&setup).unwrap();
    let pin = hash(&setup_bytes);
    if let Some(f) = &fixed {
        assert_eq!(serde_json::to_vec(f).unwrap(), setup_bytes, "the fixed setup must be reproduced byte for byte");
        println!("TREE_FIXED_SETUP_IDENTICAL");
    }
    std::fs::write(out.join("SETUP.json"), &setup_bytes).unwrap();
    std::fs::write(out.join("SETUP.sha256"), &pin).unwrap();
    let proof_bytes = save_proof(&out.join("WRAP.proof"), &fp);
    let hint = std::fs::read(chunk.join("hint.bin")).unwrap();
    let mut packet = MAGIC.to_vec();
    packet.extend_from_slice(&(hint.len() as u64).to_le_bytes());
    packet.extend_from_slice(&hint);
    packet.extend_from_slice(&class.to_le_bytes());
    packet.extend_from_slice(&(base_u.len() as u32).to_le_bytes());
    for &x in &base_u {
        for w in ef_words(x) {
            packet.extend_from_slice(&w.to_le_bytes());
        }
    }
    fp.encode(&mut packet).unwrap();
    std::fs::write(out.join("WRAP.bundle"), &packet).unwrap();
    let zk_masked = setup.final_vk.inner.params.whir.levers.zk == 6 && setup.base_params.iter().all(|p| p.whir.levers.zk >= 1);
    // the template set must be a function of the classes' shapes (ZK-ARGUMENT 7.1, 10.1):
    // * chain templates: every class's chain ran with shape floors at every level (review-D4 F2);
    // * base templates (review-D6 F5): every class's leaf program was reproduced by >= 2 independent
    //   base proofs (distinct base points u) at the class shape
    let shape_only: Vec<bool> = if base_tmpl {
        confirmed.iter().map(|&n| n >= 2).collect()
    } else {
        classes.iter().map(|d| std::fs::read_to_string(Path::new(d).join("chain.log")).is_ok_and(|s| s.contains("L1_SHAPE_FLOOR"))).collect()
    };
    let zk_ok = zk_masked && shape_only.iter().all(|&x| x);
    let abort_terms = if base_tmpl { 0 } else { target.entry.anchor.0 as usize } + n_proofs + 1;
    let zk_scope = if zk_ok {
        format!(
            "statistical zero knowledge of the tree-wrap packet for the statement (claim, hint, class, setup), classical programmable ROM: eps_ZK <= 2^-184.4 + {abort_terms} x 2^-192 (shape-pin aborts), ZK-ARGUMENT.md 6.4, 7.1, 10.1; for chunks whose base was proved at one of the setup's pinned base shape classes (the setup is one for all such chunks: a function of the classes, the arity and the depth); the packet reveals the class, i.e. the pinned per-AIR base row counts of that class (not the chunk's own); QROM: ZK-ARGUMENT.md 6.5 (the base point u is open)"
        )
    } else if zk_masked {
        format!("none: a template class is not shown shape-only {shape_only:?} (base: >= 2 base proofs per class; chain: shape floors)")
    } else {
        "none: wrap not zk-masked".into()
    };
    let kind_stats: serde_json::Map<String, serde_json::Value> =
        kinds.iter().map(|(k, v)| (k.clone(), serde_json::json!({"n": v.len(), "mean_s": v.iter().sum::<f64>() / v.len() as f64}))).collect();
    let result = serde_json::json!({
        "scope": "D0a template classes, chunk-independent tree (two node shapes, PAD at any level) + wrap (D-7)",
        "security_established": false,
        "zero_knowledge_established": zk_ok,
        "zero_knowledge_scope": zk_scope,
        "templates_shape_only": shape_only,
        "template_confirmations": confirmed,
        "template_kind": if base_tmpl { "base (the class base proof, build_base_leaf)" } else { "chain (the class chain L4, build_norm)" },
        "class": class, "arity": arity, "depth": depth, "tree_proofs": n_proofs,
        "wrap_proof_bytes": proof_bytes, "hint_bytes": hint.len(), "bundle_bytes": packet.len(),
        "setup_bytes": setup_bytes.len(), "setup_sha256": pin,
        "node2_program_rows": node_rows.0, "node_star_program_rows": node_rows.1, "wrap_program_rows": wrap_rows,
        "leaf_geom": setup.tree.leaf, "node_geom": setup.tree.node, "wrap_heights": wh,
        "seconds": seconds, "seconds_by_kind": kind_stats, "total_seconds": secs(t_all),
    });
    std::fs::write(out.join("RESULT.json"), serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    println!("TREE_WRAP_VERIFIED {result}");
}

fn try_decode_proof(b: &[u8]) -> Result<Proof<SC>, String> {
    let mut c = Cursor::new(b);
    let p = Proof::decode(&mut c).map_err(|e| format!("proof codec: {e:?}"))?;
    if c.position() as usize != b.len() {
        return Err("trailing proof bytes".into());
    }
    Ok(p)
}

fn rd_u32(b: &[u8], o: usize) -> Result<u32, String> {
    b.get(o..o + 4).map(|x| u32::from_le_bytes(x.try_into().unwrap())).ok_or_else(|| "truncated packet".to_string())
}

/// V_d over a tree-wrap packet; every malformed input is an `Err` (review-D5).
fn tree_verify_checked(air: &str, claim_path: &str, setup_path: &str, pin: &str, bundle: &str) -> Result<(usize, u32, [u64; 4], f64), String> {
    let setup_bytes = std::fs::read(setup_path).map_err(|e| format!("setup: {e}"))?;
    if hash(&setup_bytes) != pin {
        return Err("untrusted setup: hash differs from operator's pin".into());
    }
    let mut setup: WrapSetup = serde_json::from_slice(&setup_bytes).map_err(|e| format!("setup json: {e}"))?;
    if (setup.version, setup.domain_odd_factor) != (SETUP_VERSION, 15) {
        return Err("setup version / domain".into());
    }
    for p in setup.base_params.iter_mut() {
        p.whir.domain_odd_factor = setup.domain_odd_factor;
    }
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    let air_bytes = std::fs::read(air).map_err(|e| format!("air: {e}"))?;
    if hash(&air_bytes) != setup.air_sha256 {
        return Err("AIR differs from pinned setup".into());
    }
    let claim = std::fs::read(claim_path).map_err(|e| format!("claim: {e}"))?;
    let packet = std::fs::read(bundle).map_err(|e| format!("bundle: {e}"))?;
    if packet.len() < 16 || &packet[..8] != MAGIC {
        return Err("bundle framing".into());
    }
    let n = u64::from_le_bytes(packet[8..16].try_into().unwrap());
    if n > (packet.len() - 16) as u64 {
        return Err("truncated hint".into());
    }
    let n = n as usize;
    let mut body = 16 + n;
    let class = rd_u32(&packet, body)?;
    let base_params = setup.base_params.get(class as usize).ok_or("template class out of range")?.clone();
    body += 4;
    let m = rd_u32(&packet, body)? as usize;
    if m != base_params.n_stack + 1 {
        return Err("stacking point length".into());
    }
    body += 4;
    if packet.len() < body + 48 * m {
        return Err("truncated stacking point".into());
    }
    let mut u: Vec<Ef> = Vec::with_capacity(m);
    for i in 0..m {
        let o = body + 48 * i;
        let w: [u32; 12] = core::array::from_fn(|k| u32::from_le_bytes(packet[o + 4 * k..o + 4 * k + 4].try_into().unwrap()));
        if w.iter().any(|&x| x >= 0x7800_0001) {
            return Err("noncanonical stacking point coefficient".into());
        }
        u.push(ef_of_words(w));
    }
    body += 48 * m;
    let air_pub = npudr::airpub::AirPublic::from_json_slice(&air_bytes).map_err(|e| format!("air json: {e:?}"))?;
    let hint = packet[16..16 + n].to_vec();
    // the claim preparation is library code that panics on a claim / hint it rejects
    let expected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let public = public_data(&air_pub, &claim, &hint);
        state::chunk_bridge::expected_claim_parsed(&air_pub.table_num_pub, &public, base_params, Some(&u))
    }))
    .map_err(|_| "claim / hint rejected by the public-statement preparation".to_string())?;
    let ctx = t::ctx_of_digest(expected.digest());
    let fp = try_decode_proof(&packet[body..])?;
    let engine = Sha384CpuEngine::new_final(setup.final_vk.inner.params.clone());
    fs_jobs_reset();
    let t_v = std::time::Instant::now();
    let vds = VdSetup { vk_final: setup.final_vk, program: setup.program, level: setup.level, heights: Some(setup.final_heights) };
    // V_d checks the pinned heights before any other work on the proof; a panic inside the native
    // verifier on a malformed proof is still caught and reported as a rejection
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| vd::verify_wrap(&vds, &engine, &ctx, class, &fp)))
        .map_err(|_| "wrap verifier panicked on the proof".to_string())?
        .map_err(|e| format!("wrap verifier: {e}"))?;
    Ok((packet.len(), class, fs_jobs(), t_v.elapsed().as_secs_f64() * 1e3))
}

pub fn tree_verify(air: &str, claim_path: &str, setup_path: &str, pin: &str, bundle: &str) {
    let t_all = std::time::Instant::now();
    // malformed input must not abort with a panic message on stderr from a library: silence the
    // default hook for the checked body (rejections are reported below)
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = tree_verify_checked(air, claim_path, setup_path, pin, bundle);
    std::panic::set_hook(hook);
    match r {
        Ok((len, class, fs, wrap_ms)) => {
            println!(
                "VERIFY_PROFILE_MS total={:.2} wrap_verify={wrap_ms:.2} FS_JOBS flush={} commit={} squeeze={} pow={}",
                t_all.elapsed().as_secs_f64() * 1e3,
                fs[0],
                fs[1],
                fs[2],
                fs[3]
            );
            println!("INDEPENDENT_TREE_VERIFY_OK bundle_bytes={len} class={class}");
        }
        Err(e) => {
            println!("TREE_VERIFY_REJECT {e}");
            std::process::exit(1);
        }
    }
}

/// [E2E-D D-5, review-D4 F5] Count the Fiat-Shamir jobs `R` of one proof's native verification:
/// every SHA-384 evaluation of the transcript (flush, commit absorb, squeeze / PoW-run block,
/// PoW block), under the proof's own domain. `final` = the FINAL domain.
pub fn fs_count(vk_path: &str, proof_path: &str, final_domain: bool) {
    let vk = if vk_path.ends_with("SETUP.json") { setup_final_vk(vk_path) } else { read_vk(Path::new(vk_path)) };
    let p = if proof_path.ends_with(".bundle") {
        let b = std::fs::read(proof_path).unwrap();
        let n = usize::try_from(u64::from_le_bytes(b[8..16].try_into().unwrap())).unwrap();
        let mut body = 16 + n;
        if &b[..8] == MAGIC {
            body += 4; // template class
        }
        if &b[..8] != b"NPQCH01\0" {
            let m = u32::from_le_bytes(b[body..body + 4].try_into().unwrap()) as usize;
            body += 4 + 48 * m;
        }
        decode_proof(&b[body..])
    } else {
        read_proof(Path::new(proof_path))
    };
    let engine = if final_domain { Sha384CpuEngine::new_final(vk.inner.params.clone()) } else { Sha384CpuEngine::new(vk.inner.params.clone()) };
    fs_jobs_reset();
    let mut tr = engine.initial_transcript();
    let pts = openvm_stark_backend::verifier::verify_with_points(engine.config(), &vk, &p, &mut tr).expect("verify");
    let fs = fs_jobs();
    let total: u64 = fs.iter().sum();
    println!(
        "FS_COUNT file={proof_path} final={final_domain} total={total} flush={} commit={} squeeze_or_pow_run={} pow={} u_len={}",
        fs[0], fs[1], fs[2], fs[3], pts.u.len()
    );
}

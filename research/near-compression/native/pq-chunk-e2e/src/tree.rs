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
        tree::{self as t, build_base_leaf, build_node2, build_node_star_set, build_norm, build_pad, build_pad_node, build_wrap_set},
    },
    sha384::config::{Digest, F, fs_jobs, fs_jobs_reset},
};
use openvm_stark_backend::StarkProtocolConfig;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

const MAGIC: &[u8; 8] = b"NPQTW02\0";
const SETUP_VERSION: u32 = 6;

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
    /// [E2E-D D-8] the class's pinned TAPE shape `(log, classical (bus, len) keys)`, which V_d
    /// recomputes the TAPE under (`None`: the chunk's natural TAPE, D-5 .. D-7)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tape_pad: Option<(usize, Vec<(u16, usize)>)>,
    /// [E2E-D D-9] the class's leaf geometry family (index into `TreeShape::families`)
    #[serde(default)]
    pub family: u32,
}

fn tape_pad_of(e: &TemplateEntry) -> Option<state::TapePad> {
    e.tape_pad.clone().map(|(log, keys)| state::TapePad { log, keys })
}

/// A tree proof geometry: NvAir rows 2^log_rows, program 2^prog_log, SHA instances, pinned heights.
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct Geom {
    pub log_rows: usize,
    pub prog_log: usize,
    pub sha_instances: usize,
    pub heights: Vec<vd::PinnedHeight>,
}

/// [E2E-D D-9] One leaf geometry family: the classes whose leaves are proved at this geometry, its
/// `PAD_L` program and its `P_2` program (the node over `arity` leaves of this geometry, proved at
/// the shared node heights). D-8 had one family: the largest class's leaf set every leaf's heights.
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct LeafFamily {
    pub leaf: Geom,
    pub classes: Vec<u32>,
    pub c_pad_leaf: Digest,
    pub c_node2: Digest,
}

/// Audit content of the wrap setup: everything the wrap program embeds (V_d reads none of it).
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct TreeShape {
    pub arity: usize,
    pub depth: usize,
    /// [E2E-D D-9] leaf geometry families, each with its own `PAD_L` and `P_2`; every node of any
    /// family is at the one node geometry, so the wrap is one program over `{C_2^f}` (depth 1)
    /// and `P_*` one program over `{C_2^f} ∪ {C_padN}` (levels >= 3)
    pub families: Vec<LeafFamily>,
    pub node: Geom,
    pub templates: Vec<TemplateEntry>,
    pub c_pad_node: Digest,
    /// `C_*` (None at depth 1: no level >= 3)
    pub c_node_star: Option<Digest>,
    pub wrap_log_rows: usize,
    pub wrap_prog_log: usize,
    /// [E2E-D D-8] the leaves' own proof geometry `(n_stack, log_blowup)` when it differs from the
    /// tree layer's (`NEARPROOF_TREE_LEAF_PARAMS`); `None`: the tree geometry (D-5 .. D-7)
    #[serde(default)]
    pub leaf_params: Option<(usize, usize)>,
    /// [E2E-D D-9, review-D8 L1] the tree layer's geometry `(n_stack, log_blowup)`
    /// (`NEARPROOF_TREE_GEOM` when the setup was made), so `tree-audit` reads it from the setup
    #[serde(default)]
    pub tree_geom: Option<(usize, usize)>,
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

/// [E2E-D D-8] The default tree arity (D-7: arity 4 has the least CPU work and the shortest
/// projected latency at 1 Pgas; `tree-prove ... default DEPTH ...` or `ARITY` = `-`).
pub const DEFAULT_ARITY: usize = 4;

/// [E2E-D D-8] The node-height margin for depth >= 2 (`h_N` = `P_2`'s shape pin x margin must hold
/// `P_*` and `PAD_N`). D-7 measured `P_*` over `P_2` (NvAir tight / SHA total): arity 2 +4 %,
/// arity 4 +12.3 % / +9.8 %, arity 8 +26.6 % / +20.8 % (children at node heights with more SHA
/// instances); the margin is 1 % over a linear fit, never below the D-5..D-7 1.10:
/// `max(1.10, 1.01 + 0.04 (arity - 1))` = 1.10 (2, 3), 1.13 (4), 1.29 (8). Above arity 8 the
/// margin must be given (`NEARPROOF_TREE_NODE_MARGIN`), as for any override.
pub fn node_margin(arity: usize) -> f64 {
    if let Ok(v) = std::env::var("NEARPROOF_TREE_NODE_MARGIN") {
        return v.parse().expect("NEARPROOF_TREE_NODE_MARGIN");
    }
    assert!(arity <= 8, "no measured P_* margin above arity 8: set NEARPROOF_TREE_NODE_MARGIN");
    let m: f64 = 1.01 + 0.04 * (arity as f64 - 1.0);
    (m.max(1.10) * 100.0).round() / 100.0
}

fn env_pair(name: &str, d: (usize, usize)) -> (usize, usize) {
    std::env::var(name).ok().map_or(d, |v| {
        let x: Vec<usize> = v.split(',').map(|s| s.trim().parse().unwrap()).collect();
        (x[0], x[1])
    })
}

pub(crate) fn circ(k: usize, log_rows: usize, prog_log: usize, sha: usize, cap_log: usize, h: Option<&[vd::PinnedHeight]>) -> NvCircuit {
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

pub(crate) fn fits(nat: &[vd::PinnedHeight], pin: &[vd::PinnedHeight]) -> bool {
    nat.len() == pin.len() && nat.iter().zip(pin).all(|(a, b)| a.0 <= b.0 && a.1.unwrap_or(1 << a.0) <= b.1.unwrap_or(1 << b.0))
}

/// Per-AIR maximum of several pins (same AIR set).
pub(crate) fn max_pin(pins: &[Vec<vd::PinnedHeight>]) -> Vec<vd::PinnedHeight> {
    (0..pins[0].len())
        .map(|a| {
            let l = pins.iter().map(|p| p[a].0).max().unwrap();
            let t = pins.iter().map(|p| p[a].1.unwrap_or(1 << p[a].0)).max().unwrap();
            (l, Some(t))
        })
        .collect()
}

/// Grow a pin by `margin` (NvAir tight; SHA total, redistributed over `k` instances of 2^cap_log).
pub(crate) fn grow_pin(p: &[vd::PinnedHeight], margin: f64, k: usize, cap_log: usize) -> Vec<vd::PinnedHeight> {
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
    let c = state::chunk_bridge::expected_claim_at_padded(air, public, params.clone(), &u, state::TapePad::of_dir(dir).as_ref());
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
    let tape_pad = state::TapePad::of_dir(dir).map(|t| (t.log, t.keys));
    let entry = TemplateEntry { class, kind: if base_tmpl { "base" } else { "chain" }.into(), base_vk_sha256, base_heights, anchor, c_norm, tape_pad, family: 0 };
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
    // [E2E-D D-8] the leaves' proof geometry (a setup constant): leaves are proved once per segment
    // and verified only by P_2, so they can run at a lower rate than the nodes (cheaper commitment,
    // more queries for P_2 to verify): NEARPROOF_TREE_LEAF_PARAMS=nsXXlbY (same stacked height as
    // the tree layer, so the SHA instance cap is unchanged); default: the tree geometry.
    let leaf_params: Option<(usize, usize)> = match &fixed {
        Some(f) => f.tree.leaf_params,
        None => std::env::var("NEARPROOF_TREE_LEAF_PARAMS").ok().map(|v| profile::parse_geom(&v)),
    };
    let lparams = match leaf_params {
        Some(g) => profile::params_geom(false, certs, exclusions, g),
        None => parent.config().params().clone(),
    };
    assert_eq!((lparams.l_skip + lparams.n_stack, lparams.k_whir()), (cap_log, k), "leaf geometry: stacked height and fold must equal the tree layer's");
    println!(
        "TREE_LEAF_PARAMS n_stack={} log_blowup={} queries={:?}",
        lparams.n_stack,
        lparams.log_blowup,
        lparams.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>()
    );
    let leaf_engine = Sha384CpuEngine::new(lparams);
    let base_tmpl = template_kind_base();
    let margin: f64 = node_margin(arity);
    println!("TREE_SHAPE arity={arity} depth={depth} node_margin={margin}");
    let mut seconds = serde_json::Map::new();
    let mut kinds: std::collections::BTreeMap<String, Vec<f64>> = Default::default();
    // ---- [E2E-D D-9] leaf geometry families (setup constants: the leaf programs depend on them).
    // NEARPROOF_TREE_LEAF_FAMILIES=auto (default): each class's leaf at the smallest geometry that
    // holds it (program 2^pl >= its rows, NvAir 2^lr >= its NvAir rows, lr > pl), classes of equal
    // geometry share a family; =one: every class at NEARPROOF_TREE_LEAF_GEOM (D-8: one family, the
    // largest class's leaf sets every leaf's heights).
    let lg2 = |x: usize| x.max(1).next_power_of_two().trailing_zeros() as usize;
    let leaf_sha_env = std::env::var("NEARPROOF_TREE_LEAF_SHA").ok().map_or(1, |v| v.parse().unwrap());
    let one_family = match std::env::var("NEARPROOF_TREE_LEAF_FAMILIES").as_deref() {
        Ok("auto") | Err(_) => false,
        Ok("one") => true,
        Ok(o) => panic!("unknown NEARPROOF_TREE_LEAF_FAMILIES {o}"),
    };
    // per family: (log_rows, prog_log, sha_instances); per class: its family
    let (fam_geoms, class_family): (Vec<(usize, usize, usize)>, Vec<usize>) = match &fixed {
        Some(f) => {
            assert_eq!(f.tree.templates.len(), classes.len(), "class count differs from the fixed setup's");
            (
                f.tree.families.iter().map(|x| (x.leaf.log_rows, x.leaf.prog_log, x.leaf.sha_instances)).collect(),
                f.tree.templates.iter().map(|e| e.family as usize).collect(),
            )
        }
        None => {
            let cg: Vec<(usize, usize, usize)> = if one_family {
                let (l, p) = env_pair("NEARPROOF_TREE_LEAF_GEOM", (19, 18));
                vec![(l, p, leaf_sha_env); classes.len()]
            } else {
                let probe = circ(k, cap_log - 1, cap_log - 2, leaf_sha_env, cap_log, None);
                classes
                    .iter()
                    .enumerate()
                    .map(|(i, dir)| {
                        let tm = template_of(Path::new(dir), i as u32, base_tmpl, &chain_engine, &leaf_engine, &probe);
                        let pl = lg2(tm.rows);
                        let lr = lg2(tm.pin[0].1.unwrap()).max(pl + 1);
                        println!("TREE_LEAF_FAMILY_PROBE class={i} rows={} nv_tight={} -> leaf geometry ({lr},{pl},{leaf_sha_env})", tm.rows, tm.pin[0].1.unwrap());
                        (lr, pl, leaf_sha_env)
                    })
                    .collect()
            };
            let mut fg = cg.clone();
            fg.sort();
            fg.dedup();
            let cf = cg.iter().map(|g| fg.iter().position(|x| x == g).unwrap()).collect();
            (fg, cf)
        }
    };
    let n_fam = fam_geoms.len();
    let probe_f: Vec<NvCircuit> = fam_geoms.iter().map(|&(l, p, s)| circ(k, l, p, s, cap_log, None)).collect();
    println!("TREE_LEAF_FAMILIES {fam_geoms:?} class_family={class_family:?}");
    // ---- templates: one leaf program per class (at its family's geometry); the chunk's own
    // template must equal one of them
    let mut tmpls: Vec<Tmpl> = vec![];
    for (i, dir) in classes.iter().enumerate() {
        let t0 = std::time::Instant::now();
        let mut tm = template_of(Path::new(dir), i as u32, base_tmpl, &chain_engine, &leaf_engine, &probe_f[class_family[i]]);
        tm.entry.family = class_family[i] as u32;
        println!(
            "TREE_TEMPLATE class={i} family={} kind={} rows={} pin={:?} base_vk={} s={:.1}",
            class_family[i],
            tm.entry.kind,
            tm.rows,
            tm.pin,
            &tm.entry.base_vk_sha256[..16],
            secs(t0)
        );
        tmpls.push(tm);
    }
    // [E2E-D D-9, review-D8 M1 / M2] every class's base key rebuilt from the declared AIR, its
    // TAPE pad and the calibration for its shape, compared byte for byte (not only its hash)
    for (i, (tm, dir)) in tmpls.iter().zip(classes).enumerate() {
        let (bvk, _) = load_base(Path::new(dir));
        let pad_dir = state::TapePad::of_dir(Path::new(dir)).map(|t| (t.log, t.keys));
        assert_eq!(pad_dir, tm.entry.tape_pad, "class {i}: TAPE_PAD.json");
        class_key_check(air, certs, exclusions, &bvk, &bvk.inner.params, &tm.entry.base_heights, tm.entry.tape_pad.as_ref())
            .unwrap_or_else(|e| panic!("class {i} ({dir}): {e}"));
        println!("TREE_CLASS_KEY_REBUILT class={i}");
    }
    // confirmations (review-D6 F5): every base proof given for a class (the class dir, the chunk,
    // NEARPROOF_TREE_CONFIRM dirs) must yield that class's template; count base proofs that are
    // distinct in both the base point u and the chunk (its claim digest ctx; review-D7 L2: two base
    // proofs of one chunk are not two chunks)
    let ctx_dir = |d: &Path, public: &str| -> Vec<F> { t::ctx_of_digest(d0a_claim(air, public, d).0.digest()) };
    let mut confirm: Vec<Vec<(Vec<Ef>, Vec<F>)>> =
        tmpls.iter().zip(classes).map(|(t, d)| vec![(t.u.clone(), ctx_dir(Path::new(d), &Path::new(d).join("public").to_string_lossy()))]).collect();
    let add_confirm = |v: &mut Vec<(Vec<Ef>, Vec<F>)>, u: Vec<Ef>, x: Vec<F>| {
        if v.iter().all(|(u0, x0)| *u0 != u && *x0 != x) {
            v.push((u, x));
        }
    };
    let match_class = |tm: &Tmpl, tmpls: &[Tmpl]| -> Option<usize> {
        tmpls.iter().position(|c| c.entry.c_norm == tm.entry.c_norm && c.entry.base_vk_sha256 == tm.entry.base_vk_sha256 && c.entry.base_heights == tm.entry.base_heights && c.entry.tape_pad == tm.entry.tape_pad)
    };
    // [E2E-D D-9] a base dir is tried only as the classes whose base vk it has, each at its family's
    // geometry (another family's leaf geometry may not hold its leaf program: no panic, no match)
    let try_class = |dir: &Path, c: usize| -> Option<Tmpl> {
        if vk_sha(&load_base(dir).0) != tmpls[c].entry.base_vk_sha256 {
            return None;
        }
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| template_of(dir, c as u32, base_tmpl, &chain_engine, &leaf_engine, &probe_f[class_family[c]]))).ok()
    };
    let extra: Vec<String> = std::env::var("NEARPROOF_TREE_CONFIRM").map(|v| v.split_whitespace().map(String::from).collect()).unwrap_or_default();
    for dir in &extra {
        // the class index is a program constant of the leaf: try each (at that class's family)
        let hit = (0..tmpls.len()).find_map(|c| {
            let tm = try_class(Path::new(dir), c)?;
            (match_class(&tm, &tmpls) == Some(c)).then_some((c, tm.u))
        });
        let (c, u) = hit.unwrap_or_else(|| panic!("confirmation {dir}: its template is no class's"));
        let x = ctx_dir(Path::new(dir), &Path::new(dir).join("public").to_string_lossy());
        add_confirm(&mut confirm[c], u, x);
        println!("TREE_TEMPLATE_CONFIRMED class={c} by={dir}");
    }
    let (class, target) = (0..tmpls.len())
        .find_map(|c| {
            let tm = try_class(chunk, c)?;
            (match_class(&tm, &tmpls) == Some(c)).then_some((c, tm))
        })
        .expect("the chunk's template leaf is no class's: its base is not at a class shape");
    add_confirm(&mut confirm[class], target.u.clone(), ctx_dir(chunk, public));
    let fam = class_family[class];
    let class = class as u32;
    let templates: Vec<TemplateEntry> = tmpls.iter().map(|t| t.entry.clone()).collect();
    let confirmed: Vec<usize> = confirm.iter().map(Vec::len).collect();
    println!("TREE_CHUNK_CLASS class={class} family={fam} confirmations_per_class={confirmed:?}");
    let ctx: Vec<F> = if base_tmpl { t::ctx_of_digest(d0a_claim(air, public, chunk).0.digest()) } else { target.p.public_values[0][1..19].to_vec() };
    let done = vec![F::from_u32(t::PHASE_DONE), F::from_u32(class)];
    // ---- PAD_L, one program per family (its ctx / a / s are witnesses: one program per geometry)
    let mut c_pad_leaf: Vec<Digest> = vec![];
    let mut pad_pins: Vec<Vec<vd::PinnedHeight>> = vec![];
    for (f, pc) in probe_f.iter().enumerate() {
        let (mats, b) = pc.generate_with(|b| {
            build_pad(b, &ctx, F::ONE, &done);
        });
        c_pad_leaf.push(program_commitment(leaf_engine.config(), &mats[0]));
        let (pad_pin, _) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
        println!("TREE_PAD_LEAF family={f} rows={} pin={pad_pin:?}", b.instrs.len());
        pad_pins.push(pad_pin);
    }
    // P_2^f's template set: the family's classes (class order), then its PAD_L
    let sets: Vec<Vec<Digest>> = (0..n_fam)
        .map(|f| {
            let mut s: Vec<Digest> = templates.iter().filter(|e| e.family as usize == f).map(|e| e.c_norm).collect();
            s.push(c_pad_leaf[f]);
            s
        })
        .collect();
    let h_ls: Vec<Vec<vd::PinnedHeight>> = match &fixed {
        Some(f) => {
            assert_eq!(f.tree.templates, templates, "template set differs from the fixed setup's");
            for (g, x) in f.tree.families.iter().enumerate() {
                assert_eq!(x.c_pad_leaf, c_pad_leaf[g], "PAD_L of family {g} differs from the fixed setup's");
                assert_eq!(x.classes, (0..classes.len() as u32).filter(|&c| class_family[c as usize] == g).collect::<Vec<_>>(), "family {g} classes");
            }
            assert_eq!((f.tree.arity, f.tree.depth), (arity, depth), "tree shape differs from the fixed setup's");
            if std::env::var("NEARPROOF_TREE_TEMPLATES_ONLY").is_ok_and(|v| v == "1") {
                println!("TREE_TEMPLATES_MATCH_FIXED_SETUP classes={}", templates.len());
                return;
            }
            f.tree.families.iter().map(|x| x.leaf.heights.clone()).collect()
        }
        None => (0..n_fam)
            .map(|f| {
                let mut pins: Vec<_> = tmpls.iter().zip(&class_family).filter(|(_, cf)| **cf == f).map(|(t, _)| t.pin.clone()).collect();
                pins.push(pad_pins[f].clone());
                max_pin(&pins)
            })
            .collect(),
    };
    for (f, h) in h_ls.iter().enumerate() {
        println!("TREE_LEAF_HEIGHTS family={f} {h:?}");
    }
    drop(tmpls);
    let set = sets[fam].clone();
    let h_l = h_ls[fam].clone();
    let (leaf_log, leaf_prog, leaf_sha) = fam_geoms[fam];
    let want_root = |i: usize| -> Digest { if i == 0 { templates[class as usize].c_norm } else { c_pad_leaf[fam] } };
    // ---- leaves (the chunk's family)
    let lc = circ(k, leaf_log, leaf_prog, leaf_sha, cap_log, Some(&h_l));
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
                if leaf_engine.verify(&v, &p).is_ok()
                    && vd::proof_heights(&p).as_ref() == Some(&h_l)
                    && root_of(&p) == want_root(i)
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
        let (v, p, _) = prove_mats(&lc, &leaf_engine, mats, &b);
        assert_eq!(vd::proof_heights(&p).unwrap(), h_l, "leaf {i}: heights differ from the leaf pin");
        assert_eq!(root_of(&p), want_root(i), "leaf {i}: program root not its template's");
        let stmt = s.unwrap();
        assert!(openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], &stmt));
        let bytes = save_proof(&out.join(format!("LEAF{i}.proof")), &p);
        let sec = secs(t0);
        println!("TREE_LEAF {i} family={fam} rows={} bytes={bytes} seconds={sec:.1}", b.instrs.len());
        seconds.insert(format!("leaf{i}"), sec.into());
        kinds.entry(if i == 0 { "leaf_template" } else { "pad_leaf" }.into()).or_default().push(sec);
        if i == 0 {
            save_vk(&out.join("LEAF.vk.json"), &v);
        }
        n_proofs += 1;
        items.push(Item { vk: v, p, stmt });
        // [E2E-D D-8] NEARPROOF_TREE_LEAF_ONLY=1: stop after the template leaf (leaf-cost measurement)
        if i == 0 && std::env::var("NEARPROOF_TREE_LEAF_ONLY").is_ok_and(|v| v == "1") {
            println!("TREE_LEAF_ONLY_DONE heights={h_l:?} sha_instances={leaf_sha}");
            return;
        }
    }
    // ---- [E2E-D D-9] P_2 inputs per family: the chunk's family over its real leaves; at setup
    // creation every other family over `arity` copies of one PAD_L proof at that family's leaf
    // heights (P_2's program is a function of its children's geometry, not of their values: the
    // probe's program root is checked against the real P_2 of the chunk's own family below, and a
    // fixed-setup run of a chunk of the other family proves its real P_2 against the setup's root)
    type Kids = Vec<(MultiStarkVerifyingKey<SC>, Proof<SC>)>;
    let mut p2_in: Vec<Option<(Kids, Vec<RangeStmt>)>> = vec![None; n_fam];
    p2_in[fam] = Some((items.iter().map(|x| (x.vk.clone(), x.p.clone())).collect(), items.iter().map(|x| x.stmt.clone()).collect()));
    if fixed.is_none() {
        for f in (0..n_fam).filter(|&f| f != fam) {
            let t0 = std::time::Instant::now();
            let (l, pl, sh) = fam_geoms[f];
            let lcf = circ(k, l, pl, sh, cap_log, Some(&h_ls[f]));
            let mut s = None;
            let (mats, b) = lcf.generate_with(|b| {
                s = Some(build_pad(b, &ctx, F::ONE, &done));
            });
            assert!(b.failures.is_empty(), "family {f} PAD_L probe: {:?}", b.failures);
            let (v, p, _) = prove_mats(&lcf, &leaf_engine, mats, &b);
            assert_eq!(vd::proof_heights(&p).unwrap(), h_ls[f], "family {f} PAD_L probe heights");
            assert_eq!(root_of(&p), c_pad_leaf[f]);
            let s = s.unwrap();
            let sec = secs(t0);
            println!("TREE_FAMILY_PAD_PROBE family={f} seconds={sec:.1}");
            seconds.insert(format!("family{f}_pad_probe"), sec.into());
            p2_in[f] = Some(((0..arity).map(|_| (v.clone(), p.clone())).collect(), vec![s; arity]));
        }
    }
    let gen_p2 = |c: &NvCircuit, f: usize| -> std::thread::Result<(Vec<p3_matrix::dense::RowMajorMatrix<F>>, Builder, RangeStmt)> {
        let (kids, pre) = p2_in[f].as_ref().expect("P_2 input of this family");
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = kids.iter().map(|(a, b)| (a, b)).collect();
            let mut s = None;
            let (m, b) = c.generate_with(|b| {
                s = Some(build_node2(b, &refs, pre, &sets[f]));
            });
            (m, b, s.unwrap())
        }))
    };
    // ---- node geometry: from every family's P_2 (setup creation) or the fixed setup
    let node_geom: Geom = match &fixed {
        Some(f) => f.tree.node.clone(),
        None => {
            let m = if depth >= 2 { margin } else { 1.0 };
            // sizes at the largest geometry (max over the families), then the smallest geometry
            // holding every family's P_2 with the margin
            let maxg = circ(k, cap_log, cap_log - 1, openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES, cap_log, None);
            let (mut rows, mut nv_used, mut sha_used) = (0usize, 0usize, 0usize);
            for f in 0..n_fam {
                let (mats, b, _) = gen_p2(&maxg, f).unwrap_or_else(|_| panic!("P_2 (family {f}) does not fit even the largest node geometry"));
                let used = openvm_recursion_circuit::nv::circuit::natural_tight_heights(&mats, 2);
                let su: usize = (0..openvm_recursion_circuit::nv::circuit::MAX_SHA_INSTANCES).map(|j| used[openvm_recursion_circuit::nv::circuit::sha_air_index(j)]).sum();
                println!("TREE_NODE2_SIZES family={f} rows={} nv_used={} sha_used={su}", b.instrs.len(), used[0]);
                rows = rows.max(b.instrs.len());
                nv_used = nv_used.max(used[0]);
                sha_used = sha_used.max(su);
            }
            let lg = |x: f64| (x.ceil() as usize).next_power_of_two().trailing_zeros() as usize;
            let mut pl = lg(rows as f64 * m).max(env_pair("NEARPROOF_TREE_NODE_GEOM", (20, 19)).1);
            let mut lr = lg(nv_used as f64 * m).max(pl + 1);
            let mut ks_ = ((sha_used as f64 * m) / (1usize << cap_log) as f64).ceil().max(1.0) as usize;
            println!("TREE_NODE2_SIZES max rows={rows} nv_used={nv_used} sha_used={sha_used} -> geom=({lr},{pl},{ks_})");
            loop {
                let c = circ(k, lr, pl, ks_, cap_log, None);
                let mut pins = vec![];
                let mut rows = 0usize;
                for f in 0..n_fam {
                    let (mats, b, _) = gen_p2(&c, f).unwrap_or_else(|_| panic!("P_2 (family {f}) does not fit the geometry ({lr},{pl},{ks_}) chosen from its sizes"));
                    let (pin, info) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
                    println!("TREE_NODE2_PROBE family={f} geom=({lr},{pl},{ks_}) rows={} pin={pin:?} info={info:?}", b.instrs.len());
                    rows = rows.max(b.instrs.len());
                    pins.push(pin);
                }
                let pin = max_pin(&pins);
                let sha_total: usize = (0..ks_).map(|j| pin[openvm_recursion_circuit::nv::circuit::sha_air_index(j)].1.unwrap()).sum();
                if (rows as f64 * m) > (1usize << pl) as f64 {
                    pl += 1;
                } else if (pin[0].1.unwrap() as f64 * m) > (1usize << lr) as f64 {
                    lr += 1;
                } else if (sha_total as f64 * m) > (ks_ << cap_log) as f64 {
                    ks_ += 1;
                } else {
                    break Geom { log_rows: lr, prog_log: pl, sha_instances: ks_, heights: grow_pin(&pin, m, ks_, cap_log) };
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
    // ---- P_2 program roots per family: computed at setup creation (the other families from their
    // probes), from the fixed setup otherwise (the chunk's own family re-derived by its real P_2)
    let c_node2s: Vec<Digest> = match &fixed {
        Some(f) => f.tree.families.iter().map(|x| x.c_node2).collect(),
        None => (0..n_fam)
            .map(|f| {
                let probe = circ(k, node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances, cap_log, None);
                let (mats, _, _) = gen_p2(&probe, f).unwrap_or_else(|_| panic!("P_2 (family {f}) at the node geometry"));
                let c = program_commitment(parent.config(), &mats[0]);
                println!("TREE_NODE2_PROGRAM family={f} root={:?}", &c);
                c
            })
            .collect(),
    };
    drop(p2_in);
    // ---- PAD_N program root
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
                    *s = Some(if lvl == 2 { build_node2(b, &refs, &pre, &set) } else { build_node_star_set(b, &refs, &pre, &c_node2s, c_pad_node) });
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
            if lvl == 2 {
                assert_eq!(r, c_node2s[fam], "P_2 (family {fam}): program root differs from the setup's / the family probe's");
            }
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
    // [D-7] depth 1: the shape of a P_* over copies of the P_2 proof (statements do not chain: a
    // trace-shape measurement for the arity model, not a valid node)
    if depth == 1 && std::env::var("NEARPROOF_TREE_STAR_PROBE").is_ok_and(|v| v == "1") {
        let t0 = std::time::Instant::now();
        let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = (0..arity).map(|_| (&items[0].vk, &items[0].p)).collect();
        let pre: Vec<RangeStmt> = (0..arity).map(|_| items[0].stmt.clone()).collect();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let c = circ(k, node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances, cap_log, None);
            let (m, b) = c.generate_with(|b| {
                build_node_star_set(b, &refs, &pre, &c_node2s, c_pad_node);
            });
            let (pin, info) = shape_pinned_heights(&m, &b, 2, FINAL_PIN_EPS_BITS);
            println!("TREE_STAR_PROBE arity={arity} rows={} shape_pin={pin:?} info={info:?} fits_node_pin={} gen_s={:.1}", b.instrs.len(), fits(&pin, &h_n), secs(t0));
        }));
        if r.is_err() {
            println!("TREE_STAR_PROBE arity={arity} does not fit the node geometry {:?}", (node_geom.log_rows, node_geom.prog_log, node_geom.sha_instances));
        }
    }
    // the wrap's root set: every family's P_2 at depth 1, C_* above
    let c_roots: Vec<Digest> = if depth == 1 { c_node2s.clone() } else { vec![c_star.unwrap()] };
    let root = items.pop().unwrap();
    // ---- wrap (final domain, zk-masked; heights pinned from the shape, F1(b))
    let t0 = std::time::Instant::now();
    let wrap_prog_log = std::env::var("NEARPROOF_WRAP_PROG_LOG").ok().map_or(18, |v| v.parse().unwrap());
    let mut wc = NvCircuit::new(k, WRAP_LOG_ROWS, 1);
    wc.prog_log = wrap_prog_log;
    let root_level = 1 + depth as u32;
    let wbody = |b: &mut Builder| {
        build_wrap_set(b, &root.vk, &root.p, root_level, &c_roots, &root.stmt);
    };
    let fparams = final_engine.config().params().clone();
    let wh: Vec<vd::PinnedHeight> = match &fixed {
        Some(f) => {
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
    let families: Vec<LeafFamily> = (0..n_fam)
        .map(|f| LeafFamily {
            leaf: Geom { log_rows: fam_geoms[f].0, prog_log: fam_geoms[f].1, sha_instances: fam_geoms[f].2, heights: h_ls[f].clone() },
            classes: (0..classes.len() as u32).filter(|&c| class_family[c as usize] == f).collect(),
            c_pad_leaf: c_pad_leaf[f],
            c_node2: c_node2s[f],
        })
        .collect();
    let tree = TreeShape {
        arity,
        depth,
        families,
        node: node_geom.clone(),
        templates,
        c_pad_node,
        c_node_star: c_star,
        wrap_log_rows: WRAP_LOG_ROWS,
        wrap_prog_log,
        leaf_params,
        tree_geom: Some(profile::tree_geom()),
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
    // [E2E-D D-8, review-D7 L3] ship the class base vks with the setup (CLASS{i}.BASE.vk.json), so
    // `tree-audit` can check the setup against them
    for (i, d) in classes.iter().enumerate() {
        std::fs::copy(Path::new(d).join("BASE.vk.json"), out.join(format!("CLASS{i}.BASE.vk.json"))).unwrap();
    }
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
        "scope": "D0a template classes, chunk-independent tree (two node shapes, PAD at any level, one leaf geometry per family: D-9) + wrap",
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
        "family": fam, "leaf_families": setup.tree.families.len(),
        "leaf_geom": setup.tree.families[fam].leaf, "node_geom": setup.tree.node, "wrap_heights": wh,
        "seconds": seconds, "seconds_by_kind": kind_stats, "total_seconds": secs(t_all),
    });
    std::fs::write(out.join("RESULT.json"), serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    println!("TREE_WRAP_VERIFIED {result}");
}

/// [E2E-D D-9, review-D8 M1 / M2] A class's base key, rebuilt and compared: the TAPE pad is
/// well formed (sorted, unique keys) and its log is the class's TAPE log; the base parameters are
/// the stack's calibration for the class's pinned shape (n_stack, w_stack, degree from the class
/// log heights and the pad; the class's own log blowup) at the pinned per-round target; the base vk
/// is, byte for byte, the key of the declared AIR + the pad's TAPE at those parameters (so the vk's
/// constraints and the TAPE interactions are the AIR's and the pad's, not just its hash).
fn class_key_check(
    air: &str,
    certs: &str,
    exclusions: &str,
    vk: &MultiStarkVerifyingKey<SC>,
    params: &SystemParams,
    heights: &[vd::PinnedHeight],
    tape_pad: Option<&(usize, Vec<(u16, usize)>)>,
) -> Result<(), String> {
    let (log, keys) = tape_pad.ok_or("no TAPE pad: a class must pin its TAPE shape (D-8+)")?;
    let pad = state::TapePad { log: *log, keys: keys.clone() };
    pad.validate()?;
    if heights.last().map(|h| h.0) != Some(pad.log) {
        return Err(format!("TAPE pad log {} != the class's TAPE log {:?}", pad.log, heights.last()));
    }
    let logs: Vec<usize> = heights.iter().map(|h| h.0).collect();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let (n_stack, w_stack, degree) = state::chunk_bridge::class_base_shape(air, &logs, &pad);
        let mut p = profile::shaped_params_lb(false, n_stack, w_stack, degree, params.log_blowup, certs, exclusions);
        p.whir.domain_odd_factor = params.whir.domain_odd_factor;
        let vk2 = state::chunk_bridge::class_base_vk(air, p.clone(), &pad);
        (p, vk2)
    }))
    .map_err(|_| "rebuilding the class key panicked".to_string())?;
    let (p, vk2) = r;
    if serde_json::to_value(&p).unwrap() != serde_json::to_value(params).unwrap() {
        return Err(format!("base parameters are not the calibration for the class shape (rebuilt n_stack {} w_stack {} lb {})", p.n_stack, p.w_stack, p.log_blowup));
    }
    if serde_json::to_vec(&vk2).unwrap() != serde_json::to_vec(vk).unwrap() {
        return Err("base vk differs from the key of the declared AIR + TAPE pad at the class parameters".into());
    }
    Ok(())
}

/// [E2E-D D-8 .. D-9] `tree-audit AIR SETUP.json CERTS EXCLUSIONS VK_DIR [BASE_DIR...]`: check a
/// tree setup against the declared AIR and its shipped class base vks (VK_DIR/CLASS{i}.BASE.vk.json).
/// Class level (any setup version, so the D-8 review's tamper fixtures run too): the AIR's sha256
/// is the setup's; the domain factor of each shipped vk equals the setup's (compared, not
/// overwritten); each vk's sha256 is the entry's `base_vk_sha256` and `base_params[i]` its
/// parameters; and `class_key_check` (review-D8 M1, M2): pad well formed and at the class TAPE log,
/// parameters recomputed from the class shape, the vk rebuilt from AIR + pad byte for byte.
/// Tree level (setup version 6): every family's `PAD_L` root regenerated at its geometry; each
/// BASE_DIR's leaf program regenerated at its class's family geometry (root = `c_norm`), and every
/// class must be covered by at least one BASE_DIR (review-D8 L1); `C_padN` regenerated at the node
/// geometry; no `C_*` at depth 1; and, when VK_DIR is a run directory (LEAF*.proof, NODE2_0.proof),
/// the run's family `C_2` regenerated over its leaves, then the wrap program, its pinned heights
/// and the final vk regenerated over its root. The tree geometry is read from the setup. Exit 1 on
/// any mismatch.
pub fn tree_audit(air: &str, setup_path: &str, certs: &str, exclusions: &str, vk_dir: &Path, bases: &[String]) {
    let setup_bytes = std::fs::read(setup_path).unwrap();
    let v: serde_json::Value = serde_json::from_slice(&setup_bytes).unwrap();
    let version = v["version"].as_u64().unwrap_or(0) as u32;
    let dof = v["domain_odd_factor"].as_u64().unwrap_or(0) as usize;
    let mut bad = 0;
    let mut check = |ok: bool, what: String| {
        if !ok {
            bad += 1;
        }
        println!("TREE_AUDIT_CHECK {what} -> {}", if ok { "OK" } else { "MISMATCH" });
    };
    check(dof == 15, format!("setup domain_odd_factor {dof}"));
    check(v["air_sha256"].as_str() == Some(hash(&std::fs::read(air).unwrap()).as_str()), "air_sha256 = sha256(AIR)".into());
    let templates: Vec<TemplateEntry> = serde_json::from_value(v["tree"]["templates"].clone()).expect("templates");
    let base_params: Vec<SystemParams> = serde_json::from_value(v["base_params"].clone()).expect("base_params");
    check(templates.len() == base_params.len() && !templates.is_empty(), format!("{} classes, {} base_params", templates.len(), base_params.len()));
    for (i, e) in templates.iter().enumerate() {
        let path = vk_dir.join(format!("CLASS{i}.BASE.vk.json"));
        let raw: serde_json::Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let vdof = raw["domain_odd_factor"].as_u64().unwrap_or(0) as usize;
        let mut vk: MultiStarkVerifyingKey<SC> = serde_json::from_value(raw["vk"].clone()).expect("class vk");
        vk.inner.params.whir.domain_odd_factor = vdof;
        let h = vk_sha(&vk);
        let mut p0 = base_params[i].clone();
        p0.whir.domain_odd_factor = dof;
        let params_ok = serde_json::to_value(&p0).unwrap() == serde_json::to_value(&vk.inner.params).unwrap();
        let airs_ok = e.base_heights.len() == vk.inner.per_air.len();
        let key = if vdof == dof { class_key_check(air, certs, exclusions, &vk, &p0, &e.base_heights, e.tape_pad.as_ref()) } else { Err(format!("vk domain_odd_factor {vdof} != setup's {dof}")) };
        let ok = h == e.base_vk_sha256 && params_ok && airs_ok && key.is_ok();
        check(
            ok,
            format!(
                "class {i} vk_sha={} params={params_ok} airs={airs_ok} key={}",
                h == e.base_vk_sha256,
                key.as_ref().map_or_else(|e| format!("FAIL({e})"), |_| "rebuilt-identical".into())
            ),
        );
    }
    if version != SETUP_VERSION {
        println!("TREE_AUDIT_TREE_LEVEL skipped: setup version {version} (class level only)");
        check(!bases.is_empty(), format!("{} base dirs given", bases.len()));
    } else {
        let setup: WrapSetup = serde_json::from_slice(&setup_bytes).unwrap();
        let tg = setup.tree.tree_geom.expect("a version-6 setup records its tree geometry");
        let tparams = profile::params_geom(false, certs, exclusions, tg);
        let cap_log = tparams.l_skip + tparams.n_stack;
        let k = tparams.k_whir();
        let parent = Sha384CpuEngine::new(tparams.clone());
        let lparams = setup.tree.leaf_params.map_or(tparams.clone(), |g| profile::params_geom(false, certs, exclusions, g));
        let leaf_engine = Sha384CpuEngine::new(lparams);
        let chain_engine = Sha384CpuEngine::new(profile::params(false, certs, exclusions));
        let done = [F::from_u32(t::PHASE_DONE), F::ZERO];
        let zctx = [F::ZERO; t::N_CTX];
        let lcs: Vec<NvCircuit> = setup.tree.families.iter().map(|f| circ(k, f.leaf.log_rows, f.leaf.prog_log, f.leaf.sha_instances, cap_log, None)).collect();
        for (f, (fam, lc)) in setup.tree.families.iter().zip(&lcs).enumerate() {
            let (mats, _) = lc.generate_with(|b| {
                build_pad(b, &zctx, F::ONE, &done);
            });
            let ok = program_commitment(leaf_engine.config(), &mats[0]) == fam.c_pad_leaf
                && fam.classes.iter().all(|&c| setup.tree.templates.get(c as usize).is_some_and(|e| e.family as usize == f));
            check(ok, format!("family {f} geom=({},{},{}) classes={:?}: PAD_L root, class list", fam.leaf.log_rows, fam.leaf.prog_log, fam.leaf.sha_instances, fam.classes));
        }
        check(
            setup.tree.templates.iter().enumerate().all(|(c, e)| setup.tree.families.get(e.family as usize).is_some_and(|f| f.classes.contains(&(c as u32)))),
            "every class in its family".into(),
        );
        let mut covered = vec![false; setup.tree.templates.len()];
        for d in bases {
            let dvk = vk_sha(&load_base(Path::new(d)).0);
            let hit = (0..setup.tree.templates.len()).find(|&c| {
                if setup.tree.templates[c].base_vk_sha256 != dvk {
                    return false;
                }
                let fam = setup.tree.templates[c].family as usize;
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut tm = template_of(Path::new(d), c as u32, true, &chain_engine, &leaf_engine, &lcs[fam]);
                    tm.entry.family = fam as u32;
                    tm.entry == setup.tree.templates[c]
                }))
                .unwrap_or(false)
            });
            if let Some(c) = hit {
                covered[c] = true;
            }
            check(hit.is_some(), format!("leaf root regenerated from {d}: class {hit:?}"));
        }
        check(covered.iter().all(|&x| x), format!("every class's leaf root regenerated by a base dir: {covered:?}"));
        let ng = &setup.tree.node;
        let nprobe = || circ(k, ng.log_rows, ng.prog_log, ng.sha_instances, cap_log, None);
        let (mats, _) = nprobe().generate_with(|b| {
            build_pad_node(b, &zctx, F::from_usize(setup.tree.arity), &done, 2);
        });
        check(program_commitment(parent.config(), &mats[0]) == setup.tree.c_pad_node, "C_padN regenerated at the node geometry".into());
        drop(mats);
        check(setup.tree.depth >= 2 || setup.tree.c_node_star.is_none(), "no C_* at depth 1".into());
        // the run's own family: C_2 over its leaves; the wrap over its root (depth 1)
        let leaves: Vec<std::path::PathBuf> = (0..setup.tree.arity).map(|i| vk_dir.join(format!("LEAF{i}.proof"))).collect();
        if leaves.iter().all(|p| p.exists()) && vk_dir.join("LEAF.vk.json").exists() {
            let lvk = read_vk(&vk_dir.join("LEAF.vk.json"));
            let kids: Vec<Proof<SC>> = leaves.iter().map(|p| read_proof(p)).collect();
            let h0 = vd::proof_heights(&kids[0]);
            match setup.tree.families.iter().position(|f| Some(&f.leaf.heights) == h0.as_ref()) {
                None => check(false, "the run's leaves are at no family's heights".into()),
                Some(f) => {
                    let mut set: Vec<Digest> = setup.tree.templates.iter().filter(|e| e.family as usize == f).map(|e| e.c_norm).collect();
                    set.push(setup.tree.families[f].c_pad_leaf);
                    let pre: Vec<RangeStmt> = (0..kids.len()).map(|i| RangeStmt { ctx: zctx.to_vec(), a: F::from_usize(i), e: F::from_usize(i + 1), s_a: done.to_vec(), s_e: done.to_vec() }).collect();
                    let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = kids.iter().map(|p| (&lvk, p)).collect();
                    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        let (m, _) = nprobe().generate_with(|b| {
                            build_node2(b, &refs, &pre, &set);
                        });
                        program_commitment(parent.config(), &m[0])
                    }));
                    check(r.as_ref().is_ok_and(|c| *c == setup.tree.families[f].c_node2), format!("C_2 of family {f} regenerated over the run's leaves"));
                }
            }
        } else {
            println!("TREE_AUDIT_NOTE no run leaves in {}: C_2 not regenerated", vk_dir.display());
        }
        let root_p = vk_dir.join("NODE2_0.proof");
        if setup.tree.depth == 1 && root_p.exists() && vk_dir.join("NODE.vk.json").exists() {
            let rvk = read_vk(&vk_dir.join("NODE.vk.json"));
            let rp = read_proof(&root_p);
            check(vd::proof_heights(&rp).as_ref() == Some(&setup.tree.node.heights), "the run's root at the node heights".into());
            let c_roots: Vec<Digest> = setup.tree.families.iter().map(|f| f.c_node2).collect();
            let pre = RangeStmt { ctx: zctx.to_vec(), a: F::ZERO, e: F::from_usize(setup.tree.arity), s_a: vec![F::from_u32(t::PHASE_INIT), F::ZERO], s_e: done.to_vec() };
            let mut fparams = setup.final_vk.inner.params.clone();
            fparams.whir.domain_odd_factor = setup.domain_odd_factor;
            let mut calib = profile::params(true, certs, exclusions);
            calib.whir.domain_odd_factor = setup.domain_odd_factor;
            check(serde_json::to_value(&calib).unwrap() == serde_json::to_value(&fparams).unwrap(), "final parameters = the FINAL calibration (NEARPROOF_ZK_FINAL, chain geometry from the environment)".into());
            let final_engine = Sha384CpuEngine::new_final(fparams);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut wc = NvCircuit::new(k, setup.tree.wrap_log_rows, 1);
                wc.prog_log = setup.tree.wrap_prog_log;
                let (m, b) = wc.generate_with(|b| {
                    build_wrap_set(b, &rvk, &rp, 2, &c_roots, &pre);
                });
                let program: Vec<[u32; 4]> = b.instrs.iter().map(|i| i.words()).collect();
                let (pin, _) = shape_pinned_heights(&m, &b, final_engine.config().params().l_skip, FINAL_PIN_EPS_BITS);
                drop(m);
                let (_, fvk) = final_engine.keygen(&wc.airs::<SC>());
                (program, pin, fvk)
            }));
            match r {
                Ok((program, pin, fvk)) => {
                    check(program == setup.program, "wrap program regenerated over the run's root".into());
                    check(pin == setup.final_heights, "wrap pinned heights regenerated".into());
                    let mut f0 = setup.final_vk.clone();
                    f0.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
                    check(serde_json::to_vec(&fvk).unwrap() == serde_json::to_vec(&f0).unwrap(), "final vk regenerated (wrap circuit, FINAL parameters)".into());
                }
                Err(_) => check(false, "wrap regeneration panicked".into()),
            }
        } else {
            println!("TREE_AUDIT_NOTE no depth-1 run root in {}: wrap program / heights / final vk not regenerated", vk_dir.display());
        }
    }
    if bad > 0 {
        println!("TREE_AUDIT_FAILED {bad}");
        std::process::exit(1);
    }
    println!("TREE_AUDIT_OK classes={} bases={}", templates.len(), bases.len());
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
    let tpad = tape_pad_of(setup.tree.templates.get(class as usize).ok_or("template class out of range")?);
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
        let public = public_data(&air_pub, &claim, &hint).with_tape_pad(tpad);
        state::chunk_bridge::expected_claim_parsed(&air_pub.table_num_pub, &public, base_params, Some(&u))
    }))
    .map_err(|_| "claim / hint rejected by the public-statement preparation".to_string())?;
    let ctx = t::ctx_of_digest(expected.digest());
    // [review-D7 I4] the codec is library code too: a panic on a malformed proof is a rejection
    let fp = std::panic::catch_unwind(|| try_decode_proof(&packet[body..])).map_err(|_| "proof codec panicked".to_string())??;
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

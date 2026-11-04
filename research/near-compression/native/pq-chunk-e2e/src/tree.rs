//! [E2E-D D-5] The chunk-independent aggregation tree and the ZK wrap over it (plan §5.0.1;
//! circuit side `openvm-recursion-circuit::nv::tree`).
//!
//! `tree-prove`: leaves = one D0a template leaf (the normaliser of the chunk's converged chain
//! proof `L4`) + PAD leaves up to `arity^depth`; `depth` levels of `arity`-ary nodes; the wrap
//! (final domain, zk = 6). Every tree proof shares one vk and one pinned set of trace heights; the
//! node program is one program `P_node` (`C_node` its program root); the level-1 template set
//! holds the normaliser program of every D0a shape class given, plus PAD. The wrap setup is a
//! function of (template set, tree shape) only: the same `SETUP.json` for every chunk
//! (`NEARPROOF_TREE_SETUP=SETUP.json` proves against an existing setup and checks it is
//! byte-identical).
//!
//! `tree-verify`: V_d. Packet `NPQTW02 | u64 |hint| | hint | u32 class | u32 m | u (m x 12 u32) |
//! wrap proof`; V_d recomputes the D0a template statement digest `ctx` from (claim, hint, u) under
//! the base parameters of template class `class` (the setup lists them), exactly as the D0a
//! verifier does, and checks `pvs = [LEVEL_WRAP, D_wrap(ctx, class)]` (`vd::verify_wrap`); the
//! class is folded into `D_wrap` from the root's `B_0`, which the template leaf set. Nothing of the
//! tree is a V_d input. (The class is public: for D0a it is the base shape class, which `u` and
//! the base parameters reveal anyway; a canonical-claimDigest template would not need it.)
use super::*;
use openvm_recursion_circuit::{
    nv::{
        agg::RangeStmt,
        circuit::{program_commitment, prove_mats},
        tree::{self as t, build_base_leaf, build_norm, build_node, build_pad, build_wrap},
    },
    sha384::config::{Digest, F, fs_jobs, fs_jobs_reset},
};
use openvm_stark_backend::StarkProtocolConfig;
use p3_field::{PrimeCharacteristicRing, PrimeField32};

const MAGIC: &[u8; 8] = b"NPQTW02\0";

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct TemplateEntry {
    /// the D0a shape class (chunk) whose converged chain level this normaliser verifies
    pub name: String,
    /// the anchor the normaliser binds its child by: (level M, the level-M program root C_M)
    pub anchor: (u32, Digest),
    /// the normaliser's program root (an element of the node's template set)
    pub c_norm: Digest,
}

/// Audit content of the wrap setup: everything the wrap program embeds (V_d reads none of it).
#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct TreeShape {
    pub arity: usize,
    pub depth: usize,
    pub log_rows: usize,
    pub prog_log: usize,
    /// pinned (log, tight) heights of every tree proof (leaves and nodes), AIR order
    pub heights: Vec<vd::PinnedHeight>,
    pub templates: Vec<TemplateEntry>,
    pub c_pad: Digest,
    pub c_node: Digest,
    pub wrap_log_rows: usize,
    pub wrap_prog_log: usize,
}

#[derive(Serialize, Deserialize)]
pub struct WrapSetup {
    pub version: u32,
    pub domain_odd_factor: usize,
    /// the D0a template's base AIR and parameters (V_d recomputes the template statement `ctx`)
    pub air_sha256: String,
    /// per template class (template order): the D0a base parameters V_d recomputes `ctx` under
    pub base_params: Vec<SystemParams>,
    pub final_vk: MultiStarkVerifyingKey<SC>,
    pub program: Vec<[u32; 4]>,
    pub level: u32,
    pub final_heights: Vec<vd::PinnedHeight>,
    pub tree: TreeShape,
}

const LOG_ROWS: usize = 20;
const PROG_LOG: usize = 19;

fn root_of(p: &Proof<SC>) -> Digest {
    p.trace_vdata[0].as_ref().unwrap().cached_commitments[0]
}

fn template_kind_base() -> bool {
    match std::env::var("NEARPROOF_TREE_TEMPLATE").as_deref() {
        Ok("base") => true,
        Ok("chain") | Err(_) => false,
        Ok(o) => panic!("unknown NEARPROOF_TREE_TEMPLATE {o}"),
    }
}

fn leaf_circ(k: usize, h: &[vd::PinnedHeight]) -> NvCircuit {
    let mut c = NvCircuit::new(k, LOG_ROWS, 1);
    c.program_part = true;
    c.prog_log = PROG_LOG;
    c.heights = Some(h.iter().map(|&(l, _)| 1usize << l).collect());
    c.tight_floor = Some(h.iter().map(|&(l, tt)| tt.unwrap_or(1 << l)).collect());
    c
}

fn fits(nat: &[vd::PinnedHeight], pin: &[vd::PinnedHeight]) -> bool {
    nat.iter().zip(pin).all(|(a, b)| a.0 <= b.0 && a.1.unwrap_or(1 << a.0) <= b.1.unwrap_or(1 << b.0))
}

/// The chunk's D0a template claim (statement digest of the base proof + TAPE at u), as the D0a
/// chain carries it.
fn d0a_claim(air: &str, public: &str, dir: &Path) -> (openvm_recursion_circuit::nv::circuit::StatementClaim, Vec<Ef>, SystemParams) {
    let (vk, p) = load_base(dir);
    let u = base_point(&vk, &p);
    let params = vk.inner.params.clone();
    let c = state::chunk_bridge::expected_claim_at(air, public, params.clone(), &u);
    (c, u, params)
}

/// [E2E-D D-6] `tree-arity CERTS EXCLUSIONS RUN_DIR ARITIES PROVE_ARITY CLASS_DIR...`: the cost of
/// an `a`-ary node over the leaf proofs of a finished `tree-prove` run (`RUN_DIR/LEAF*.proof`,
/// `TREE.vk.json`; the run's chunk is the class whose `L4` the run's leaf 0 normalised: the first
/// class dir whose ctx matches). For each `a` in ARITIES: generate (never prove) the node's trace at
/// natural heights at the tree's `NvAir` 2^20 / program 2^19 (a node's ALU height must equal its
/// children's, BIND) over the leaves
/// `i mod n` (when `a > n` the children repeat, so the range statements do not chain: the program
/// and its trace shape are measured, not a valid node), and print program rows, used rows per AIR,
/// SHA-384 compressions and the shape pin. PROVE_ARITY `p` (0 = none, `p <= n`): also prove the
/// valid `p`-ary node over leaves `0..p` at natural heights (`NvAir` 2^20, program 2^19, the tree
/// layer's parameters) and report its size, time and native verification. Nothing of the run is
/// changed.
pub fn tree_arity(certs: &str, exclusions: &str, run: &Path, arities: &str, prove_arity: usize, classes: &[String]) {
    let tparams = profile::params_geom(false, certs, exclusions, profile::tree_geom());
    let parent = Sha384CpuEngine::new(tparams);
    let chain_engine = Sha384CpuEngine::new(profile::params(false, certs, exclusions));
    let k = parent.config().params().k_whir();
    let probe = {
        let mut c = NvCircuit::new(k, LOG_ROWS, 1);
        c.program_part = true;
        c.prog_log = PROG_LOG;
        c
    };
    // the template set exactly as tree-prove builds it
    let mut set = vec![];
    let mut tmpl = vec![];
    for (i, dir) in classes.iter().enumerate() {
        let d = Path::new(dir);
        let vk = read_vk(&d.join("L4.vk.json"));
        let p = read_proof(&d.join("L4.proof"));
        chain_engine.verify(&vk, &p).expect("template L4 proof");
        let anchor = (p.public_values[0][0].as_canonical_u32(), root_of(&p));
        let (mats, _) = probe.generate_with(|b| {
            build_norm(b, &vk, &p, anchor, F::ZERO, i as u32);
        });
        set.push(program_commitment(parent.config(), &mats[0]));
        tmpl.push(p.public_values[0][1..19].to_vec());
    }
    let tvk = read_vk(&run.join("TREE.vk.json"));
    let mut leaves = vec![];
    while run.join(format!("LEAF{}.proof", leaves.len())).exists() {
        let p = read_proof(&run.join(format!("LEAF{}.proof", leaves.len())));
        parent.verify(&tvk, &p).expect("leaf proof");
        leaves.push((tvk.clone(), p));
    }
    let n = leaves.len();
    assert!(n >= 2, "need the run's leaves");
    // leaf 0 = the template leaf of class c over ctx; leaves 1.. = PAD
    let (class, ctx) = (0..classes.len())
        .find_map(|c| {
            let ctx = tmpl[c].clone();
            let s = RangeStmt { ctx: ctx.clone(), a: F::ZERO, e: F::ONE, s_a: vec![F::from_u32(t::PHASE_INIT), F::from_usize(c)], s_e: vec![F::from_u32(t::PHASE_DONE), F::from_usize(c)] };
            openvm_recursion_circuit::nv::agg::check_range_statement(&leaves[0].1.public_values[0], &s).then_some((c, ctx))
        })
        .expect("leaf 0 is no class's template leaf");
    let done = vec![F::from_u32(t::PHASE_DONE), F::from_usize(class)];
    // the PAD program closes the template set (as in tree-prove)
    let (mats, _) = probe.generate_with(|b| {
        build_pad(b, &ctx, F::ONE, &done);
    });
    set.push(program_commitment(parent.config(), &mats[0]));
    let stmts: Vec<RangeStmt> = (0..n)
        .map(|i| {
            if i == 0 {
                RangeStmt { ctx: ctx.clone(), a: F::ZERO, e: F::ONE, s_a: vec![F::from_u32(t::PHASE_INIT), F::from_usize(class)], s_e: done.clone() }
            } else {
                RangeStmt { ctx: ctx.clone(), a: F::from_usize(i), e: F::from_usize(i + 1), s_a: done.clone(), s_e: done.clone() }
            }
        })
        .collect();
    for (i, (_, p)) in leaves.iter().enumerate() {
        assert!(openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], &stmts[i]), "leaf {i} statement");
    }
    println!("TREE_ARITY_LEAVES n={n} class={class} heights={:?}", vd::proof_heights(&leaves[0].1));
    // [E2E-D D-6] a node's NvAir height must equal its children's: the in-circuit BIND check
    // evaluates the node's own program at the child's ALU domain (`bind_child_program`: "child ALU
    // height must equal ours"), and it is emitted for every child (gated in-circuit by the level
    // flag). So the probe runs at the tree's LOG_ROWS / PROG_LOG; an arity whose NvAir trace
    // exceeds 2^LOG_ROWS is reported as not fitting.
    for a in arities.split(',').map(|x| x.trim().parse::<usize>().unwrap()) {
        let t0 = std::time::Instant::now();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut c = NvCircuit::new(k, LOG_ROWS, 1);
            c.program_part = true;
            c.prog_log = PROG_LOG;
            let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = (0..a).map(|i| (&leaves[i % n].0, &leaves[i % n].1)).collect();
            let pre: Vec<RangeStmt> = (0..a).map(|i| stmts[i % n].clone()).collect();
            let (mats, b) = c.generate_with(|b| {
                build_node(b, &refs, &pre, &set);
            });
            let used = openvm_recursion_circuit::nv::circuit::natural_tight_heights(&mats, 2);
            let (pin, info) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
            println!(
                "TREE_ARITY_PROBE arity={a} distinct_children={} program_rows={} used_rows={used:?} sha_compressions={} shape_pin={pin:?} info={info:?} failures={} gen_s={:.1}",
                a.min(n),
                b.instrs.len(),
                used[1] / openvm_recursion_circuit::sha384::compress4_air::ROWS,
                b.failures.len(),
                t0.elapsed().as_secs_f64()
            );
        }));
        if r.is_err() {
            println!("TREE_ARITY_PROBE_DOES_NOT_FIT arity={a} (NvAir 2^{LOG_ROWS}, program 2^{PROG_LOG}: the children's ALU height) gen_s={:.1}", t0.elapsed().as_secs_f64());
        }
    }
    if prove_arity >= 2 {
        assert!(prove_arity <= n, "a valid node needs distinct consecutive leaves");
        let t0 = std::time::Instant::now();
        let mut c = NvCircuit::new(k, LOG_ROWS, 1);
        c.program_part = true;
        c.prog_log = PROG_LOG;
        let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = leaves[..prove_arity].iter().map(|(a, b)| (a, b)).collect();
        let mut s = None;
        let (mats, b) = c.generate_with(|b| {
            s = Some(build_node(b, &refs, &stmts[..prove_arity], &set));
        });
        assert!(b.failures.is_empty(), "node: {:?}", b.failures);
        let gen_s = t0.elapsed().as_secs_f64();
        let (v, p, shapes) = prove_mats(&c, &parent, mats, &b);
        assert!(openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], s.as_ref().unwrap()));
        let bytes = save_proof(&run.join(format!("ARITY{prove_arity}_NODE.proof")), &p);
        println!(
            "TREE_ARITY_PROVED arity={prove_arity} program_rows={} heights={:?} shapes={shapes:?} bytes={bytes} gen_s={gen_s:.1} total_s={:.1} verified=native",
            b.instrs.len(),
            vd::proof_heights(&p),
            t0.elapsed().as_secs_f64()
        );
        drop(v);
    }
}

pub fn tree_prove(air: &str, public: &str, out: &Path, chunk: &Path, classes: &[String], certs: &str, exclusions: &str, arity: usize, depth: usize) {
    assert!(arity >= 2 && depth >= 1);
    std::fs::create_dir_all(out).unwrap();
    let t_all = std::time::Instant::now();
    let tparams = profile::params_geom(false, certs, exclusions, profile::tree_geom());
    println!(
        "TREE_PARAMS n_stack={} log_blowup={} queries={:?}",
        tparams.n_stack,
        tparams.log_blowup,
        tparams.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>()
    );
    let parent = Sha384CpuEngine::new(tparams);
    let chain_engine = Sha384CpuEngine::new(profile::params(false, certs, exclusions));
    let final_engine = Sha384CpuEngine::new_final(profile::params(true, certs, exclusions));
    let k = parent.config().params().k_whir();
    let fixed: Option<WrapSetup> = std::env::var("NEARPROOF_TREE_SETUP")
        .ok()
        .map(|p| serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap());
    // ---- templates: one normaliser program per D0a shape class, plus PAD
    let probe = {
        let mut c = NvCircuit::new(k, LOG_ROWS, 1);
        c.program_part = true;
        c.prog_log = PROG_LOG;
        c
    };
    let mut templates = vec![];
    let mut leaf_pins: Vec<Vec<vd::PinnedHeight>> = vec![];
    let mut target: Option<(MultiStarkVerifyingKey<SC>, Proof<SC>, (u32, Digest), u32)> = None;
    // [E2E-D D-6] NEARPROOF_TREE_TEMPLATE=base: the template is the class's standalone base proof
    // itself, verified by the leaf (`build_base_leaf`: the lane A/B leaf prototype), not a chain
    // level; the anchor is then (0, 0) (no program binding: the child has no NV program)
    let base_tmpl = template_kind_base();
    for dir in classes {
        let d = Path::new(dir);
        let ci = templates.len() as u32;
        let (vk, p, anchor) = if base_tmpl {
            let (vk, p) = load_base(d);
            (vk, p, (0u32, Digest::default()))
        } else {
            let vk = read_vk(&d.join("L4.vk.json"));
            let p = read_proof(&d.join("L4.proof"));
            chain_engine.verify(&vk, &p).expect("template L4 proof");
            let anchor = (p.public_values[0][0].as_canonical_u32(), root_of(&p));
            (vk, p, anchor)
        };
        let level = anchor.0;
        let t0 = std::time::Instant::now();
        let (mats, b) = probe.generate_with(|b| {
            if base_tmpl {
                build_base_leaf(b, &vk, &p, F::ZERO, ci);
            } else {
                build_norm(b, &vk, &p, anchor, F::ZERO, ci);
            }
        });
        assert!(b.failures.is_empty(), "template leaf {dir}: {:?}", b.failures);
        let c_norm = program_commitment(parent.config(), &mats[0]);
        let (pin, info) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
        let name = d.file_name().unwrap().to_string_lossy().to_string();
        println!("TREE_TEMPLATE {name} kind={} level={level} rows={} pin={pin:?} info={info:?} s={:.1}", if base_tmpl { "base" } else { "chain" }, b.instrs.len(), t0.elapsed().as_secs_f64());
        leaf_pins.push(pin);
        templates.push(TemplateEntry { name, anchor, c_norm });
        if d.canonicalize().unwrap() == chunk.canonicalize().unwrap() {
            target = Some((vk, p, anchor, ci));
        }
    }
    let (tvk, tp, tanchor, class) = target.expect("the chunk must be one of the template classes");
    let ctx: Vec<F> = if base_tmpl {
        t::ctx_of_digest(d0a_claim(air, public, chunk).0.digest())
    } else {
        tp.public_values[0][1..19].to_vec()
    };
    let done = vec![F::from_u32(t::PHASE_DONE), F::from_u32(class)];
    let (mats, b) = probe.generate_with(|b| {
        build_pad(b, &ctx, F::ONE, &done);
    });
    let c_pad = program_commitment(parent.config(), &mats[0]);
    let (pad_pin, _) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
    println!("TREE_PAD rows={} pin={pad_pin:?}", b.instrs.len());
    leaf_pins.push(pad_pin);
    let mut set: Vec<Digest> = templates.iter().map(|t| t.c_norm).collect();
    set.push(c_pad);
    // ---- uniform tree heights: the node verifies `arity` leaf-sized children, so its rows are
    // about `arity` times a leaf's; pin generously (checked against the node's shape pin below)
    let mut h: Vec<vd::PinnedHeight> = match &fixed {
        Some(f) => {
            assert_eq!(f.tree.templates, templates, "template set differs from the fixed setup's");
            assert_eq!(f.tree.c_pad, c_pad, "PAD program differs from the fixed setup's");
            assert_eq!((f.tree.arity, f.tree.depth), (arity, depth), "tree shape differs from the fixed setup's");
            // [E2E-D D-6] NEARPROOF_TREE_TEMPLATES_ONLY=1: stop once the template set (every
            // class's anchor (M, C_M) and normaliser root) and PAD equal the fixed setup's; the
            // rest of the setup is a function of these, the arity and the depth
            if std::env::var("NEARPROOF_TREE_TEMPLATES_ONLY").is_ok_and(|v| v == "1") {
                println!("TREE_TEMPLATES_MATCH_FIXED_SETUP {:?}", templates.iter().map(|t| (&t.name, t.anchor.0)).collect::<Vec<_>>());
                return;
            }
            f.tree.heights.clone()
        }
        None => {
            let mx = |a: usize| -> usize { leaf_pins.iter().map(|p| p[a].1.unwrap()).max().unwrap() };
            let lg = |a: usize| -> usize { leaf_pins.iter().map(|p| p[a].0).max().unwrap() };
            // measured on the Fib fixture: a 2-ary node is ~2.4x a leaf (its children are tree
            // proofs, larger than the template child); start at arity x 1.25 + 1/16
            let grow = |x: usize| (x * arity + x * arity / 4 + x / 16).next_multiple_of(4);
            let t0 = grow(mx(0)).min(1 << LOG_ROWS);
            let t1 = grow(mx(1));
            vec![
                (LOG_ROWS, Some(t0)),
                (lg(1).max(t1.next_power_of_two().trailing_zeros() as usize), Some(t1)),
                (lg(2), Some(mx(2))),
                (lg(3), Some(mx(3))),
            ]
        }
    };
    // ---- leaves: the chunk's normaliser at index 0, PAD at 1.. (n = arity^depth). The pin must
    // hold the node (checked on the first node's shape pin before any node is proved); if it does
    // not, raise the pin to the node's (+2%) and re-prove the leaves (setup creation only).
    let n = arity.pow(depth as u32);
    let mut seconds = serde_json::Map::new();
    let (lc, mut level_proofs, mut stmts) = loop {
    println!("TREE_HEIGHTS {h:?}");
    let lc = leaf_circ(k, &h);
    let mut level_proofs: Vec<(MultiStarkVerifyingKey<SC>, Proof<SC>)> = vec![];
    let mut stmts: Vec<RangeStmt> = vec![];
    for i in 0..n {
        let t0 = std::time::Instant::now();
        let (mats, b, stmt) = if i == 0 {
            let mut s = None;
            let (m, b) = lc.generate_with(|b| {
                s = Some(if base_tmpl {
                    build_base_leaf(b, &tvk, &tp, F::ZERO, class)
                } else {
                    build_norm(b, &tvk, &tp, tanchor, F::ZERO, class)
                });
            });
            (m, b, s.unwrap())
        } else {
            let mut s = None;
            let (m, b) = lc.generate_with(|b| {
                s = Some(build_pad(b, &ctx, F::from_usize(i), &done));
            });
            (m, b, s.unwrap())
        };
        let (v, p, _) = prove_mats(&lc, &parent, mats, &b);
        assert_eq!(vd::proof_heights(&p).unwrap(), h, "leaf {i}: heights differ from the tree pin");
        assert_eq!(root_of(&p), set[if i == 0 { class as usize } else { set.len() - 1 }], "leaf {i}: program root not its template's");
        assert!(openvm_recursion_circuit::nv::agg::check_range_statement(&p.public_values[0], &stmt));
        let bytes = save_proof(&out.join(format!("LEAF{i}.proof")), &p);
        let s = t0.elapsed().as_secs_f64();
        println!("TREE_LEAF {i} rows={} bytes={bytes} seconds={s:.1}", b.instrs.len());
        seconds.insert(format!("leaf{i}"), s.into());
        if i == 0 {
            save_vk(&out.join("TREE.vk.json"), &v);
        }
        level_proofs.push((v, p));
        stmts.push(stmt);
    }
    {
        let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = level_proofs[..arity].iter().map(|(a, b)| (a, b)).collect();
        let (mats, b) = lc.generate_with(|b| {
            build_node(b, &refs, &stmts[..arity], &set);
        });
        let (npin, info) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
        println!("TREE_NODE_PROBE rows={} shape_pin={npin:?} info={info:?}", b.instrs.len());
        if fits(&npin, &h) {
            break (lc, level_proofs, stmts);
        }
        assert!(fixed.is_none(), "node does not fit the fixed setup's tree heights");
        h = h
            .iter()
            .zip(&npin)
            .map(|(&(l, t), &(nl, nt))| {
                let t2 = t.unwrap().max(nt.unwrap() + nt.unwrap() / 50).next_multiple_of(4);
                let l2 = l.max(nl).max(t2.next_power_of_two().trailing_zeros() as usize);
                (l2, Some(t2.min(1 << l2)))
            })
            .collect();
        println!("TREE_HEIGHTS_RAISED {h:?}");
    }
    };
    // ---- nodes
    let mut c_node: Option<Digest> = None;
    let mut node_rows = 0;
    for lvl in 2..=depth + 1 {
        let mut next = vec![];
        let mut nstmts = vec![];
        for (j, (kids, pre)) in level_proofs.chunks(arity).zip(stmts.chunks(arity)).enumerate() {
            let t0 = std::time::Instant::now();
            let refs: Vec<(&MultiStarkVerifyingKey<SC>, &Proof<SC>)> = kids.iter().map(|(a, b)| (a, b)).collect();
            let mut s = None;
            let (mats, b) = lc.generate_with(|b| {
                s = Some(build_node(b, &refs, pre, &set));
            });
            assert!(b.failures.is_empty(), "node L{lvl}_{j}: {:?}", b.failures);
            let (npin, info) = shape_pinned_heights(&mats, &b, 2, FINAL_PIN_EPS_BITS);
            println!("TREE_NODE L{lvl}_{j} rows={} shape_pin={npin:?} info={info:?}", b.instrs.len());
            assert!(fits(&npin, &h), "node L{lvl}_{j}: shape pin {npin:?} exceeds the tree pin {h:?}");
            node_rows = b.instrs.len();
            let (v, p, _) = prove_mats(&lc, &parent, mats, &b);
            assert_eq!(vd::proof_heights(&p).unwrap(), h);
            assert_eq!(p.public_values[0][0], F::from_usize(lvl), "node level");
            let r = root_of(&p);
            assert!(c_node.is_none_or(|c| c == r), "node programs differ across levels / siblings");
            c_node = Some(r);
            let bytes = save_proof(&out.join(format!("NODE{lvl}_{j}.proof")), &p);
            let sec = t0.elapsed().as_secs_f64();
            println!("TREE_NODE_PROVED L{lvl}_{j} bytes={bytes} seconds={sec:.1}");
            seconds.insert(format!("node{lvl}_{j}"), sec.into());
            next.push((v, p));
            nstmts.push(s.unwrap());
        }
        level_proofs = next;
        stmts = nstmts;
    }
    let c_node = c_node.unwrap();
    let (rvk, rp) = level_proofs.pop().unwrap();
    let root_stmt = stmts.pop().unwrap();
    // ---- wrap (final domain, zk-masked; heights pinned from the shape, F1(b))
    let t0 = std::time::Instant::now();
    let wrap_prog_log = std::env::var("NEARPROOF_WRAP_PROG_LOG").ok().map_or(18, |v| v.parse().unwrap());
    let mut wc = NvCircuit::new(k, LOG_ROWS, 1);
    wc.prog_log = wrap_prog_log;
    let root_level = 1 + depth as u32;
    let wbody = |b: &mut openvm_recursion_circuit::nv::builder::Builder| {
        build_wrap(b, &rvk, &rp, root_level, c_node, &root_stmt);
    };
    let fparams = final_engine.config().params().clone();
    let wh: Vec<vd::PinnedHeight> = match &fixed {
        Some(f) => {
            assert_eq!(f.tree.c_node, c_node, "node program differs from the fixed setup's");
            f.final_heights.clone()
        }
        None => {
            let (m, b) = wc.generate_with(wbody);
            let (pin, info) = shape_pinned_heights(&m, &b, fparams.l_skip, FINAL_PIN_EPS_BITS);
            println!("WRAP_SHAPE_PIN {pin:?} info={info:?} profile={:?}", b.height_profile);
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
    let wsec = t0.elapsed().as_secs_f64();
    seconds.insert("wrap".into(), wsec.into());
    let program: Vec<[u32; 4]> = b.instrs.iter().map(|i| i.words()).collect();
    let tree = TreeShape {
        arity,
        depth,
        log_rows: LOG_ROWS,
        prog_log: PROG_LOG,
        heights: h.clone(),
        templates,
        c_pad,
        c_node,
        wrap_log_rows: LOG_ROWS,
        wrap_prog_log,
    };
    let (_, base_u, _) = d0a_claim(air, public, chunk);
    let base_params: Vec<SystemParams> = classes.iter().map(|d| load_base(Path::new(d)).0.inner.params.clone()).collect();
    let setup = WrapSetup {
        version: 3,
        domain_odd_factor: 15,
        air_sha256: hash(&std::fs::read(air).unwrap()),
        base_params,
        final_vk: fv,
        program,
        level: t::LEVEL_WRAP,
        final_heights: wh.clone(),
        tree,
    };
    let vds = VdSetup { vk_final: setup.final_vk.clone(), program: setup.program.clone(), level: setup.level, heights: Some(wh.clone()) };
    // the template statement the chain carried is the D0a claim of this chunk
    let (claim, _, _) = d0a_claim(air, public, chunk);
    let cctx = t::ctx_of_digest(claim.digest());
    assert_eq!(cctx, ctx, "the template leaf's ctx is the chunk's claim digest");
    vd::verify_wrap(&vds, &final_engine, &ctx, class, &fp).expect("V_d (wrap)");
    for c in 0..setup.tree.templates.len() as u32 {
        if c != class {
            assert!(vd::verify_wrap(&vds, &final_engine, &ctx, c, &fp).is_err(), "wrong class accepted");
        }
    }
    // negative controls on the real artifact
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
    // [E2E-D D-6] the template set must be a function of the classes' shapes: every class's chain
    // ran with shape floors at every level (review-D4 F2; ZK-ARGUMENT 7.1, 10.1). Provenance is the
    // chain log of the run that made the class's L4 (`L1_SHAPE_FLOOR`, printed only with
    // NEARPROOF_CHAIN_SHAPE_FLOORS on).
    let shape_floored: Vec<bool> = classes
        .iter()
        .map(|d| base_tmpl || std::fs::read_to_string(Path::new(d).join("chain.log")).is_ok_and(|s| s.contains("L1_SHAPE_FLOOR")))
        .collect();
    let zk_ok = zk_masked && shape_floored.iter().all(|&x| x);
    // shape-pin aborts the prover can hit for this packet, each <= 2^-192 (ZK-ARGUMENT 10.1): the
    // chunk's chain levels L1..L_M (shape floors), every tree proof, the wrap
    let tree_proofs: usize = (0..=depth).map(|l| arity.pow(l as u32)).sum();
    let abort_terms = tanchor.0 as usize + tree_proofs + 1;
    let zk_scope = if zk_ok {
        format!(
            "statistical zero knowledge of the tree-wrap packet for the statement (claim, hint, class, setup), classical programmable ROM: eps_ZK <= 2^-184.4 + {abort_terms} x 2^-192 (shape-pin aborts), ZK-ARGUMENT.md 6.4, 7.1, 10.1; the setup is one for all chunks (a function of the template classes' shapes, the arity and the depth); the packet reveals the template class (the chunk's D0a shape class); QROM: ZK-ARGUMENT.md 6.5 (the base point u is open)"
        )
    } else if zk_masked {
        format!("none: a template class was not proved with shape floors {shape_floored:?}")
    } else {
        "none: wrap not zk-masked".into()
    };
    let result = serde_json::json!({
        "scope": "D0a template, chunk-independent tree + wrap (D-6)",
        "security_established": false,
        "zero_knowledge_established": zk_ok,
        "zero_knowledge_scope": zk_scope,
        "templates_shape_floored": shape_floored,
        "template_kind": if base_tmpl { "base (the class base proof, build_base_leaf)" } else { "chain (the class chain L4, build_norm)" },
        "arity": arity, "depth": depth, "leaves": n,
        "wrap_proof_bytes": proof_bytes, "hint_bytes": hint.len(), "bundle_bytes": packet.len(),
        "setup_bytes": setup_bytes.len(), "setup_sha256": pin,
        "node_program_rows": node_rows, "wrap_program_rows": wrap_rows,
        "tree_heights": h, "wrap_heights": wh,
        "seconds": seconds, "total_seconds": t_all.elapsed().as_secs_f64(),
    });
    std::fs::write(out.join("RESULT.json"), serde_json::to_vec_pretty(&result).unwrap()).unwrap();
    println!("TREE_WRAP_VERIFIED {result}");
}

pub fn tree_verify(air: &str, claim_path: &str, setup_path: &str, pin: &str, bundle: &str) {
    let t_all = std::time::Instant::now();
    let setup_bytes = std::fs::read(setup_path).unwrap();
    assert_eq!(hash(&setup_bytes), pin, "untrusted setup: hash differs from operator's pin");
    let mut setup: WrapSetup = serde_json::from_slice(&setup_bytes).unwrap();
    assert_eq!((setup.version, setup.domain_odd_factor), (3, 15));
    for p in setup.base_params.iter_mut() {
        p.whir.domain_odd_factor = setup.domain_odd_factor;
    }
    setup.final_vk.inner.params.whir.domain_odd_factor = setup.domain_odd_factor;
    let air_bytes = std::fs::read(air).unwrap();
    assert_eq!(hash(&air_bytes), setup.air_sha256, "AIR differs from pinned setup");
    let packet = std::fs::read(bundle).unwrap();
    assert!(packet.len() >= 16 && &packet[..8] == MAGIC, "bundle framing");
    let n = usize::try_from(u64::from_le_bytes(packet[8..16].try_into().unwrap())).unwrap();
    assert!(n <= packet.len() - 16, "truncated hint");
    let mut body = 16 + n;
    assert!(packet.len() >= body + 8, "truncated class / stacking point");
    let class = u32::from_le_bytes(packet[body..body + 4].try_into().unwrap());
    let base_params = setup.base_params.get(class as usize).expect("template class out of range").clone();
    body += 4;
    let m = u32::from_le_bytes(packet[body..body + 4].try_into().unwrap()) as usize;
    assert_eq!(m, base_params.n_stack + 1, "stacking point length");
    body += 4;
    assert!(packet.len() >= body + 48 * m, "truncated stacking point");
    let u: Vec<Ef> = (0..m)
        .map(|i| {
            let o = body + 48 * i;
            ef_of_words(core::array::from_fn(|k| u32::from_le_bytes(packet[o + 4 * k..o + 4 * k + 4].try_into().unwrap())))
        })
        .collect();
    body += 48 * m;
    let air_pub = npudr::airpub::AirPublic::from_json_slice(&air_bytes).expect("air json");
    let public = public_data(&air_pub, &std::fs::read(claim_path).unwrap(), &packet[16..16 + n]);
    let expected = state::chunk_bridge::expected_claim_parsed(&air_pub.table_num_pub, &public, base_params, Some(&u));
    let ctx = t::ctx_of_digest(expected.digest());
    let fp = decode_proof(&packet[body..]);
    let engine = Sha384CpuEngine::new_final(setup.final_vk.inner.params.clone());
    fs_jobs_reset();
    let t_v = std::time::Instant::now();
    vd::verify_wrap(
        &VdSetup { vk_final: setup.final_vk, program: setup.program, level: setup.level, heights: Some(setup.final_heights) },
        &engine,
        &ctx,
        class,
        &fp,
    )
    .expect("wrap verifier");
    let fs = fs_jobs();
    println!(
        "VERIFY_PROFILE_MS total={:.2} wrap_verify={:.2} FS_JOBS flush={} commit={} squeeze={} pow={}",
        t_all.elapsed().as_secs_f64() * 1e3,
        t_v.elapsed().as_secs_f64() * 1e3,
        fs[0],
        fs[1],
        fs[2],
        fs[3]
    );
    println!("INDEPENDENT_TREE_VERIFY_OK bundle_bytes={} class={class}", packet.len());
}

/// [E2E-D D-5, review-D4 F5] Count the Fiat-Shamir jobs `R` of one proof's native verification:
/// every SHA-384 evaluation of the transcript (flush, commit absorb, squeeze / PoW-run block,
/// PoW block), under the proof's own domain. `final` = the FINAL domain.
pub fn fs_count(vk_path: &str, proof_path: &str, final_domain: bool) {
    let vk = if vk_path.ends_with("SETUP.json") {
        let v: serde_json::Value = serde_json::from_slice(&std::fs::read(vk_path).unwrap()).unwrap();
        let mut vk: MultiStarkVerifyingKey<SC> = serde_json::from_value(v["final_vk"].clone()).unwrap();
        vk.inner.params.whir.domain_odd_factor = v["domain_odd_factor"].as_u64().unwrap() as usize;
        vk
    } else {
        read_vk(Path::new(vk_path))
    };
    let p = if proof_path.ends_with(".bundle") {
        // the proof is the packet's tail: re-encode check by decoding from each candidate offset
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

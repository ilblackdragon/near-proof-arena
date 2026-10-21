//! NV-faithful: degree-of-freedom (single-cell perturbation) runs and tamper tests for the ALU,
//! BIND roles (results/pq-recursion-nv/FAITHFUL.md; the app-binding role was removed with G2).
//!
//!   NV_DOF_CAP=<rows per (AIR, role)>   (default 48; 0 = every row)
use core::borrow::Borrow;
use std::collections::BTreeMap;

use openvm_stark_backend::{
    keygen::types::MultiStarkVerifyingKey,
    proof::Proof,
    test_utils::{FibFixture, InteractionsFixture11, TestFixture},
    AirRef, StarkEngine,
};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{
    circuit::NvCircuit,
    faithful_dof::*,
    isa::{Op, ADDR_BITS, OP_LO},
    uair::{AbCols, BindCols, NvCommon, AB_W, BIND_W, N_COMMON, NV_WIDTH},
};
use crate::sha384::{config::*, e2e_tests::child_params_small};

fn honest(
    vk: &MultiStarkVerifyingKey<Sha384Config>,
    proof: &Proof<Sha384Config>,
    log_rows: usize,
) -> (Vec<AirRef<Sha384Config>>, Vec<RowMajorMatrix<F>>, Vec<Vec<F>>) {
    let circ = NvCircuit::new(vk.inner.params.k_whir(), log_rows, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mats, b) = circ.generate(vk, proof);
    assert!(b.failures.is_empty(), "{:?}", b.failures);
    let pvs: Vec<Vec<F>> = (0..airs.len()).map(|i| if i == 0 { b.public_values() } else { vec![] }).collect();
    (airs, mats, pvs)
}

/// Undetected cells that are don't-care by construction (FAITHFUL.md §4.2): the column is not
/// read by any constraint or interaction of the row's role (or its op), so the extracted
/// semantics cannot depend on it.  Returns the reason, or None if unexpected.
pub fn dont_care(air: &str, role: &str, col: &str) -> Option<&'static str> {
    if air.contains("ByteAir") {
        // x = 255: (x - 255) inv = 1 - z = 0 leaves inv free; inv is read nowhere else
        return (role == "x255" && col == "c3").then_some("byte table inv on the x = 255 rows");
    }
    if !air.contains("NvAir") {
        return None;
    }
    let pool = col.starts_with("pool");
    if let Some(op) = role.strip_prefix("ALU:") {
        if pool {
            return Some("pool column beyond the ALU view");
        }
        let o = Op::all().into_iter().find(|o| format!("{o:?}") == op);
        let is = |c: &str, p: &str| c.starts_with(p) && c[p.len()..].chars().all(|x| x.is_ascii_digit());
        if let Some(o) = o {
            if is(col, "a") && !o.reads_a() {
                return Some("operand a not read by this op");
            }
            if is(col, "b") && !o.reads_b() {
                return Some("operand b not read by this op");
            }
            if col == "wit" && !matches!(o, Op::Horn | Op::Horn2) {
                return Some("wit only used by Horn / Horn2");
            }
            if col == "wit2" && o != Op::Horn2 {
                return Some("wit2 only used by Horn2");
            }
        }
        return None;
    }
    if role == "BIND" && pool {
        return Some("pool column beyond the BIND view");
    }
    if role.starts_with("GLUE") || role.starts_with("HASH") || role == "SAMP" {
        if pool {
            return Some("pool column beyond the role view");
        }
    }
    if role.starts_with("GLUE") && role.ends_with(":end") && (col == "carry" || col == "carry2") {
        return Some("GLUE end row: carry/carry2 feed only the next row of the same job and inactive slots");
    }
    if role.starts_with("GLUE") && role.ends_with(":mid") && ["q4", "q5", "q6", "q7"].iter().any(|q| role.contains(&format!(":{q}:"))) && col.starts_with('s') && col.len() == 2 {
        return Some("GLUE rows q >= 4 of a non-last block: the state pair is not on any bus");
    }
    if role == "SAMP:inv-operand-0" {
        return Some("SAMP is-zero gadget: the inverse column is free when its operand is 0");
    }
    if role.starts_with("HASH:") {
        let op = role.split(':').nth(1).unwrap_or("?");
        if col == "nwit" && matches!(op, "f" | "c" | "s") {
            return Some("T* HASH: nwit is read only on PoW rows (len, counter index, op_q inheritance)");
        }
        if col == "ctr" && matches!(op, "f" | "c") {
            return Some("T* HASH: ctr is read only on squeeze / PoW rows (counter unit, run counters)");
        }
    }
    if role.starts_with("HASH:") && role.ends_with(":hn0") && col == "nxt" {
        return Some("last hash-chain row: nxt is gated by hn = 0");
    }
    None
}

fn report(tag: &str, t: &BTreeMap<(String, String, String), Tally>) -> Vec<String> {
    let (mut tested, mut und) = (0, 0);
    let mut unexpected = vec![];
    let mut dc: BTreeMap<(String, String), (usize, Vec<String>)> = BTreeMap::new();
    for ((a, r, c), v) in t {
        tested += v.tested;
        und += v.undetected;
        if v.undetected > 0 {
            match dont_care(a, r, c) {
                Some(why) => {
                    let e = dc.entry((r.clone(), why.to_string())).or_default();
                    e.0 += v.undetected;
                    e.1.push(c.clone());
                }
                None => {
                    let s = format!("{a} role={r} col={c} undetected {}/{} (e.g. row {})", v.undetected, v.tested, v.example_row);
                    println!("NV_DOF_UNEXPECTED[{tag}] {s}");
                    unexpected.push(s);
                }
            }
        }
    }
    for ((r, why), (n, cols)) in &dc {
        let mut cols = cols.clone();
        cols.dedup();
        let cs = if cols.len() > 6 { format!("{} .. {} ({} cols)", cols[0], cols[cols.len() - 1], cols.len()) } else { cols.join(",") };
        println!("NV_DOF_DONTCARE[{tag}] role={r} cells={n} cols=[{cs}] : {why}");
    }
    // per-AIR summary
    let mut per: BTreeMap<String, (usize, usize, usize, usize)> = BTreeMap::new();
    for ((a, _, _), v) in t {
        let e = per.entry(a.clone()).or_default();
        e.0 += v.tested;
        e.1 += v.constraint;
        e.2 += v.bus;
        e.3 += v.undetected;
    }
    for (a, (n, c, b, u)) in per {
        println!("NV_DOF_SUMMARY[{tag}] {a}: cells={n} constraint={c} bus={b} undetected={u}");
    }
    println!("NV_DOF_TOTAL[{tag}] tested={tested} undetected={und} unexpected_groups={}", unexpected.len());
    unexpected
}

/// Memory-coupled perturbation over every ALU row with a free result (and a sample of others).
fn mem_pass(tag: &str, air: &AirRef<Sha384Config>, m: &RowMajorMatrix<F>, pvs: &[F]) -> Vec<String> {
    let w = m.width();
    let h = m.height();
    let idx: Vec<usize> = (0..NV_WIDTH).collect();
    let cm: &NvCommon<usize> = idx[..N_COMMON].borrow();
    let ab: &AbCols<usize> = idx[N_COMMON..N_COMMON + AB_W].borrow();
    let bc: &BindCols<usize> = idx[N_COMMON..N_COMMON + BIND_W].borrow();
    let g = |r: usize, c: usize| m.values[r * w + c];
    // readers per address and coefficient-independent column bases
    let mut readers: Vec<Vec<(usize, usize)>> = vec![vec![]; h]; // (row, base column of the 12 copies)
    let mut ops = vec![None; h];
    for r in 0..h {
        if g(r, cm.ka) == F::ONE {
            let lo = (0..OP_LO).find(|&k| g(r, ab.h[k]) == F::ONE).unwrap();
            let hi = (0..crate::nv::isa::OP_HI).find(|&k| g(r, ab.g[k]) == F::ONE).unwrap();
            let v = 8 * hi + lo;
            let op = Op::all().into_iter().find(|o| *o as usize == v);
            ops[r] = op;
            if let Some(op) = op {
                if op.reads_a() {
                    readers[g(r, cm.p[0]).as_canonical_u32() as usize].push((r, ab.a[0]));
                }
                if op.reads_b() {
                    let bf = g(r, cm.p[1]).as_canonical_u32() - ((op as u32) << ADDR_BITS);
                    readers[bf as usize].push((r, ab.b[0]));
                }
            }
        } else if g(r, cm.kb) == F::ONE {
            let ya = g(r, bc.ya).as_canonical_u32() as usize;
            let yb = g(r, bc.yb).as_canonical_u32() as usize;
            readers[ya].push((r, bc.e1a[0]));
            readers[ya + 1].push((r, bc.e1b[0]));
            readers[512 + yb].push((r, bc.e2[0]));
        }
    }
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut accepted = vec![];
    let mut tested = 0;
    for y in 0..h {
        let Some(op) = ops[y] else { continue };
        let free = matches!(op, Op::Load | Op::LoadF | Op::LoadBit | Op::Smp1 | Op::Smp12 | Op::Acc | Op::Dig | Op::PowChk | Op::SibWS4 | Op::SibWS2 | Op::DigWS4 | Op::DigWS2);
        let name = format!("{op:?}");
        let n = seen.entry(name.clone()).or_default();
        if !free && *n >= 8 {
            continue;
        }
        if free && *n >= 400 {
            continue;
        }
        *n += 1;
        for k in 0..12 {
            let rd: Vec<(usize, usize)> = readers[y].iter().map(|&(r, base)| (r, base + k)).collect();
            tested += 1;
            if mem_coupled(air, m, &rd, y, k, F::from_u32(12345 + k as u32), pvs) {
                let s = format!("{name} row {y} coeff {k} readers {}", rd.len());
                accepted.push(s);
            }
        }
    }
    // group
    let mut grp: BTreeMap<(String, usize, bool), usize> = BTreeMap::new();
    for s in &accepted {
        let parts: Vec<&str> = s.split(' ').collect();
        let rd: usize = parts[6].parse().unwrap();
        *grp.entry((parts[0].to_string(), parts[4].parse().unwrap(), rd > 0)).or_default() += 1;
    }
    for ((op, k, has_readers), n) in &grp {
        println!("NV_MEM_ACCEPTED[{tag}] op={op} coeff={k} has_readers={has_readers} rows={n}");
    }
    println!("NV_MEM_TOTAL[{tag}] tested={tested} accepted={}", accepted.len());
    // a consistent memory change accepted while the value is read is a real degree of freedom
    grp.into_iter().filter(|((_, _, r), _)| *r).map(|((op, k, _), n)| format!("{op} coeff {k} ({n} rows)")).collect()
}

fn cap() -> Option<usize> {
    match std::env::var("NV_DOF_CAP").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(48) {
        0 => None,
        c => Some(c),
    }
}

fn dof_case(tag: &str, vk: &MultiStarkVerifyingKey<Sha384Config>, proof: &Proof<Sha384Config>) -> Vec<String> {
    let t0 = std::time::Instant::now();
    let (airs, mats, pvs) = honest(vk, proof, 16);
    let (bad, unb) = global_check(&airs, &mats, &pvs);
    println!("NV_DOF_HONEST[{tag}] bad_constraints={bad} unbalanced_messages={unb}");
    assert_eq!((bad, unb), (0, 0), "evaluator must accept the honest trace");
    for (a, m) in airs.iter().zip(&mats) {
        println!("NV_DOF_AIR[{tag}] {} {} x {}", a.name(), m.height(), m.width());
    }
    let t = run_dof(&airs, &mats, &pvs, cap(), 0xC0FFEE);
    let mut bad = report(tag, &t);
    bad.extend(mem_pass(tag, &airs[0], &mats[0], &pvs[0]).into_iter().map(|s| format!("memory-coupled: {s}")));
    println!("NV_DOF_TIME[{tag}] {:.1}s", t0.elapsed().as_secs_f64());
    bad
}

#[test]
fn nv_dof_fib() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let bad = dof_case("fib", &vk, &proof);
    assert!(bad.is_empty(), "unexpected degrees of freedom: {bad:#?}");
}

#[test]
fn nv_dof_interactions_levers() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let lv = WhirLevers { gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, next_mask: true, whir_y: true, ..Default::default() };
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let engine = Sha384CpuEngine::new(with_levers(p, lv, 1, 5));
    let (vk, proof) = InteractionsFixture11.keygen_and_prove(&engine);
    let bad = dof_case("interactions-levers", &vk, &proof);
    assert!(bad.is_empty(), "unexpected degrees of freedom: {bad:#?}");
}

#[test]
fn nv_dof_whir_levers_x15() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let lv = WhirLevers { k_first: 1, keep_domain: true, multiproof: true, wide_query_pow: true, whir_y: true, ..Default::default() };
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let engine = Sha384CpuEngine::new(with_levers(p, lv, 15, 5));
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let bad = dof_case("whir-levers-x15", &vk, &proof);
    assert!(bad.is_empty(), "unexpected degrees of freedom: {bad:#?}");
}

// ---------------------------------------------------------------------------------------
// ALU / BIND tamper tests
// ---------------------------------------------------------------------------------------

fn debug_params() -> openvm_stark_backend::SystemParams {
    let mut p = crate::sha384::e2e_tests::parent_params_debug();
    p.max_constraint_degree = NvCircuit::new(3, 16, 1).layout().degree().max(6);
    p
}

/// Full debug check (all constraints, exact bus balance) of a trace set; panics on failure.
fn debug_check(airs: &[AirRef<Sha384Config>], mats: Vec<RowMajorMatrix<F>>, pvs: &[Vec<F>]) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::{AirProvingContext, ProvingContext};
    let ctxs: Vec<AirProvingContext<CpuBackend<Sha384Config>>> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| if pvs[i].is_empty() { AirProvingContext::simple_no_pis(m) } else { AirProvingContext::simple(m, pvs[i].clone()) })
        .collect();
    Sha384CpuEngine::new(debug_params()).debug(airs, &ProvingContext::new(ctxs.into_iter().enumerate().collect()));
}

fn must_fail(name: &str, f: impl FnOnce()) {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    assert!(r.is_err(), "tamper `{name}` accepted");
    println!("NV_TAMPER_REJECTED {name}");
}

struct Ix {
    cm: NvCommon<usize>,
    ab: AbCols<usize>,
    bc: BindCols<usize>,
}
fn ix() -> Ix {
    let idx: Vec<usize> = (0..NV_WIDTH).collect();
    let cm: &NvCommon<usize> = idx[..N_COMMON].borrow();
    let ab: &AbCols<usize> = idx[N_COMMON..N_COMMON + AB_W].borrow();
    let bc: &BindCols<usize> = idx[N_COMMON..N_COMMON + BIND_W].borrow();
    Ix {
        cm: NvCommon { ka: cm.ka, kb: cm.kb, kg: cm.kg, kh: cm.kh, ks: cm.ks, y: cm.y, p: cm.p },
        ab: AbCols { a: ab.a, b: ab.b, c: ab.c, h: ab.h, g: ab.g, wit: ab.wit, mult: ab.mult, rx: ab.rx, ry: ab.ry, rz: ab.rz, wit2: ab.wit2 },
        bc: BindCols { e1a: bc.e1a, e1b: bc.e1b, e2: bc.e2, acc: bc.acc, pc0: bc.pc0, pc1: bc.pc1, ya: bc.ya, yb: bc.yb, bl: bc.bl },
    }
}

fn op_of(m: &RowMajorMatrix<F>, r: usize, x: &Ix) -> Option<usize> {
    let w = m.width();
    let g = |c: usize| m.values[r * w + c];
    if g(x.cm.ka) != F::ONE {
        return None;
    }
    let lo = (0..OP_LO).find(|&k| g(x.ab.h[k]) == F::ONE)?;
    let hi = (0..crate::nv::isa::OP_HI).find(|&k| g(x.ab.g[k]) == F::ONE)?;
    Some(8 * hi + lo)
}

/// Relabel ALU row r to opcode `op` (one-hot halves) and set the B-field bytes (rx, ry, rz);
/// adjusts the byte-table multiplicities for the changed lookups.
fn relabel(mats: &mut [RowMajorMatrix<F>], r: usize, op: usize, rxyz: (F, F, F), x: &Ix) {
    let w = mats[0].width();
    let old = (mats[0].values[r * w + x.ab.rx], mats[0].values[r * w + x.ab.ry], mats[0].values[r * w + x.ab.rz]);
    for k in 0..OP_LO {
        mats[0].values[r * w + x.ab.h[k]] = F::from_bool(k == op % OP_LO);
    }
    for k in 0..crate::nv::isa::OP_HI {
        mats[0].values[r * w + x.ab.g[k]] = F::from_bool(k == op / OP_LO);
    }
    mats[0].values[r * w + x.ab.rx] = rxyz.0;
    mats[0].values[r * w + x.ab.ry] = rxyz.1;
    mats[0].values[r * w + x.ab.rz] = rxyz.2;
    // byte-pair table (AIR 3): row x + 256 y, multiplicity column 4
    let bt = &mut mats[3];
    let bw = bt.width();
    let mut bump = |a: F, b: F, d: i64| {
        let (a, b) = (a.as_canonical_u32() as usize, b.as_canonical_u32() as usize);
        if a >= 256 || b >= 256 {
            // not a table entry: this lookup cannot be balanced (the point of the tamper)
            println!("NV_RELABEL lookup ({a}, {b}) is outside the byte table");
            return;
        }
        let c = &mut bt.values[(a + 256 * b) * bw + 4];
        *c = if d > 0 { *c + F::ONE } else { *c - F::ONE };
    };
    bump(old.0, old.1, -1);
    bump(old.2, F::ZERO, -1);
    bump(rxyz.0, rxyz.1, 1);
    bump(rxyz.2, F::ZERO, 1);
}

/// B-field bytes forging B' = B + 2^ADDR_BITS (the relabel op -> op - 1).  With ADDR_BITS = 24
/// the B field is rx + 2^8 ry + 2^16 rz with rz looked up as a full byte (pair (rz, 0)), so the
/// only decompositions of B' need rz >= 256 (here rz = (B >> 16) + 2^(ADDR_BITS-16)), which is
/// outside the byte table.  The old 20-bit attack (rz = t/16, 65536 rz = 4096 t) cannot reach
/// B + 2^24 either: 4096 * 255 + 65535 < 2^24.
fn forge_b_plus_2_addr(b: u32) -> (F, F, F) {
    let t = b as u64 + (1u64 << ADDR_BITS);
    assert!(4096 * 255 + 65535 < (1u64 << ADDR_BITS));
    (F::from_u32((t & 255) as u32), F::from_u32(((t >> 8) & 255) as u32), F::from_u32((t >> 16) as u32))
}

/// Bug (fixed on this branch; regression kept for ADDR_BITS = 24): the 20-bit B-field range check `lookup_byte(16 rz)` accepts any
/// rz = t/16 (t a byte), so B ranges over [0, 1110015] instead of [0, 2^20) and an op can be
/// relabelled to op - 1 with B' = B + 2^20.  Zero -> Bit turns the equality assertion a == 0 into
/// a0 in {0, 1}: a child proof whose Gruen GKR s(3) = 1 (must be 0) is accepted.
#[test]
fn nv_alu_relabel_zero_to_bit() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let lv = WhirLevers { gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, ..Default::default() };
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let engine = Sha384CpuEngine::new(with_levers(p, lv, 1, 5));
    let (vk, proof) = InteractionsFixture11.keygen_and_prove(&engine);
    let mut bad = proof.clone();
    bad.gkr_proof.sumcheck_polys[0][0][2] += EF::ONE; // Gruen: s(3) must be zero
    let circ = NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let airs = circ.airs::<Sha384Config>();
    let (mut mats, b) = circ.generate(&vk, &bad);
    println!("NV_RELABEL program failures: {:?}", b.failures);
    assert!(!b.failures.is_empty());
    let x = ix();
    let w = mats[0].width();
    let zero = Op::Zero as usize;
    let rows: Vec<usize> = (0..mats[0].height())
        .filter(|&r| op_of(&mats[0], r, &x) == Some(zero) && (0..12).any(|k| mats[0].values[r * w + x.ab.a[k]] != F::ZERO))
        .collect();
    println!("NV_RELABEL failing Zero rows: {rows:?}");
    assert!(!rows.is_empty());
    for &r in &rows {
        let a: Vec<F> = (0..12).map(|k| mats[0].values[r * w + x.ab.a[k]]).collect();
        assert!(a[0] == F::ONE && a[1..].iter().all(|v| *v == F::ZERO), "Zero row {r} a = {a:?} is not the unit");
        let bf = mats[0].values[r * w + x.cm.p[1]].as_canonical_u32() - ((zero as u32) << ADDR_BITS);
        relabel(&mut mats, r, Op::Bit as usize, forge_b_plus_2_addr(bf), &x);
        for k in 0..12 {
            mats[0].values[r * w + x.ab.c[k]] = a[k]; // Bit: c = a
        }
        assert_eq!(mats[0].values[r * w + x.ab.mult], F::ZERO, "Zero results are never read");
    }
    let pvs = vec![vec![F::ONE], vec![], vec![], vec![]];
    must_fail("alu relabel Zero->Bit (forged B field)", || debug_check(&airs, mats, &pvs));
}

/// Same mechanism, Mul -> Nop (and Mul -> undefined op 29): a product is replaced by 0.  Uses a Mul
/// row whose honest product is already 0 so that no reader changes; the reads of the row are
/// removed from the memory multiplicities.
#[test]
fn nv_alu_relabel_mul_to_nop() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    for target in [Op::Nop as usize, 29] {
        let (airs, mut mats, pvs) = honest(&vk, &proof, 16);
        let x = ix();
        let w = mats[0].width();
        let mul = Op::Mul as usize;
        let r = (0..mats[0].height())
            .find(|&r| {
                op_of(&mats[0], r, &x) == Some(mul)
                    && (0..12).all(|k| mats[0].values[r * w + x.ab.c[k]] == F::ZERO)
            })
            .expect("a Mul row with zero product");
        let a_addr = mats[0].values[r * w + x.cm.p[0]].as_canonical_u32() as usize;
        let b_addr = (mats[0].values[r * w + x.cm.p[1]].as_canonical_u32() - (1 << ADDR_BITS)) as usize;
        relabel(&mut mats, r, target, forge_b_plus_2_addr(b_addr as u32), &x);
        mats[0].values[a_addr * w + x.ab.mult] -= F::ONE;
        mats[0].values[b_addr * w + x.ab.mult] -= F::ONE;
        must_fail(&format!("alu relabel Mul->op{target} (forged B field)"), || debug_check(&airs, mats, &pvs));
    }
}

/// Relabels that the op binding must reject with honest B-field bytes: a row to another opcode
/// (op 30), a Nop row to a reserved opcode (the former app-table Data op).
#[test]
fn nv_alu_relabel_misc() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let x = ix();
    // Const -> op 30 (undefined): B-field = P1 = 4 * 2^20 out of range
    {
        let (airs, mut mats, pvs) = honest(&vk, &proof, 16);
        let w = mats[0].width();
        let r = (0..mats[0].height()).find(|&r| op_of(&mats[0], r, &x) == Some(Op::Const as usize)).unwrap();
        let keep = (mats[0].values[r * w + x.ab.rx], mats[0].values[r * w + x.ab.ry], mats[0].values[r * w + x.ab.rz]);
        relabel(&mut mats, r, 30, keep, &x);
        must_fail("alu relabel Const->op30", || debug_check(&airs, mats, &pvs));
    }
    // Nop -> Rsv26 (reserved, c = 0 like Nop): P1 still encodes Nop, so the B field is negative
    {
        let (airs, mut mats, pvs) = honest(&vk, &proof, 16);
        let w = mats[0].width();
        let r = (0..mats[0].height()).rev().find(|&r| op_of(&mats[0], r, &x) == Some(Op::Nop as usize)).unwrap();
        let keep = (mats[0].values[r * w + x.ab.rx], mats[0].values[r * w + x.ab.ry], mats[0].values[r * w + x.ab.rz]);
        relabel(&mut mats, r, Op::Rsv26 as usize, keep, &x);
        must_fail("alu relabel Nop->Rsv26", || debug_check(&airs, mats, &pvs));
    }
    // public value: the Pv row asserts a0 == level
    {
        let (airs, mats, mut pvs) = honest(&vk, &proof, 16);
        pvs[0][0] += F::ONE;
        must_fail("alu public value (level)", || debug_check(&airs, mats, &pvs));
    }
}

/// BIND: alternative (ya, yb) decomposition of the same pair index and a premature last-row flag.
#[test]
fn nv_bind_tamper() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let x = ix();
    // ya + 2, yb - 2/512 (same y2 = ya + 512 yb); E1 copies refilled from the new addresses
    {
        let (airs, mut mats, pvs) = honest(&vk, &proof, 16);
        let w = mats[0].width();
        let r0 = (0..mats[0].height()).find(|&r| mats[0].values[r * w + x.cm.kb] == F::ONE).unwrap();
        let r = r0 + 5;
        let ya = mats[0].values[r * w + x.bc.ya].as_canonical_u32() as usize;
        mats[0].values[r * w + x.bc.ya] += F::from_u32(2);
        mats[0].values[r * w + x.bc.yb] -= F::from_u32(2) * F::from_u32(512).inverse();
        for k in 0..12 {
            mats[0].values[r * w + x.bc.e1a[k]] = mats[0].values[(ya + 2) * w + x.ab.c[k]];
            mats[0].values[r * w + x.bc.e1b[k]] = mats[0].values[(ya + 3) * w + x.ab.c[k]];
        }
        must_fail("bind alternative (ya, yb) decomposition", || debug_check(&airs, mats, &pvs));
    }
    // bl = 1 on a middle BIND row
    {
        let (airs, mut mats, pvs) = honest(&vk, &proof, 16);
        let w = mats[0].width();
        let r0 = (0..mats[0].height()).find(|&r| mats[0].values[r * w + x.cm.kb] == F::ONE).unwrap();
        mats[0].values[(r0 + 7) * w + x.bc.bl] = F::ONE;
        must_fail("bind premature last flag", || debug_check(&airs, mats, &pvs));
    }
}

fn ef(c: [F; 12]) -> EF {
    <EF as p3_field::BasedVectorSpace<F>>::from_basis_coefficients_slice(&c).unwrap()
}
fn cf(x: EF) -> [F; 12] {
    <EF as p3_field::BasedVectorSpace<F>>::as_basis_coefficients_slice(&x).try_into().unwrap()
}

/// Add `delta` to c of ALU row `y` and propagate it through readers that are linear in the
/// changed operand (Add, Sub, DblAdd, Mul with an unchanged other operand) down to Zero rows.
/// Returns false if another reader is met.
fn propagate(mats: &mut [RowMajorMatrix<F>], y: usize, delta: [F; 12], x: &Ix) -> bool {
    let w = mats[0].width();
    let h = mats[0].height();
    let mut work = vec![(y, delta)];
    for k in 0..12 {
        mats[0].values[y * w + x.ab.c[k]] += delta[k];
    }
    while let Some((addr, d)) = work.pop() {
        for r in 0..h {
            let Some(op) = op_of(&mats[0], r, x) else { continue };
            let Some(o) = Op::all().into_iter().find(|o| *o as usize == op) else { continue };
            let pa = mats[0].values[r * w + x.cm.p[0]].as_canonical_u32() as usize;
            let pb = (mats[0].values[r * w + x.cm.p[1]].as_canonical_u32() as i64 - ((op as i64) << ADDR_BITS)) as usize;
            let ra = o.reads_a() && pa == addr;
            let rb = o.reads_b() && pb == addr;
            if !ra && !rb {
                continue;
            }
            let get = |m: &RowMajorMatrix<F>, cols: [usize; 12]| -> [F; 12] { core::array::from_fn(|k| m.values[r * w + cols[k]]) };
            let (av, bv) = (get(&mats[0], x.ab.a), get(&mats[0], x.ab.b));
            let de = ef(d);
            let z = EF::ZERO;
            let (da, db) = (if ra { de } else { z }, if rb { de } else { z });
            let dc: EF = match o {
                Op::Add => da + db,
                Op::Sub => da - db,
                Op::DblAdd => da.double() + db,
                Op::Mul if !(ra && rb) => da * ef(bv) + ef(av) * db,
                Op::Zero => z,
                _ => return false,
            };
            for k in 0..12 {
                mats[0].values[r * w + x.ab.a[k]] += cf(da)[k];
                mats[0].values[r * w + x.ab.b[k]] += cf(db)[k];
            }
            if o != Op::Zero {
                for k in 0..12 {
                    mats[0].values[r * w + x.ab.c[k]] += cf(dc)[k];
                }
                work.push((r, cf(dc)));
            }
        }
    }
    true
}

/// Bug B3 (fixed on this branch): base-field loads were plain `Load` rows (all 12 coefficients
/// free, only c0 observed).  In `Builder::pow` the low limb l0 is such a load; its free
/// coefficient 1 absorbs any change of the recomposed limb 1, so the BIT rows need not equal the
/// limb received from the hash chain and the leading-zero check is vacuous.  Demonstrated on the
/// honest trace: one limb-1 bit is flipped and the difference is put into l0's coefficient 1.
/// Accepted with the pre-fix program (row emulated as `Load`), rejected with `LoadF`.
#[test]
fn nv_alu_base_load_pow() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let (airs, mats, pvs) = honest(&vk, &proof, 16);
    let x = ix();
    let w = mats[0].width();
    let yp = (0..mats[0].height()).find(|&r| op_of(&mats[0], r, &x) == Some(Op::PowChk as usize)).expect("child has PoW");
    let yl = yp + 1;
    assert_eq!(op_of(&mats[0], yl, &x), Some(Op::LoadF as usize), "pow low limb is a LoadF row");
    let yb = yl + 1;
    assert_eq!(op_of(&mats[0], yb, &x), Some(Op::LoadBit as usize), "first limb-1 bit row");
    let flip = |m: &mut Vec<RowMajorMatrix<F>>| -> bool {
        let bit = m[0].values[yb * w + x.ab.c[0]];
        let d = if bit == F::ZERO { F::ONE } else { -F::ONE };
        // the bit's change, propagated to the final Zero row
        let mut dl = [F::ZERO; 12];
        dl[0] = d;
        if !propagate(m, yb, dl, &x) {
            return false;
        }
        // compensate in l0: the final Zero row's operand must return to 0
        let zr = (yb..m[0].height())
            .find(|&r| op_of(&m[0], r, &x) == Some(Op::Zero as usize) && (0..12).any(|k| m[0].values[r * w + x.ab.a[k]] != F::ZERO))
            .unwrap();
        let comp: [F; 12] = core::array::from_fn(|k| -m[0].values[zr * w + x.ab.a[k]]);
        assert_eq!(comp[0], F::ZERO, "the difference sits in coefficient >= 1");
        propagate(m, yl, comp, &x)
    };
    // (A) pre-fix program: the l0 row is a plain Load (P1 = Load << 20).  Level-1 program: the
    //     binding tables are zero, so the BIND accumulator does not depend on the program words.
    {
        let mut m = mats.clone();
        let ld = Op::Load as usize;
        m[0].values[yl * w + x.cm.p[1]] = F::from_u32((ld as u32) << ADDR_BITS);
        relabel(&mut m, yl, ld, (F::ZERO, F::ZERO, F::ZERO), &x);
        let nb = (0..m[0].height()).find(|&r| m[0].values[r * w + x.cm.kb] == F::ONE).unwrap() + yl / 2;
        let pc = if yl % 2 == 0 { x.bc.pc0[1] } else { x.bc.pc1[1] };
        m[0].values[nb * w + pc] = m[0].values[yl * w + x.cm.p[1]];
        assert!(flip(&mut m));
        debug_check(&airs, m, &pvs);
        println!("NV_B3 pre-fix program (Load): PoW limb bits decoupled from the hash output, accepted");
    }
    // (B) this branch: LoadF forces c1..c11 = 0
    let mut m = mats;
    assert!(flip(&mut m));
    must_fail("pow low limb with extension junk (LoadF)", || debug_check(&airs, m, &pvs));
}

/// (F4) LogUp count bounds of NV's own vk at the fixed-point heights: every per-bus constraint
/// sum_a weight_a * h_a < p and the total interaction bound; message lengths <= 2^7.
#[test]
fn nv_logup_counts() {
    let circ = NvCircuit::new(3, 18, 1);
    let airs = circ.airs::<Sha384Config>();
    let mut p = crate::sha384::e2e_tests::params_from_env("PARENT", [19, 3, 20, 3]);
    p.max_constraint_degree = debug_params().max_constraint_degree;
    let engine = Sha384CpuEngine::new(p);
    let (_pk, vk) = engine.keygen(&airs);
    for (a, v) in airs.iter().zip(&vk.inner.per_air) {
        let ints = &v.symbolic_constraints.interactions;
        let maxlen = ints.iter().map(|i| i.message.len() + 1).max().unwrap_or(0);
        let w1 = ints.iter().filter(|i| i.count_weight > 0).count();
        println!("NV_LOGUP_AIR {} interactions={} weighted={} max_msg_len={}", a.name(), ints.len(), w1, maxlen);
        assert!(maxlen <= 1 << vk.inner.params.logup.log_max_message_length);
    }
    for heights in [[1usize << 18, 1 << 18, 64, 1 << 16], [1 << 19, 1 << 19, 64, 1 << 16]] {
        for (i, c) in vk.inner.trace_height_constraints.iter().enumerate() {
            let sum: u64 = heights.iter().zip(&c.coefficients).map(|(&h, &w)| h as u64 * w as u64).sum();
            println!("NV_LOGUP_CONSTRAINT heights={heights:?} #{i} coeffs={:?} sum={sum} (2^{:.2}) threshold={} ok={}", c.coefficients, (sum as f64).log2(), c.threshold, sum < c.threshold as u64);
            assert!(sum < c.threshold as u64);
        }
    }
}

/// (F3) statement passthrough at level >= 2: an NV level verifying an NV child re-exposes the
/// child's public values 1..19 (the base statement digest) unchanged; any other value is
/// rejected.  With NV_DOF_L2=1 also runs the single-cell perturbation over the level-2 trace
/// (pack + PvD rows, NV-child DAG).
#[test]
fn nv_statement_passthrough() {
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk0, p0) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let mut pp = openvm_stark_backend::test_utils::test_system_params_small(2, 16, 3);
    pp.max_constraint_degree = debug_params().max_constraint_degree;
    let parent = Sha384CpuEngine::new(pp);
    let circ1 = NvCircuit::new(3, 16, 1);
    let (vk1, p1, _b1, _) = super::circuit::prove_level(&circ1, &parent, &vk0, &p0);
    let child_pv = p1.public_values[0].clone();
    assert!(super::circuit::check_statement(&child_pv, &p0.public_values));
    let mut circ2 = NvCircuit::new(3, 19, 1);
    circ2.child_nv = true;
    circ2.test_no_bind = true; // the child is smaller than this level: passthrough only
    let airs = circ2.airs::<Sha384Config>();
    let (mats, b2) = circ2.generate(&vk1, &p1);
    assert!(b2.failures.is_empty(), "{:?}", b2.failures);
    let pv2 = b2.public_values();
    assert_eq!(pv2[1..], child_pv[1..], "statement digest passed through");
    assert!(super::circuit::check_statement(&pv2, &p0.public_values));
    let pvs = vec![pv2.clone(), vec![], vec![], vec![]];
    debug_check(&airs, mats.clone(), &pvs);
    println!("NV_PASSTHROUGH honest level 2 ok");
    for k in [1usize, 7, 12, 13, 18] {
        let mut bad = pvs.clone();
        bad[0][k] += F::ONE;
        must_fail(&format!("level-2 exposed statement limb {k}"), || debug_check(&airs, mats.clone(), &bad));
    }
    if std::env::var("NV_DOF_L2").is_ok() {
        let (bad_c, unb) = global_check(&airs, &mats, &pvs);
        assert_eq!((bad_c, unb), (0, 0));
        let t = run_dof(&airs, &mats, &pvs, cap(), 0xBEEF);
        let bad = report("level2-passthrough", &t);
        assert!(bad.is_empty(), "{bad:#?}");
    }
}

/// §W: every generated program has complete Horner chains (HornS HornR* HornE, contiguous), and
/// the assertion in `Builder::finish` rejects a broken one.
#[test]
fn nv_horner_chain_shape() {
    use super::isa::Instr;
    let engine = Sha384CpuEngine::new(child_params_small());
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let circ = NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
    let (_, b) = circ.generate(&vk, &proof);
    let chains = b.instrs.iter().filter(|i| i.op == Op::HornS).count();
    let rs = b.instrs.iter().filter(|i| i.op == Op::HornR).count();
    println!("NV_HORNER chains={chains} HornR rows={rs} program={}", b.instrs.len());
    assert!(chains > 0);
    super::builder::assert_horner_chains(&b.instrs);
    // a HornR whose predecessor is not a chain op, and a dangling HornS, are rejected
    let r = b.instrs.iter().position(|i| i.op == Op::HornR).unwrap();
    let mut bad = b.instrs.clone();
    bad[r - 1] = Instr::NOP;
    must_fail("HornR without predecessor", || super::builder::assert_horner_chains(&bad));
    let mut bad = b.instrs.clone();
    let e = bad.iter().position(|i| i.op == Op::HornE).unwrap();
    bad[e] = Instr::NOP;
    must_fail("chain without HornE", || super::builder::assert_horner_chains(&bad));
}

/// §W: DOF on a child with stacked width >= 2 (n_stack 3), whose program has Horn2 rows.
#[test]
fn nv_dof_horn2() {
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 3, 3);
    p.max_constraint_degree = 4;
    let engine = Sha384CpuEngine::new(p);
    let (vk, proof) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&engine);
    let bad = dof_case("horn2", &vk, &proof);
    assert!(bad.is_empty(), "unexpected degrees of freedom: {bad:#?}");
}

/// §X (G1 invariant): the generated program depends only on the child vk and shape.  Two proofs
/// with different statements (hence different transcripts, samples, rejections, PoW witnesses
/// and query indices) give byte-identical programs, for every lever set used by the suite.
#[test]
fn nv_program_identity_levers() {
    use crate::sha384::e2e_tests::with_levers;
    use openvm_stark_backend::WhirLevers;
    let mk = |lv: WhirLevers, x15: usize| {
        let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
        p.max_constraint_degree = 4;
        with_levers(p, lv, x15, 5)
    };
    let cases: Vec<(&str, openvm_stark_backend::SystemParams)> = vec![
        ("small (logup PoW)", child_params_small()),
        ("gruen+derive+next_mask+whir_y", mk(WhirLevers { gruen_gkr: true, gkr_derive_claims: true, gruen_zerocheck: true, next_mask: true, whir_y: true, ..Default::default() }, 1)),
        ("k1+keep+multiproof+wide_pow+whir_y, x15", mk(WhirLevers { k_first: 1, keep_domain: true, multiproof: true, wide_query_pow: true, whir_y: true, ..Default::default() }, 15)),
        ("tight+next_mask+multiproof, x15", mk(WhirLevers { tight_heights: true, next_mask: true, multiproof: true, whir_y: true, ..Default::default() }, 15)),
    ];
    for (name, p) in cases {
        let engine = Sha384CpuEngine::new(p);
        let progs: Vec<Vec<super::isa::Instr>> = [(0u64, 1u64), (2, 3), (5, 8)]
            .iter()
            .map(|&(a, b)| {
                let (vk, proof) = FibFixture::new(a, b, 1 << 5).keygen_and_prove(&engine);
                let circ = NvCircuit::new(vk.inner.params.k_whir(), 16, 1);
                let (_, bld) = circ.generate(&vk, &proof);
                assert!(bld.failures.is_empty(), "{name}: {:?}", bld.failures);
                bld.instrs
            })
            .collect();
        println!("NV_G1 {name}: program rows {}, identical across 3 statements: {}", progs[0].len(), progs.windows(2).all(|w| w[0] == w[1]));
        assert!(progs.windows(2).all(|w| w[0] == w[1]), "{name}: program depends on the proof");
    }
}

/// Native risk R5 (pq-nv-preprocessed DESIGN §7): with the tight-heights lever, the device
/// `commit` commits every matrix tight, but the verifier's proof shape lays cached parts out
/// non-tight (`StackedLayout::new`).  A cached trace with a zero tail committed tight therefore
/// yields a proof the native verifier rejects (completeness), while the same trace committed
/// non-tight verifies.  Soundness is unaffected: the verifier only ever uses its own layout.
#[test]
fn native_r5_cached_tight_commit() {
    use std::sync::Arc;
    use openvm_stark_backend::{
        prover::{stacked_pcs::stacked_commit_odd, AirProvingContext, ColMajorMatrix, CommittedTraceData, CpuColMajorBackend, ProvingContext},
        test_utils::{CachedFixture11, TestFixture},
        StarkProtocolConfig, WhirLevers,
    };
    struct TailFixture {
        config: Sha384Config,
        tight: bool,
    }
    impl TestFixture<Sha384Config> for TailFixture {
        fn airs(&self) -> Vec<AirRef<Sha384Config>> {
            CachedFixture11::new(self.config.clone()).airs()
        }
        fn generate_proving_ctx(&self) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
            let col = |v: &[usize]| ColMajorMatrix::new(v.iter().map(|&x| F::from_usize(x)).collect(), 1);
            // sender: count | field, rows 4..8 zero (tight height 4 < 8); receiver as CachedFixture11
            let pairs = [
                (col(&[0, 3, 7, 546, 0, 0, 0, 0]), col(&[1, 5, 4, 889, 0, 0, 0, 0])),
                (col(&[1, 3, 4, 2, 0, 545, 1, 0]), col(&[5, 4, 4, 5, 123, 889, 889, 456])),
            ];
            let params = self.config.params();
            ProvingContext::new(
                pairs
                    .into_iter()
                    .map(|(common, cached)| {
                        let (commit, data) = stacked_commit_odd(
                            self.config.hasher(),
                            params.l_skip,
                            params.n_stack,
                            params.log_blowup,
                            params.whir.k_first(),
                            params.whir.domain_odd_factor,
                            &[&cached],
                            self.tight,
                        )
                        .unwrap();
                        AirProvingContext {
                            cached_mains: vec![CommittedTraceData { commitment: commit, trace: cached, data: Arc::new(data) }],
                            common_main: common,
                            public_values: vec![],
                        }
                    })
                    .enumerate()
                    .collect(),
            )
        }
    }
    let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 8, 3);
    p.max_constraint_degree = 4;
    let p = crate::sha384::e2e_tests::with_levers(p, WhirLevers { tight_heights: true, ..Default::default() }, 1, 5);
    let engine = Sha384CpuEngine::new(p);
    for tight in [false, true] {
        let fx = TailFixture { config: engine.config().clone(), tight };
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (vk, proof) = fx.keygen_and_prove(&engine);
            engine.verify(&vk, &proof).map_err(|e| format!("{e:?}"))
        }));
        let outcome = match &r {
            Ok(Ok(())) => "verifies".to_string(),
            Ok(Err(e)) => format!("rejected: {e}"),
            Err(_) => "prover panicked".to_string(),
        };
        println!("NV_R5 cached trace committed tight={tight}: {outcome}");
        if !tight {
            assert!(matches!(r, Ok(Ok(()))), "non-tight cached commit must verify");
        } else {
            assert!(!matches!(r, Ok(Ok(()))), "R5: expected a mismatch for a tight cached commit");
        }
    }
}

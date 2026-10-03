//! Toy AIRs for conformance tests (milestone M1).

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

use crate::air::{Air, Expr as E, Table};
use crate::field::F;

/// `pub(i) + 256·pub(i+1) + 2^16·pub(i+2) + 2^24·pub(i+3)`
fn pub_u32(i: usize) -> E {
    let mut e = E::Pub(i);
    for k in 1..4 {
        e = E::add(e, E::mul(E::c(1 << (8 * k)), E::Pub(i + k)));
    }
    e
}

/// Fibonacci: columns (a, b); a_0 = pub0, b_0 = pub1, (a,b)' = (b, a+b),
/// last b = u32le(pub2..pub6).
pub fn fib_table(max_log: usize) -> Table {
    let first = |e| E::mul(E::IsFirst, e);
    let trans = |e| E::mul(E::IsTransition, e);
    Table {
        name: "fib".into(),
        width: 2,
        constraints: vec![
            first(E::sub(E::col(0), E::Pub(0))),
            first(E::sub(E::col(1), E::Pub(1))),
            trans(E::sub(E::nxt(0), E::col(1))),
            trans(E::sub(E::nxt(1), E::add(E::col(0), E::col(1)))),
            E::mul(E::IsLast, E::sub(E::col(1), pub_u32(2))),
        ],
        interactions: vec![],
        max_log,
    }
}

pub fn fib_air() -> Air {
    Air { tables: vec![fib_table(22)], num_buses: 0, num_pub: 6 }
}

pub fn fib_trace(log_n: usize, a0: u32, b0: u32) -> (RowMajorMatrix<F>, F) {
    let n = 1 << log_n;
    let mut v = Vec::with_capacity(2 * n);
    let (mut a, mut b) = (F::new(a0), F::new(b0));
    for _ in 0..n {
        v.push(a);
        v.push(b);
        let c = a + b;
        a = b;
        b = c;
    }
    (RowMajorMatrix::new(v, 2), a)
}

pub fn fib_claim(a0: u8, b0: u8, last: F) -> Vec<u8> {
    use p3_field::PrimeField32;
    let mut cb = vec![a0, b0];
    cb.extend_from_slice(&last.as_canonical_u32().to_le_bytes());
    cb
}

/// Cube chain of width `w`: column c satisfies x'_c = x_c^3 + c (degree 4 with
/// the selector: 3 quotient chunks), first row x_c = c + 2.
pub fn cube_table(w: usize, max_log: usize) -> Table {
    let mut cs = vec![];
    for c in 0..w {
        let cube = E::mul(E::col(c), E::mul(E::col(c), E::col(c)));
        cs.push(E::mul(E::IsTransition, E::sub(E::nxt(c), E::add(cube, E::c(c as u64)))));
        cs.push(E::mul(E::IsFirst, E::sub(E::col(c), E::c(c as u64 + 2))));
    }
    Table { name: "cube".into(), width: w, constraints: cs, interactions: vec![], max_log }
}

pub fn cube_trace(w: usize, log_n: usize) -> RowMajorMatrix<F> {
    let n = 1 << log_n;
    let mut v = vec![F::ZERO; w * n];
    for c in 0..w {
        let mut x = F::from_u64(c as u64 + 2);
        for r in 0..n {
            v[r * w + c] = x;
            x = x * x * x + F::from_u64(c as u64);
        }
    }
    RowMajorMatrix::new(v, w)
}

/// A multi-table toy exercising mixed heights (several classes and roll-ins):
/// fib (2^log_fib rows), cube(3) (2^log_cube rows), cube(1) (2 rows).
pub fn multi_air() -> Air {
    Air { tables: vec![fib_table(22), cube_table(3, 22), cube_table(1, 22)], num_buses: 0, num_pub: 6 }
}

/// Bus toy (range lookup): table `rng` (2^log_r rows) has `v = row index`
/// and 4 multiplicity-bit columns, receiving `[v]` on bus 0 with
/// multiplicity `Σ m_k 2^k`; table `use` (2^log_u rows) has columns
/// `(x, s)` and sends `[x]` with multiplicity bit `s` (and `[x+1]` on bus 1,
/// received by a third table with single-bit multiplicity `[1]`).
pub fn bus_air() -> Air {
    use crate::air::Interaction;
    let mut rng = Table {
        name: "rng".into(),
        width: 5,
        constraints: vec![
            E::mul(E::IsFirst, E::col(0)),
            E::mul(E::IsTransition, E::sub(E::nxt(0), E::add(E::col(0), E::c(1)))),
        ],
        interactions: vec![Interaction {
            bus: 0,
            mult: (1..5).map(E::col).collect(),
            msg: vec![E::col(0)],
            send: false,
        }],
        max_log: 22,
    };
    let mut usr = Table {
        name: "use".into(),
        width: 2,
        constraints: vec![],
        interactions: vec![
            Interaction { bus: 0, mult: vec![E::col(1)], msg: vec![E::col(0)], send: true },
            Interaction { bus: 1, mult: vec![E::c(1)], msg: vec![E::add(E::col(0), E::c(1))], send: true },
        ],
        max_log: 22,
    };
    let mut sink = Table {
        name: "sink".into(),
        width: 1,
        constraints: vec![],
        interactions: vec![Interaction { bus: 1, mult: vec![E::c(1)], msg: vec![E::col(0)], send: false }],
        max_log: 22,
    };
    for t in [&mut rng, &mut usr, &mut sink] {
        let b = crate::aux::bit_constraints(t);
        t.constraints.extend(b);
    }
    Air { tables: vec![rng, usr, sink], num_buses: 2, num_pub: 0 }
}

/// Honest traces for `bus_air`; `xs` are the looked-up values (< 2^log_r,
/// each used ≤ 15 times), `len(xs) ≤ 2^log_u`.
pub fn bus_traces(log_r: usize, log_u: usize, xs: &[u32]) -> Vec<RowMajorMatrix<F>> {
    let nr = 1usize << log_r;
    let nu = 1usize << log_u;
    let mut cnt = vec![0u32; nr];
    let mut usr = vec![F::ZERO; 2 * nu];
    let mut sink = vec![F::ZERO; nu];
    for (i, &x) in xs.iter().enumerate() {
        cnt[x as usize] += 1;
        usr[2 * i] = F::new(x);
        usr[2 * i + 1] = F::ONE;
    }
    for i in 0..nu {
        sink[i] = usr[2 * i] + F::ONE;
    }
    let mut rng = vec![F::ZERO; 5 * nr];
    for v in 0..nr {
        rng[5 * v] = F::new(v as u32);
        for k in 0..4 {
            rng[5 * v + 1 + k] = F::new((cnt[v] >> k) & 1);
        }
    }
    vec![RowMajorMatrix::new(rng, 5), RowMajorMatrix::new(usr, 2), RowMajorMatrix::new(sink, 1)]
}

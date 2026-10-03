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

//! Fixed lookup tables (preprocessed, verifier-computed):
//!
//! * `byte`: 256 rows, preprocessed `(x, class(x), x >> 4, x & 15)`; provides
//!   `BUS_RANGE8 (x)`, `BUS_CLASS (x, class)`, `BUS_NIB (x, hi, lo)`.
//! * `u16`: 65536 rows, preprocessed `x`; provides `BUS_RANGE16 (x)`.
//!
//! The main trace holds only the free multiplicities. The verifier rejects
//! any proof whose height for these tables differs from 256 / 65536 (the
//! preprocessed commitment is built for exactly that height).

use super::*;
use crate::consts::*;

pub const BYTE_PRE_WIDTH: usize = 4;
pub const BYTE_LOG_HEIGHT: usize = 8;
pub const U16_LOG_HEIGHT: usize = 16;

#[derive(Clone, Debug)]
pub struct ByteAir;

impl ByteAir {
    pub fn width(&self) -> usize {
        3
    }
    pub fn preprocessed<F: Field>(&self) -> RowMajorMatrix<F> {
        let mut v = Vec::with_capacity(256 * BYTE_PRE_WIDTH);
        for x in 0..256u32 {
            v.push(F::from_u32(x));
            v.push(F::from_u32(char_class(x as u8) as u32));
            v.push(F::from_u32(x >> 4));
            v.push(F::from_u32(x & 15));
        }
        RowMajorMatrix::new(v, BYTE_PRE_WIDTH)
    }
    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let p = b.preprocessed().clone();
        let pre = p.current_slice();
        let (x, cls, hi, lo): (AB::Expr, AB::Expr, AB::Expr, AB::Expr) =
            (pre[0].into(), pre[1].into(), pre[2].into(), pre[3].into());
        let r = Rows::<AB>::new(b, false);
        provide(b, BUS_RANGE8, vec![x.clone()], r.c(0));
        provide(b, BUS_CLASS, vec![x.clone(), cls], r.c(1));
        provide(b, BUS_NIB, vec![x, hi, lo], r.c(2));
    }
}

#[derive(Clone, Debug)]
pub struct U16Air;

impl U16Air {
    pub fn width(&self) -> usize {
        1
    }
    pub fn preprocessed<F: Field>(&self) -> RowMajorMatrix<F> {
        RowMajorMatrix::new((0..65536u32).map(F::from_u32).collect(), 1)
    }
    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let p = b.preprocessed().clone();
        let x: AB::Expr = p.current_slice()[0].into();
        let r = Rows::<AB>::new(b, false);
        provide(b, BUS_RANGE16, vec![x], r.c(0));
    }
}

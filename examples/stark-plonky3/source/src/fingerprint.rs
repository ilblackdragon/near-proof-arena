//! Schwartz–Zippel fingerprint of an AIR: every trace cell (current and next
//! row), preprocessed cell, public value and row selector is replaced by a
//! fixed pseudo-random element of the degree-8 extension (derived from
//! SHA-256 of a label), the AIR is evaluated once, and the sequence of
//! constraint values and bus interactions (bus name, tuple values, count
//! value) is hashed. Two AIRs whose constraint or interaction polynomials
//! differ get different fingerprints except with probability
//! ~ deg / |EF| ≈ 2^-240 per polynomial; the fingerprint is therefore a
//! stable identifier of the constraint system compiled into the verifier.

use crate::air::NpAir;
use crate::config::{Challenge, Val};
use p3_air::{Air, AirBuilder, BaseAir, RowWindow};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use p3_lookup::{Count, InteractionBuilder};
use sha2::Digest;

fn rand_ef(label: &str, i: usize) -> Challenge {
    let d: [u8; 32] = sha2::Sha256::digest(format!("np-stark-fp/{label}/{i}").as_bytes()).into();
    let coeffs: Vec<Val> =
        (0..8).map(|j| Val::from_u32(u32::from_le_bytes(d[4 * j..4 * j + 4].try_into().unwrap()))).collect();
    <Challenge as BasedVectorSpace<Val>>::from_basis_coefficients_slice(&coeffs).unwrap()
}

struct Fp<'a> {
    main: RowWindow<'a, Challenge>,
    pre: RowWindow<'a, Challenge>,
    pvs: &'a [Challenge],
    sel: [Challenge; 3],
    h: sha2::Sha256,
}

fn put(h: &mut sha2::Sha256, x: Challenge) {
    for c in <Challenge as BasedVectorSpace<Val>>::as_basis_coefficients_slice(&x) {
        h.update(c.as_canonical_u32().to_le_bytes());
    }
}

impl<'a> AirBuilder for Fp<'a> {
    type F = Val;
    type Expr = Challenge;
    type Var = Challenge;
    type PreprocessedWindow = RowWindow<'a, Challenge>;
    type MainWindow = RowWindow<'a, Challenge>;
    type PublicVar = Challenge;
    type PeriodicVar = Challenge;
    fn main(&self) -> Self::MainWindow {
        self.main
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.pre
    }
    fn is_first_row(&self) -> Challenge {
        self.sel[0]
    }
    fn is_last_row(&self) -> Challenge {
        self.sel[1]
    }
    fn is_transition(&self) -> Challenge {
        self.sel[2]
    }
    fn assert_zero<I: Into<Challenge>>(&mut self, x: I) {
        self.h.update(b"c");
        put(&mut self.h, x.into());
    }
    fn public_values(&self) -> &[Challenge] {
        self.pvs
    }
}

impl InteractionBuilder for Fp<'_> {
    fn push_interaction<E: Into<Challenge>>(
        &mut self,
        bus_name: &str,
        fields: impl IntoIterator<Item = E>,
        count: impl Into<Count<Challenge>>,
    ) {
        let (c, w) = count.into().into_parts();
        self.h.update(format!("i{bus_name}/{w}").as_bytes());
        for f in fields {
            put(&mut self.h, f.into());
        }
        put(&mut self.h, c);
    }
    fn push_local_interaction(
        &mut self,
        _t: impl IntoIterator<Item = (Vec<Challenge>, Count<Challenge>)>,
    ) {
        unimplemented!()
    }
}

pub fn fingerprint(air: &NpAir) -> [u8; 32] {
    let w = BaseAir::<Val>::width(air);
    let pw = BaseAir::<Val>::preprocessed_width(air);
    let cur: Vec<Challenge> = (0..w).map(|i| rand_ef("cur", i)).collect();
    let nxt: Vec<Challenge> = (0..w).map(|i| rand_ef("nxt", i)).collect();
    let pc: Vec<Challenge> = (0..pw).map(|i| rand_ef("pcur", i)).collect();
    let pn: Vec<Challenge> = (0..pw).map(|i| rand_ef("pnxt", i)).collect();
    let pvs: Vec<Challenge> = (0..air.num_pv()).map(|i| rand_ef("pv", i)).collect();
    let mut b = Fp {
        main: RowWindow::from_two_rows(&cur, &nxt),
        pre: RowWindow::from_two_rows(&pc, &pn),
        pvs: &pvs,
        sel: [rand_ef("sel", 0), rand_ef("sel", 1), rand_ef("sel", 2)],
        h: sha2::Sha256::new(),
    };
    air.eval(&mut b);
    b.h.finalize().into()
}

//! The AIRs of the transfer-batch STARK.
//!
//! Nine tables are proven together in one `p3-batch-stark` proof and linked
//! by LogUp buses (`consts::BUS_*`):
//!
//! | table | rows | role |
//! |---|---|---|
//! | `sha`  | one SHA-256 compression | hashes every message; padding, chaining, digest |
//! | `rcpt` | one receipt | parses/serialises receipts, outcomes, refunds; arithmetic; domain checks |
//! | `mrk`  | one outcome-merkle node | nearcore `merklize` shape and hashing |
//! | `sort` | one receipt id (sorted) | receipt ids pairwise distinct |
//! | `acct` | one touched account | account values pre/post, key nibbles |
//! | `node` | one revealed trie node | node serialisation pre/post, edges, value slots |
//! | `path` | one key nibble of one account | trie walk from the root to the value slot |
//! | `byte` | 256 fixed rows | range-8, char class, nibble split tables |
//! | `u16`  | 65536 fixed rows | range-16 table |

pub mod acct;
pub mod fixed;
pub mod mrk;
pub mod node;
pub mod path;
pub mod rcpt;
pub mod sha;
pub mod sha_core;
pub mod sha_gen;
pub mod sort;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;

/// Column allocator: tables declare their layout once; the AIR and the trace
/// generator share it.
#[derive(Default)]
pub struct Alloc(pub usize);

impl Alloc {
    pub fn one(&mut self) -> usize {
        self.0 += 1;
        self.0 - 1
    }
    pub fn arr<const N: usize>(&mut self) -> [usize; N] {
        core::array::from_fn(|_| self.one())
    }
    pub fn vec(&mut self, n: usize) -> Vec<usize> {
        (0..n).map(|_| self.one()).collect()
    }
}

/// Row access helper.
pub struct Rows<AB: AirBuilder> {
    pub cur: Vec<AB::Var>,
    pub nxt: Vec<AB::Var>,
}

impl<AB: AirBuilder> Rows<AB> {
    pub fn new(b: &AB, need_next: bool) -> Self {
        let m = b.main();
        let cur = m.current_slice().to_vec();
        let nxt = if need_next { m.next_slice().to_vec() } else { Vec::new() };
        Rows { cur, nxt }
    }
    #[inline]
    pub fn c(&self, i: usize) -> AB::Expr {
        self.cur[i].into()
    }
    #[inline]
    pub fn n(&self, i: usize) -> AB::Expr {
        self.nxt[i].into()
    }
}

#[inline]
pub fn k<AB: AirBuilder>(x: u64) -> AB::Expr {
    AB::Expr::from_u64(x)
}

#[inline]
pub fn pv<AB: AirBuilder>(b: &AB, i: usize) -> AB::Expr {
    b.public_values()[i].into()
}

/// Little-endian integer from public-value bytes.
pub fn pv_le<AB: AirBuilder>(b: &AB, off: usize, len: usize) -> AB::Expr {
    let mut acc = AB::Expr::ZERO;
    for i in (0..len).rev() {
        acc = acc * AB::Expr::from_u32(256) + pv::<AB>(b, off + i);
    }
    acc
}

/// 16 digest limbs (big-endian 16-bit halves) from 32 byte expressions.
pub fn limbs_from_bytes<AB: AirBuilder>(bytes: &[AB::Expr]) -> Vec<AB::Expr> {
    assert_eq!(bytes.len(), 32);
    (0..16)
        .map(|j| bytes[2 * j].clone() * AB::Expr::from_u32(256) + bytes[2 * j + 1].clone())
        .collect()
}

pub fn pv_digest_limbs<AB: AirBuilder>(b: &AB, off: usize) -> Vec<AB::Expr> {
    let bytes: Vec<AB::Expr> = (0..32).map(|i| pv::<AB>(b, off + i)).collect();
    limbs_from_bytes::<AB>(&bytes)
}

/// Permutation send / lookup query: `+gate` (gate must be boolean).
#[inline]
pub fn send<AB: InteractionBuilder>(b: &mut AB, bus: &str, fields: Vec<AB::Expr>, gate: AB::Expr) {
    b.push_interaction(bus, fields, Count::bounded(gate, 1));
}

/// Permutation receive: `-gate` (gate must be boolean).
#[inline]
pub fn recv<AB: InteractionBuilder>(b: &mut AB, bus: &str, fields: Vec<AB::Expr>, gate: AB::Expr) {
    b.push_interaction(bus, fields, Count::bounded(-gate, 1));
}

/// Lookup query (`+gate`, gate boolean).
#[inline]
pub fn query<AB: InteractionBuilder>(b: &mut AB, bus: &str, fields: Vec<AB::Expr>, gate: AB::Expr) {
    send(b, bus, fields, gate);
}

/// Lookup table entry with a free multiplicity.
#[inline]
pub fn provide<AB: InteractionBuilder>(
    b: &mut AB,
    bus: &str,
    fields: Vec<AB::Expr>,
    mult: AB::Expr,
) {
    b.push_interaction(bus, fields, Count::provided(-mult));
}

/// Byte-wise little-endian addition `a + b + cin = s` with boolean carries
/// `cs[i]` (carry into limb i+1) and no carry out, all multiplied by `gate`.
pub fn assert_add_bytes<AB: AirBuilder>(
    bld: &mut AB,
    gate: AB::Expr,
    a: &[AB::Expr],
    b: &[AB::Expr],
    cin: AB::Expr,
    s: &[AB::Expr],
    cs: &[AB::Expr],
) {
    let n = a.len();
    assert!(b.len() == n && s.len() == n && cs.len() == n - 1);
    for i in 0..n {
        let c_in = if i == 0 { cin.clone() } else { cs[i - 1].clone() };
        let c_out = if i + 1 < n { cs[i].clone() } else { AB::Expr::ZERO };
        bld.assert_zero(
            gate.clone()
                * (a[i].clone() + b[i].clone() + c_in - s[i].clone()
                    - c_out * AB::Expr::from_u32(256)),
        );
    }
    for c in cs {
        bld.assert_zero(gate.clone() * c.clone() * (c.clone() - AB::Expr::ONE));
    }
}

/// `y = x * C` for a constant little-endian byte vector `cbytes`, with
/// carries `cs` (range-checked by the caller to < 2^16) and result bytes `y`
/// (range-checked by the caller). Every result byte above `y.len()` must be
/// zero (no overflow).
pub fn assert_mul_const<AB: AirBuilder>(
    bld: &mut AB,
    x: &[AB::Expr],
    cbytes: &[u8],
    y: &[AB::Expr],
    cs: &[AB::Expr],
) {
    // Positions 0..m_max; cs[m-1] is the carry into position m (1 <= m < m_max);
    // no carry into position 0 and none out of the last position.
    let m_max = x.len() + cbytes.len() - 1;
    assert_eq!(cs.len(), m_max - 1);
    for m in 0..m_max {
        let mut conv = AB::Expr::ZERO;
        for (j, &cj) in cbytes.iter().enumerate() {
            if m >= j && m - j < x.len() && cj != 0 {
                conv = conv + x[m - j].clone() * AB::Expr::from_u32(cj as u32);
            }
        }
        let c_in = if m == 0 { AB::Expr::ZERO } else { cs[m - 1].clone() };
        let c_out = if m + 1 < m_max { cs[m].clone() } else { AB::Expr::ZERO };
        let ym = if m < y.len() { y[m].clone() } else { AB::Expr::ZERO };
        bld.assert_zero(conv + c_in - ym - c_out * AB::Expr::from_u32(256));
    }
}

/// Number of carry columns `assert_mul_const` needs.
pub const fn mul_carries(xlen: usize, clen: usize) -> usize {
    xlen + clen - 2
}

/// Native counterpart of [`assert_mul_const`]: result bytes (len `ylen`) and
/// carries; `None` on overflow.
pub fn mul_const_native(x: &[u8], cbytes: &[u8], ylen: usize) -> Option<(Vec<u8>, Vec<u32>)> {
    let m_max = x.len() + cbytes.len() - 1;
    let mut y = vec![0u8; ylen];
    let mut cs = vec![0u32; m_max - 1];
    let mut carry: u64 = 0;
    for m in 0..m_max {
        let mut conv: u64 = 0;
        for (j, &cj) in cbytes.iter().enumerate() {
            if m >= j && m - j < x.len() {
                conv += x[m - j] as u64 * cj as u64;
            }
        }
        let t = conv + carry;
        let ym = (t & 255) as u8;
        if m < ylen {
            y[m] = ym;
        } else if ym != 0 {
            return None;
        }
        carry = t >> 8;
        if m + 1 < m_max {
            cs[m] = carry as u32;
        } else if carry != 0 {
            return None;
        }
    }
    Some((y, cs))
}

pub use acct::AcctAir;
pub use fixed::{ByteAir, U16Air};
pub use mrk::MrkAir;
pub use node::NodeAir;
pub use path::PathAir;
pub use rcpt::RcptAir;
pub use sha::ShaAir;
pub use sort::SortAir;

/// The instance order inside a proof (fixed).
pub const TABLES: [&str; 9] = ["sha", "rcpt", "mrk", "sort", "acct", "node", "path", "byte", "u16"];

#[derive(Clone)]
pub enum NpAir {
    Sha(ShaAir),
    Rcpt(RcptAir),
    Mrk(MrkAir),
    Sort(SortAir),
    Acct(AcctAir),
    Node(NodeAir),
    Path(PathAir),
    Byte(ByteAir),
    U16(U16Air),
}

/// All AIRs in instance order.
pub fn all_airs() -> Vec<NpAir> {
    vec![
        NpAir::Sha(ShaAir::new()),
        NpAir::Rcpt(RcptAir::new()),
        NpAir::Mrk(MrkAir::new()),
        NpAir::Sort(SortAir::new()),
        NpAir::Acct(AcctAir::new()),
        NpAir::Node(NodeAir::new()),
        NpAir::Path(PathAir::new()),
        NpAir::Byte(ByteAir),
        NpAir::U16(U16Air),
    ]
}

macro_rules! dispatch {
    ($s:expr, $a:ident => $e:expr) => {
        match $s {
            NpAir::Sha($a) => $e,
            NpAir::Rcpt($a) => $e,
            NpAir::Mrk($a) => $e,
            NpAir::Sort($a) => $e,
            NpAir::Acct($a) => $e,
            NpAir::Node($a) => $e,
            NpAir::Path($a) => $e,
            NpAir::Byte($a) => $e,
            NpAir::U16($a) => $e,
        }
    };
}

impl NpAir {
    pub fn name(&self) -> &'static str {
        match self {
            NpAir::Sha(_) => "sha",
            NpAir::Rcpt(_) => "rcpt",
            NpAir::Mrk(_) => "mrk",
            NpAir::Sort(_) => "sort",
            NpAir::Acct(_) => "acct",
            NpAir::Node(_) => "node",
            NpAir::Path(_) => "path",
            NpAir::Byte(_) => "byte",
            NpAir::U16(_) => "u16",
        }
    }
    pub fn uses_next(&self) -> bool {
        !matches!(self, NpAir::Sha(_) | NpAir::Byte(_) | NpAir::U16(_))
    }
    pub fn num_pv(&self) -> usize {
        match self {
            NpAir::Rcpt(_) | NpAir::Mrk(_) | NpAir::Node(_) => crate::consts::NUM_PV,
            _ => 0,
        }
    }
    /// Lookup-folding degree budget passed to
    /// `ProverData::from_airs_and_degrees_with_lookup_budgets` (0 = default).
    pub fn lookup_budget(&self) -> usize {
        match self {
            NpAir::Rcpt(_) | NpAir::Node(_) | NpAir::Acct(_) => 9,
            NpAir::Mrk(_) | NpAir::Sort(_) => 5,
            _ => 0,
        }
    }
}

impl<F: Field> BaseAir<F> for NpAir {
    fn width(&self) -> usize {
        dispatch!(self, a => a.width())
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            NpAir::Byte(a) => Some(a.preprocessed()),
            NpAir::U16(a) => Some(a.preprocessed()),
            _ => None,
        }
    }
    fn preprocessed_width(&self) -> usize {
        match self {
            NpAir::Byte(_) => fixed::BYTE_PRE_WIDTH,
            NpAir::U16(_) => 1,
            _ => 0,
        }
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        if self.uses_next() {
            (0..BaseAir::<F>::width(self)).collect()
        } else {
            Vec::new()
        }
    }
    fn num_public_values(&self) -> usize {
        NpAir::num_pv(self)
    }
}

impl<AB: AirBuilder + InteractionBuilder> Air<AB> for NpAir
where
    AB::F: Field,
{
    fn eval(&self, b: &mut AB) {
        dispatch!(self, a => a.eval(b))
    }
}

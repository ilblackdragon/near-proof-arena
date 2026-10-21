//! NV ALU instruction set.  One instruction per ALU row; every row writes its result
//! `c` (an Ext12 value) to memory address = its row index.  Program words:
//!   P0 = A  (operand address, or base-field immediate)
//!   P1 = B + 2^17 * op   (operand address, or small immediate)
//!   P2 = key1 (transcript index / SHA job id / key id)
//!   P3 = key2 (unit index / key id)
//! These four columns are the program; NV binds a child's program to its own by an
//! in-circuit multilinear evaluation (see DESIGN.md §2.1).

/// Address bits available for operand `B` in `P1`.
/// Address / B-field width: 24 bits (NvAir up to 2^24 rows; L1 over a real base needs > 2^20).
/// P1 = B + op * 2^24 < 40 * 2^24 < p, so the decomposition stays unique.
pub const ADDR_BITS: u32 = 24;
pub const MAX_ROWS: usize = 1 << ADDR_BITS;

#[repr(u32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Op {
    /// padding: c = 0, no reads (opcode 0 so padding contributes nothing to the binding sum)
    Nop = 0,
    /// c = a * b (Ext12)
    Mul = 1,
    /// c = a + b
    Add = 2,
    /// c = a - b
    Sub = 3,
    /// c = A (base immediate in coefficient 0)
    Const = 4,
    /// c = A * X (coefficient 1)
    ConstX = 5,
    /// c = free witness (bound by later uses)
    Load = 6,
    /// c = a; push c0 as felt unit of job P2 at unit index P3 (transcript observe)
    Unit1 = 7,
    /// anchor transcript job P2: send (2, P2, 0, 0, A = t_start, B = count, 0); c = 0
    Anchor = 8,
    /// c = a; push B (2 or 4) word units (limbs c[3i..3i+3]) of job P2 at unit index P3 + 2i
    UnitW = 9,
    /// c0 = sample at tidx P2 (c1..c11 = 0)
    Smp1 = 10,
    /// c = 12 samples at tidx P2..P2+11
    Smp12 = 11,
    /// c = a; push c0..c11 as felt units of SHA job P2 at unit index P3..P3+11
    Unit12 = 12,
    /// c = a * b + wit; push wit as felt unit of job P2 at unit index P3
    Horn = 13,
    /// start SHA job P2 with tag A; push length units (B bytes, 0) at unit index 0, 1
    Job = 14,
    /// c = a, a0 in {0,1}, a1..a11 = 0
    Bit = 15,
    /// assert a == 0; c = 0
    Zero = 16,
    /// c = digest pairs P3 .. P3 + B - 1 (B in {1, 2}) of job P2, received from the digest
    /// bus (6 limbs per pair; c[6..12] = 0 if B = 1)
    Dig = 17,
    /// start a Merkle-node job P2 (tag A = NODE_TAG; 12 word units pushed by UnitW); c = 0
    NodeJob = 18,
    /// c = binding accumulator total (last row)
    Acc = 19,
    /// c = 2a + b
    DblAdd = 20,
    /// c = a * b + a
    MulAddA = 21,
    /// c = a; a0 == public value 0 (the recursion level)
    Pv = 22,
    /// c = a; push 4 word units of job P2 at unit index P3 + 2i + 12 b0 (Merkle L/R by bit b)
    UnitWS4 = 23,
    /// c = a; push 2 word units of job P2 at unit index P3 + 2i + 12 b0
    UnitWS2 = 24,
    /// c = PoW output word 0 limbs of transcript job P2 (from the hash chain, slot chan 3)
    PowChk = 25,
    /// Reserved (was `Data`, the app-table data row; removed with G2): no semantics beyond c = 0
    /// (like Nop); never emitted.
    Rsv26 = 26,
    /// [agg] Declares that job P2 begins a new transcript chain.  c = 0; the row exists for its
    /// interaction only: the ALU sends (P2, 1) on the chain-start bus and the hash row consumes
    /// it as `is_first`, which makes chain starts program constants rather than free columns.
    ChainStart = 27,
    /// c = free witness bit: c0 in {0, 1}, c1..c11 = 0 (one row instead of Load + Bit)
    LoadBit = 28,
    /// c = free base-field witness: c1..c11 = 0 (a plain `Load` leaves all 12 coefficients
    /// free; base-field loads must use this op, FAITHFUL.md bug B3)
    LoadF = 29,
    /// c = a; push word unit c[0..3] (kind word) at unit index P3 and the 42-byte digest tail
    /// c[3..6] (kind UNIT_HALF) at P3 + 2 of job P2 (42-B commitment words 4, 5)
    UnitWT = 30,
    /// c = a; expose the statement digest: a's coefficients = public values 1..13 (P2 = 0, lo
    /// cell) or 13..19 with c6..c11 = 0 (P2 = 1, hi cell)  (final-soundness G1)
    PvD = 31,
    /// Merkle sibling, low digest cell: c = free witness (the sibling's 12 limbs); push word units
    /// c[0..12] at unit index P3 + 12 (1 - B) of job P2 (B = the path bit read at the B field).
    /// Replaces Load + one_minus + UnitWS4 (3 rows) for the sibling.  Also starts node job P2
    /// with tag P0 (= NODE_TAG) on the job bus, replacing the level's NodeJob row.
    SibWS4 = 32,
    /// Merkle sibling, high digest cell: as SibWS4 for 2 word units (c[0..6]; c[6..12] = 0).
    SibWS2 = 33,
    /// Merkle path, current digest, low cell: c = digest pairs 0, 1 of the child job P0 (digest
    /// bus), pushed as word units c[0..12] at P3 + 12 B of job P2 (B = the path bit). Replaces
    /// Dig + UnitWS4 (2 rows).
    DigWS4 = 34,
    /// As DigWS4 for the high cell: digest pair 2 of job P0, 2 word units (c[6..12] = 0).
    DigWS2 = 35,
    /// Horner start: c = a; the next row's c = a (the leading coefficient).
    HornS = 36,
    /// Horner step: c free (set by the previous row); the next row's c = c * b + a
    /// (b = the evaluation point, a = the next coefficient).
    HornR = 37,
    /// Horner end: c free (set by the previous HornR row); no transition.
    HornE = 38,
    /// Two Horner steps over base witnesses: c = a b^2 + w1 b + w2 (w1 = wit, w2 = wit2),
    /// pushing w2, w1 as felt units P3, P3 + 1 of job P2 (degree 3: NvAir stays within the SHA
    /// AIR's degree 9).
    Horn2 = 39,
}

pub const NUM_OPS: usize = 40;
/// Op code = 8 * hi + lo, hi < OP_HI (UAIR one-hot selector halves).
pub const OP_LO: usize = 8;
pub const OP_HI: usize = 5;

impl Op {
    pub fn all() -> [Op; NUM_OPS] {
        use Op::*;
        [
            Nop, Mul, Add, Sub, Const, ConstX, Load, Unit1, Anchor, UnitW, Smp1, Smp12, Unit12,
            Horn, Job, Bit, Zero, Dig, NodeJob, Acc, DblAdd, MulAddA, Pv, UnitWS4, UnitWS2, PowChk, Rsv26, ChainStart, LoadBit, LoadF, UnitWT, PvD, SibWS4, SibWS2, DigWS4, DigWS2, HornS, HornR, HornE, Horn2,
        ]
    }
    pub fn reads_a(self) -> bool {
        use Op::*;
        matches!(
            self,
            Mul | Add | Sub | Unit1 | UnitW | Unit12 | Horn | Bit | Zero | DblAdd
                | MulAddA | Pv | UnitWS4 | UnitWS2 | UnitWT | PvD | HornS | HornR | Horn2
        )
    }
    pub fn reads_b(self) -> bool {
        use Op::*;
        matches!(self, Mul | Add | Sub | Horn | DblAdd | MulAddA | UnitWS4 | UnitWS2 | SibWS4 | SibWS2 | DigWS4 | DigWS2 | HornR | Horn2)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Instr {
    pub op: Op,
    pub a: u32,
    pub b: u32,
    pub k1: u32,
    pub k2: u32,
}

impl Instr {
    pub const NOP: Instr = Instr {
        op: Op::Nop,
        a: 0,
        b: 0,
        k1: 0,
        k2: 0,
    };
    pub fn words(&self) -> [u32; 4] {
        assert!(self.b < (1 << ADDR_BITS), "B field overflow");
        [self.a, self.b + ((self.op as u32) << ADDR_BITS), self.k1, self.k2]
    }
}

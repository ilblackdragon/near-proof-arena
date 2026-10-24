//! Bounded ordered account ledger for the multi-list receipt circuit.
//!
//! One public table row per distinct receiver (16 slots, an explicit profile
//! bound: corpus max observed 10, not a universal NEAR bound). Private
//! running-balance registers thread through every receipt slot in application
//! order — list 0..k-1, slot 0..cap-1 — including across list boundaries.
//!
//! Per active receipt: exactly one table row matches by (name_len, all eight
//! padded 64-bit name words); the receipt's constrained before-balance must
//! equal that row's running register; locked/storage must equal the row's
//! public values (D0a transfers never touch them); the register advances to
//! the already-constrained arithmetic after-value. Registers start at the
//! rows' public initial balances, so the first touch needs no separate case
//! and repeated receivers are bound by construction. Active rows must be
//! matched at least once and have pairwise-distinct canonical names; inactive
//! rows are all zero. Public final balances must equal the final registers.
//!
//! This closes the forged-starting-balance hole for repeated receivers
//! within the already-constrained D0a transfer subset. It is NOT trie
//! membership of the table against the state root: that binding is
//! host-audited against the claim's prev_state_root (account-trie-path
//! export + audit_account_paths.py), with the table itself public in the
//! proof statement. Not full NEAR validity.
//!
//! Matching uses full padded name words: table rows are constrained to zero
//! padding beyond name_len, so a receipt with garbage receiver padding
//! matches no row and is rejected by the exactly-one constraint (the host
//! audit checks receipt padding independently). Inactive receipt slots match
//! no row because the match bit is ANDed with the slot-active bit. Comparison
//! outputs are read as MSB-bools only; `assert_zero` is used for whole-word
//! guards per the lane's lessons.
use binius_frontend::{CircuitBuilder, Wire};
pub use crate::receipt::U128;
pub const ACCOUNT_SLOTS: usize = 16;
/// active, name_len, name[8], balance lo/hi, locked lo/hi, storage lo/hi,
/// final balance lo/hi.
pub const ROW_WORDS: usize = 18;
pub const TABLE_WORDS: usize = ACCOUNT_SLOTS * ROW_WORDS;

pub struct Row {
    pub active: Wire,
    pub name_len: Wire,
    pub name: [Wire; 8],
    pub balance: U128,
    pub locked: U128,
    pub storage: U128,
}

pub struct Ledger {
    pub rows: Vec<Row>,
    pub final_balances: Vec<U128>,
    /// All public table words in statement order (row-major).
    pub words: Vec<Wire>,
}

/// Full padded-name equality as an MSB-bool: lengths equal and all eight
/// 64-bit words equal.
fn name_eq(b: &CircuitBuilder, len_a: Wire, a: &[Wire; 8], len_b: Wire, bb: &[Wire; 8]) -> Wire {
    let mut acc = b.icmp_eq(len_a, len_b);
    for j in 0..8 {
        acc = b.band(acc, b.icmp_eq(a[j], bb[j]));
    }
    acc
}

/// Public account table with row-validity constraints. Build BEFORE the
/// lists so the table words lead the public statement.
pub fn build(b: &CircuitBuilder) -> Ledger {
    let mut rows = Vec::with_capacity(ACCOUNT_SLOTS);
    let mut final_balances = Vec::with_capacity(ACCOUNT_SLOTS);
    let mut words = Vec::with_capacity(TABLE_WORDS);
    for r in 0..ACCOUNT_SLOTS {
        let s = b.subcircuit(format!("account-{r}"));
        let active = s.add_inout();
        let name_len = s.add_inout();
        let name: [Wire; 8] = core::array::from_fn(|_| s.add_inout());
        let balance: U128 = [s.add_inout(), s.add_inout()];
        let locked: U128 = [s.add_inout(), s.add_inout()];
        let storage: U128 = [s.add_inout(), s.add_inout()];
        let final_balance: U128 = [s.add_inout(), s.add_inout()];
        words.push(active);
        words.push(name_len);
        words.extend_from_slice(&name);
        words.extend_from_slice(&balance);
        words.extend_from_slice(&locked);
        words.extend_from_slice(&storage);
        words.extend_from_slice(&final_balance);
        // Whole-word boolean: active is exactly 0 or 1 (assert_zero, not
        // assert_false, so every bit is constrained).
        s.assert_zero(format!("active-boolean-{r}"), s.shr(active, 1));
        let act = s.shl(active, 63);
        let inactive = s.bnot(act);
        // Inactive rows are entirely zero (whole words).
        let fields: Vec<Wire> = [name_len]
            .into_iter()
            .chain(name.iter().copied())
            .chain(balance.iter().copied())
            .chain(locked.iter().copied())
            .chain(storage.iter().copied())
            .chain(final_balance.iter().copied())
            .collect();
        for (i, w) in fields.iter().enumerate() {
            s.assert_eq_cond(
                format!("inactive-zero-{r}-{i}"),
                *w,
                s.add_constant_64(0),
                inactive,
            );
        }
        // Active rows: 1 <= name_len <= 64 (MSB-bool logic only).
        let nonzero = s.icmp_ne(name_len, s.add_constant_64(0));
        let too_long = s.icmp_ugt(name_len, s.add_constant_64(64));
        let len_ok = s.band(nonzero, s.bnot(too_long));
        s.assert_true(format!("len-range-{r}"), s.bor(s.band(act, len_ok), inactive));
        // Active rows: zero name padding beyond name_len, byte-exact.
        for k in 0..64usize {
            let beyond = s.band(s.icmp_ugt(s.add_constant_64(k as u64), name_len), act);
            let byte = s.extract_byte(name[k / 8], (k % 8) as u32);
            s.assert_eq_cond(
                format!("name-padding-{r}-{k}"),
                byte,
                s.add_constant_64(0),
                beyond,
            );
        }
        rows.push(Row { active, name_len, name, balance, locked, storage });
        final_balances.push(final_balance);
    }
    // Pairwise-distinct canonical names among active rows: an inert
    // duplicate row must not verify either.
    for r1 in 0..ACCOUNT_SLOTS {
        for r2 in (r1 + 1)..ACCOUNT_SLOTS {
            let a1 = b.shl(rows[r1].active, 63);
            let a2 = b.shl(rows[r2].active, 63);
            let same = name_eq(
                b,
                rows[r1].name_len,
                &rows[r1].name,
                rows[r2].name_len,
                &rows[r2].name,
            );
            b.assert_false(
                format!("distinct-names-{r1}-{r2}"),
                b.band(b.band(same, a1), a2),
            );
        }
    }
    Ledger { rows, final_balances, words }
}

/// Initial registers: one per row, starting at the row's public initial
/// balance. Thread through `bind` in application order.
pub fn initial_registers(ledger: &Ledger) -> [U128; ACCOUNT_SLOTS] {
    core::array::from_fn(|r| ledger.rows[r].balance)
}

/// Bind one receipt slot against the table and advance every register.
/// `active` is the slot-active MSB-bool (slot index < list count). `matched`
/// accumulates per-row "matched some active receipt" MSB-bools.
#[allow(clippy::too_many_arguments)]
pub fn bind(
    b: &CircuitBuilder,
    ledger: &Ledger,
    regs: &mut [U128; ACCOUNT_SLOTS],
    matched: &mut [Wire; ACCOUNT_SLOTS],
    active: Wire,
    receiver_len: Wire,
    receiver: &[Wire; 8],
    before: &U128,
    locked: &U128,
    storage: &U128,
    after: &U128,
) {
    let one = b.add_constant_64(1);
    let zero = b.add_constant_64(0);
    let mut acc = zero;
    for r in 0..ACCOUNT_SLOTS {
        let row = &ledger.rows[r];
        let m = b.band(name_eq(b, row.name_len, &row.name, receiver_len, receiver), active);
        for j in 0..2 {
            // before == running register (the register starts at the row's
            // public initial balance, so first touch and repeats are one case).
            b.assert_eq_cond(format!("before-balance-{r}-{j}"), before[j], regs[r][j], m);
            // locked/storage are invariant for D0a transfers.
            b.assert_eq_cond(format!("locked-unchanged-{r}-{j}"), locked[j], row.locked[j], m);
            b.assert_eq_cond(format!("storage-unchanged-{r}-{j}"), storage[j], row.storage[j], m);
        }
        // Register update: the matched row advances to the constrained
        // after-value; all others hold.
        regs[r] = [
            b.select(m, after[0], regs[r][0]),
            b.select(m, after[1], regs[r][1]),
        ];
        matched[r] = b.bor(matched[r], m);
        // Materialized 0/1 word for the exactly-one sum.
        acc = b.iadd(acc, b.select(m, one, zero)).0;
    }
    // Exactly one row matches each active receipt; none matches inactive slots.
    b.assert_eq("exactly-one-match", acc, b.select(active, one, zero));
}

/// Final obligations: public final balances equal the final registers, and
/// every active row was matched by at least one active receipt (the table is
/// exactly the distinct receiver set).
pub fn finalize(
    b: &CircuitBuilder,
    ledger: &Ledger,
    regs: &[U128; ACCOUNT_SLOTS],
    matched: &[Wire; ACCOUNT_SLOTS],
) {
    for r in 0..ACCOUNT_SLOTS {
        for j in 0..2 {
            b.assert_eq(
                format!("final-balance-{r}-{j}"),
                ledger.final_balances[r][j],
                regs[r][j],
            );
        }
        let act = b.shl(ledger.rows[r].active, 63);
        b.assert_true(format!("row-covered-{r}"), b.bor(matched[r], b.bnot(act)));
    }
}

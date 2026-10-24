# Receipt arithmetic circuit kernel

2026-10-24. Work toward execution/hash binding, not a full receipt or NEAR proof.

`receipt_arithmetic.rs` constrains unsigned 128-bit arithmetic using two 64-bit
limbs. It checks credit without overflow (excluding exactly u128::MAX), the
locked-balance sum, storage coverage or storage <= 770, effective gas price
`min(receipt_price, block_price)`, burnt tokens and surplus/refund amounts.
System receipts bypass gas multiplication. The system flag is constrained to a
bit, but its equality to the receipt's predecessor and authenticated account/state
inputs remain the caller's obligation. Outputs are derived wires, suitable for
direct use in outcome serialization rather than host-computed copies.

Whole-word conditions use `assert_zero`; arithmetic carry/borrow and comparison
conditions use MSB predicates as required by the frontend. Carry chains pass the
API's carry mask (whose top bit is the carry into the next limb), not its low bit.

## Backend compatibility finding

The first version used the frontend's `imul` for six 64x64->128 products. The
actual LaBinius LIOP rejects such circuits: its IntMul channel has no oracle.
The failed run is preserved. Constant products now use checked shifts/additions,
remaining within supported relations. Every nonnegative shifted term and partial
sum must fit u128, which is equivalent to no overflow of the final nonnegative
constant product. No new arithmetic proof channel or security assumption is added.

The first shift/add run matched all oracle cases and rejected all 18,893 output/
flag mutations, then the separate proof attempt stopped at `TooFewColumns`:
the kernel packs to witness log 7, while this PCS requires at least log 8
(one column bit plus seven row bits). No arithmetic PCS proof was produced.
The final checker reports this unsupported geometry explicitly and returns after
constraint evaluation. Next combine it with the necessary outcome/hash relation;
we have not padded it with unrelated work just to obtain a proof.

The planned smoke test exposes arithmetic inputs and outputs publicly. Even once
it works, it would test the constraint/backend connection only, not PQ128,
privacy, useful succinctness, fresh-process serialization or NEAR validity.
The full-size strict hash measurements do not transfer to this new kernel.

## Independent cases and scope

`make_receipt_arithmetic.py` uses the preceding Python oracle to generate 2,910
cases: 2,138 real receipts, 324 balance edges, 162 gas edges, 30 storage edges and
256 deterministic random cases. Expectations: 2,699 valid, 211 invalid, with
173 positive burns. Synthetic arithmetic cases are not valid NEAR claim fixtures.
The native harness also mutates each of six output limbs and the system flag on
every accepted case; this exercises private/input domains and claimed outputs.

Still required: derive the system flag from the same receipt bytes, feed these
computed burnt/refund wires into the hashed outcome, bind gas context and
account/state inputs to the chunk, enforce receipt sourcing/ordering/access-key
and routing conditions, then integrate state/Wasm/history and composed security.
The preserved draft `receipt_outcome.rs` sketches the shared-wire serialization
and hashing step; it is not yet built or verified and is not result evidence.

Evidence: [receipt-arithmetic](evidence/receipt-arithmetic). Build the preserved
`near-receipt-arithmetic-check` and support module on the preceding stronger
backend. Generate the binary expectations with `make_receipt_arithmetic.py
RECEIPT_EXPORTS OUTPUT --report REPORT`, then pass OUTPUT to the checker.

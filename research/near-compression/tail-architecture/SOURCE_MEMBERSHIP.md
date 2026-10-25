# Receipt-list membership in claim-derived source roots

2026-10-24. Host-side audit matches **268 source lists across 64 original claims**,
with **2,571 negative checks**. The latest 804-receipt proof's public source digest
reaches its designated source root. A concrete research envelope carrying its
two-step path totals **244,900 bytes** (86 bytes beyond the 244,814-byte packet).
This adds a checked source-membership layer; it is not full chunk validity,
recursive history, or a proof of the native claim parser.

## Required hash chain

For destination shard `s` and receipt list `rs`:

```
item = SHA256(u64le(s) || BorshVec(rs))  # already proved by the list circuit
acc  = SHA256(item)                    # mandatory additional leaf hash
for (sibling, direction) in path:
    acc = SHA256(sibling || acc) if direction == 0 else SHA256(acc || sibling)
assert acc == expected_source_root
```

This follows `spec/lean/v3/NearSpecV3/ChunkValidationV0.lean::verifyReceiptProof`
and `rootFromPath`. Omitting the additional leaf hash fails every tested source.
Direction 0 puts the sibling on the left; direction 1 puts it on the right.
The destination shard and receipt count are already inside the hashed preimage.

## Expected-root provenance

`source-roots-export.rs` reads **only the verifier's claim bytes**, invokes
`v3::d0::prep_claim`, and emits source chunk keys, source shard IDs and expected
outgoing-receipt roots in application order. The existing native routine selects
source blocks/new chunks and performs the seeded shuffle. It is trusted native
code here; no new equivalence theorem or succinct proof of these checks is claimed.

A separate `source-auth-export.rs` reads the witness and selects the last entry
for each source key, matching the existing lenient witness semantics. The Python
audit checks those selections against the independently invoked claim-only export,
source/destination shards, distinct entry-key counts, source message bytes,
original list fixtures and each Merkle path. Roots/order must never be accepted
from an unauthenticated prover-supplied manifest. Claim hashes pin all 64 inputs.

## Packet and envelope checks

The packet's dense public vector independently matches its original fixture;
its digest words are decoded in the correct byte order and checked against the
claim-designated root through the exported path. The inner packet hash is exactly
the one accepted by the unchanged older verifier in `evidence/parallel-jl`
(1.499 s, backend roundtrip, four negative checks). This audit reuses that pinned
verification evidence; it does not claim to have reimplemented the lattice verifier.

`source_envelope.py` encodes:

```
NPSRC001 || u32(packet_bytes) || packet || u32(source_index)
         || u32(path_depth) || (u8(direction) || sibling32)*
```

`check_membership` checks exact framing, expected public bytes, destination shard,
path and expected source root, then returns the unchanged inner packet. **The
caller must also verify that inner proof against the same expected public bytes
and fixed local profile.** This helper alone is not a proof verifier. Eleven
framing/index/path/public-digest mutations reject in the large fixture.
The envelope remains a research codec, with no hostile C-decoder safety claim.

The original source is index 2 of `00-h10035-s3`, with 804 receipts and depth 2.
Other lists of that chunk are not thereby proved. The reported 3.00–3.11 s warm
readiness is still the inner relation's measurement; no combined claim parsing,
envelope validation or whole-chunk latency has been measured here.

## Remaining integration obligations

- Enforce the complete claim-derived source list sequence, including every list,
  duplicate-key semantics, source/destination routing and application order.
  A membership proof for one root does not establish those execution obligations.
- Bind authenticated account state and all state updates, context, complete
  outcomes and general runtime/Wasm execution.
- Integrate the public membership check with the production verifier or constrain
  it inside the recursive relation as required by the eventual history protocol.
- Establish bounded history, composed PQ security and the 1–2 second deadline.

Because the source digest is public, its path can potentially be checked by the
terminal verifier without enlarging the private circuit. Whether this remains
outside the circuit under recursive composition is an open design obligation.
The current SHA-based membership layer does not itself settle PQ security levels.

## Reproduction

The two Rust exporter sources and Cargo dependency description are archived in
`evidence/source-membership`. Build against the pinned owned-lane native source.
Run the roots exporter with `claim.bin OUTPUT.json`; run the authentication
exporter with `CASE_DIRECTORY OUTPUT.json`. Save one JSON per original case.
Then:

```
python3 audit_source_membership.py EXPORTS AUTH LISTS CLAIMS ROOTS \
  --packet PACKET --packet-case 00-h10035-s3 --packet-index 2 --output REPORT
python3 audit_source_envelope.py PACKET LIST_FIXTURE ROOTS_JSON AUTH_JSON ENVELOPE \
  --index 2 --capacity 1024
```

All paths above are explicit local inputs. Evidence includes consolidated root
and path exports, full audit report, envelope hash/size, source/binary hashes,
and the hash link to the previously verified inner packet. Generated binary
packets remain in scratch storage.

# Source-byte budget: correct profile, insufficient speedup

2026-10-24. A circuit-enforced source-size profile reduces SHA work but **does
not meet the 1–2 second target**. Keep the full-size packed relation as the
coverage baseline; this experiment does not justify assuming smaller NEAR lists.

## Profiles and validation

The public configuration is `(receipt capacity, mode)`. Mode 0 retains
`12 + 347*capacity` source bytes. Mode 1 allows `128*capacity` bytes: 131,072
bytes at 1,024 slots. An explicit unsigned comparison constrains the derived
serialized source length before hashing its bounded prefix. All receipt
name/key/refund shapes remain supported subject to the total byte limit.

NPLIST03 counts an additional eight bytes for capacity/mode. The verifier
reconstructs the fixed circuit from its expected configuration and rejects
mismatched selectors before importing the trusted-local C backend. Selectors
cannot supply arbitrary parameters or change the accepted statement.

Synthetic cap4 tests prove a 512-byte source exactly at the compact limit,
reject a 513-byte source at `.source-byte-cap`, and prove the latter with the
full profile. Both exports verify freshly. These are local boundary tests,
not accepted NEAR claims. Tiny profile setup needed column log <= witness
log minus 8; the large profile is unchanged. Initial ColumnTooShort failure is
retained alongside the successful evidence.

## Original 804-receipt list

| Measurement | Observation |
|---|---:|
| Source SHA block capacity | 5,553 -> 2,049 |
| Witness log | 23 -> 23 |
| Packet including selector | 244,814 B |
| Two initial warm readiness samples | 4.350 / 4.197 s |
| Instrumented warm readiness | 4.318 s |
| Fresh decode + verification | 1.489 s |
| Initial two-run process peak RSS | 12,627,236 KiB |

One CPU core; not p95. Cold construction/setup and original witness preprocessing
are excluded. The previous full source profile measured 4.543 s once. This small
set of observations does not isolate a reliable percentage speedup; it clearly
does not resolve the deadline. All exports retain the wider project's stronger
backend policy, without establishing composed PQ security.

The profiled circuit has **10,074,314 private words**, 11,273 public words,
44,536 constants, 3,530,668 AND constraints and 880,973 zero constraints.
The commitment still pads to the same domain. Reaching 8,388,608 private words
would remove 1,685,706 words (about 16.7%) and allow the next smaller packed
witness domain, assuming the public segment remains smaller. That is an
implementation threshold, not a claim that such a reduction is already possible.

Recorded prover stages (milliseconds):

| Stage | Time |
|---|---:|
| Pack witness | 50.1 |
| Commit | 641.6 |
| Bitwise / binary-product reduction | 1,078.1 |
| Wiring / shifts | 578.6 |
| Field switch | 198.1 |
| Opening / compression | 1,706.2 |
| Total | 4,260.4 |

Fresh verification needs no receipt witnesses, reproduces backend bytes and
rejects changed profile selectors, expected root, public root and proof tape.
Independent public-byte audits match the packets. Original source-root inclusion,
account/state authentication, full runtime and recursive history remain absent.
No full NEAR/PQ128 result is claimed.

## Next representation experiment

Do not keep reducing source capacity to chase the same padded domain.
The pinned frontend implements `select` using a binary-multiplication constraint;
packed concatenation uses many such selections. Compare an exact bitmask-select
construction and measure private-word/constraint counts plus full proof timing.
This must retain whole-word range checks, canonical suffixes, ordering, negative
fixtures and fixed-profile verification. Even a local latency win leaves source
inclusion, state/runtime and bounded PQ history as required integrations.

## Reproduce

Build `near-receipt-list-budget` with the documented native flags and isolated
backend. Use original `make_receipt_lists.py` fixtures; synthesize boundaries
with `make_receipt_list_boundaries.py OUTPUT`. The expected public format remains
`receipt_list_public.py`.

```
NEAR_EXPORT_DIR=EXPORT_DIR near-receipt-list-budget 1024 compact ORIGINAL_LIST
NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC near-receipt-list-budget 1024 compact
NEAR_EXPECT_REJECT=1 near-receipt-list-budget 4 compact SOURCE_513_BYTES
```

`full` selects the retained larger profile. Source, logs, hashes, boundary report
and stage timing evidence are in `evidence/source-byte-budget`.

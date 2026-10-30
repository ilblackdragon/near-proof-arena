# Versioned claim/witness envelope for `near-arena-claim-v3` / `near-arena-witness-v3`

Companion to [`claim-v3.md`](claim-v3.md). That file is pinned by digest in the signed challenge
(`challenges/chl_640ed008…json`, `claim_encoding.spec_digest`), so it is not edited. This file adds
an explicit schema-version field without changing any v3 byte format or any signed relation.

## 1. Formats

```
claim.bin   = bytes "near-arena-claim"   ‖ u32 schema_version ‖ body
witness.bin = bytes "near-arena-witness" ‖ u32 schema_version ‖ u8 encoding ‖ body
```

Conventions are those of `claim-v3.md` §1 (`bytes` = `u32` length ‖ raw bytes, little-endian
integers, strict decoding).

| schema_version | claim body | witness body |
|---|---|---|
| 3 | the `near-arena-claim-v3` file after its format tag (`claim-v3.md` §2) | `encoding = 0`: the `near-arena-witness-v3` file after its format tag (§3, state witness in the clear); `encoding = 1`: the `near-arena-cwitness-v3` file after its format tag (the distributed zstd `EncodedChunkStateWitness`, ≤ 48 MiB encoded, ≤ 64 MiB decoded) |

No other version or encoding is defined. A file with any other `schema_version` or `encoding` is
**rejected** (`invalid: unsupported … schema version` / `… encoding`); it is never decided as
version 3.

## 2. Legacy rule

A file that does not start with an envelope tag is an **unversioned file and has schema version 3**:

| first tag | schema_version | encoding |
|---|---|---|
| `near-arena-claim-v3` | 3 | — |
| `near-arena-witness-v3` | 3 | 0 |
| `near-arena-cwitness-v3` | 3 | 1 |

Unversioned files are passed to the existing decoders unchanged. The borsh length prefix of the
first tag already tells the two apart (envelope tags 16 and 18 bytes; legacy tags 19, 21 and 22
bytes).

## 3. Relation

The envelope is a transport format. Every relation stays the relation over the canonical v3 bytes.
In Lean (`spec/lean/v3/NearSpecV3/Successor/SchemaVersion.lean`):

* `normalizeClaim` / `normalizeWitness` rewrite an envelope to the canonical v3 file;
* `checkVersioned cfg c w = checkSuccessor cfg c' w'` after that rewrite;
* `checkVersioned_legacy`: on every input that does not start with an envelope tag (every existing
  file), `checkVersioned = checkSuccessor` — no verdict can move;
* `checkVersioned_versioned`: a version-3 envelope is decided exactly as its canonical file;
* `normalizeClaim_unsupported`, `normalizeWitness_bad_encoding`: other versions/encodings are errors.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

`nearspec-v3-check-successor` reads the envelope on every tier except `signed`, which keeps the
signed byte format exactly.

## 4. Schema gate

`tools/d3/claim_schema.py` decodes the header and checks the body structurally against
`claim-v3.md` §2/§3 (field order, lengths, option and flag tags, `n_blocks` flags, strictly
ascending epochs, no trailing bytes, the witness size caps). It runs in the `difftest-gates` CI job
on every committed fixture, with its self-test and a negative control
(`oracle/tools/test_claim_schema.py`).

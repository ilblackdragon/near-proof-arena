# Lane L5: the SHA-256 block table

Source of truth: `zk-formal/ZkFormal/Sha/Table.lean` (`Table.table busBytes busDigest`).
Layout: `Sha/Layout.lean`. Honest generator (the reference for L8's Rust trace
generator, column by column): `Sha/Gen.lean`.

## Shape

| Item | Value |
|---|---|
| Columns | 544 base columns, no extension columns |
| Constraints | 1011 user constraints (+17 multiplicity-bit booleanity constraints) |
| Max degree | 4 (`isFirst` counts as degree 1) |
| Interactions | 17: 16 byte receives, 1 digest provide |
| Rows | 1 start row `S` per message, then 17 rows per block (`R0..R15`, `D`), then all-zero padding |
| `maxLog` | 22 |
| `Air.wf 4` on a SHA-only AIR | true (`multBound = 17·2^22`, `fpBound ≈ 2^31.2`) |

Each round row `Rj` performs rounds `4j..4j+3` (OpenVM layout): it holds the
four new `a` words and four new `e` words as bits. The previous row plus the
current row form the 8-slot window of the spec sequences `As`/`Es`
(`Sha/Spec.lean`). Additions mod 2^32 are checked on 16-bit limbs, with 3-bit
carries. The schedule is checked on `R4..R15` using delayed helper columns.
A state row (`S` or `D`) holds the chaining value as `(d,c,b,a)` and `(h,g,f,e)`.
A `D` row holds `Hin + final working variables`.

Padding is checked locally. The table uses per-byte data flags `F`, a per-row
`Fprev`, a running data counter `Nd`, and the block flags `Last`, `P80` and
`Seen`. The `0x80` byte and the zero bytes are forced. The last block's words
14 and 15 are `0` and `8·len`, with `len < 2^25`.

## Bus contract (for L6)

* **bytes bus** (`busBytes`, the SHA table *receives*): on round rows `R0..R3`,
  the message is `(Id, pos, byte)` and the multiplicity is the single bit `F q`.
* **digest bus** (`busDigest`, the SHA table *sends*): on the `D` row of a last
  block, the message is `(Id, len, digest[0..32))` (digest bytes as field
  elements) and the multiplicity is the single bit `Dmult`. Each message's
  digest is provided at most once. A consumer that needs the same digest twice
  must hash the message twice.

The soundness statement L6 consumes is `sha_digest_contract`
(`Sha/Compose.lean`, closed form `Sha/Frame/All.lean`
`sha_digest_contract_of`). If the digest interaction is active on row `d`,
then:

* there is a claimed pair `(m, dg) ∈ digests tr t` with `dg = ArenaCore.sha256 m`;
* the digest message is exactly `(Id_d, |m|, dg)`;
* for every `i < |m|`, some row of the SHA table receives `(Id_d, i, m[i])` with multiplicity 1.

L6 then uses the balance of the bytes bus. If L6 sends `(Id, i, b_i)` for
`i < len` exactly once per `Id`, the received bytes are among the sent ones, so
`m = b`.

`Holds A pub tr` together with `A.tables[t] = Table.table busBytes busDigest`
gives `ShaLocal tr t pub` (`shaLocal_of_holds`).

## Completeness (for L7/L8)

`sha_complete`: for `msgs` with bytes `< 256`, lengths `< 2^25` and at most
2^22 rows, the trace `honestTrace msgs` has these properties:

* it satisfies every constraint;
* its multiplicity bits are boolean;
* its bus traffic is exactly `Gen.expectedBytes msgs` received and `Gen.expectedDigests msgs` sent.

Executable checks:

* `lake env lean --run zk-formal/test/ShaGenTest.lean`: 7 messages, padding edge cases, 0 violations, digests equal `ArenaCore.sha256`, 11/11 single-cell mutants caught;
* `test/ShaAirCheck.lean`: degree, `wf`, JSON export.

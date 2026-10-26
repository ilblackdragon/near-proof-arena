# GasKeyTarget: nearcore outcomes per step (4 runs)

| step | nearcore (first receipt; later failures) × runs |
|---|---|
| `00.add-gas-keys` | ok: ×4 |
| `01.fund-cross-shard` | ok: ×4 |
| `02.transfer-and-fund-cross-shard` | ok: ×4 |
| `03.fund-missing-key-cross-shard` | fail:key/account does not exist ×4 |
| `04.fund-regular-key-cross-shard` | fail:key/account does not exist ×4 |
| `05.ordinary-transfer-same-chunk` | ok: ×4 |
| `06.ordinary-call-same-chunk` | ok: ×4 |
| `07.gas-key-transfer-out-index0` | ok: ×4 |
| `08.gas-key-call-index1` | ok: ×4 |
| `09.gas-key-failing-call-deposit-index2` | fail:panic ×4 |
| `10.gas-key-transfer-out-index0-second` | ok: ×4 |
| `11.ordinary-receipts-same-chunk` | ok: ×4 |
| `12.fund-and-spend-same-chunk-fund` | ok: ×4 |
| `13.fund-and-spend-same-chunk-spend` | ok: +CodeDoesNotExist ×4 |
| `14.withdraw-partial` | ok: ×4 |
| `15.withdraw-too-much` | fail:insufficient gas-key balance ×4 |
| `16.delete-gas-key-small-balance` | ok: ×4 |
| `17.refund-to-deleted-gas-key-call` | fail:panic ×4 |
| `18.refund-to-deleted-gas-key-delete` | ok: ×4 |
| `19.create-fund-delete-small-cross-shard` | ok: ×4 |
| `20.create-fund-withdraw-cross-shard` | ok: ×4 |
| `21.create-fund-delete-too-much-cross-shard` | fail:GasKeyBalanceTooHigh ×4 |
| `22.create-fund-delete-account-cross-shard` | ok: ×4 |
| `23.create-fund-delete-account-too-much-cross-shard` | fail:GasKeyBalanceTooHigh ×4 |
| `24.new-account-gas-key-tx-cross-shard` | ok: ×4 |
| `25.new-account-gas-key-call-cross-shard` | ok: ×4 |
| `26.withdraw-zero-then-delete-funded` | fail:GasKeyBalanceTooHigh ×4 |
| `27.gas-key-call-emits-before-delete` | ok: +CodeDoesNotExist ×4 |
| `28.withdraw-all-then-delete` | ok: ×4 |
| `29.fund-deleted-gas-key-cross-shard` | fail:key/account does not exist ×4 |

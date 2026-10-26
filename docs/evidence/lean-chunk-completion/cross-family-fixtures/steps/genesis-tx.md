# GenesisTx: nearcore outcomes per step (4 runs)

| step | nearcore (first receipt; later failures) × runs |
|---|---|
| `00.emit-cross-shard-then` | ok: +panic ×7; ok: +panic (1 pending at run end) ×2; ok: (3 pending at run end) ×1; ok: +panic (4 pending at run end) ×1; ok: +panic (3 pending at run end) ×1 |
| `01.emit-then-panic` | fail:panic ×12 |
| `02.yield-create` | ok:cfd0547f (1 pending at run end) ×2; ok:26fe784f (1 pending at run end) ×2; ok:64dbd69d (1 pending at run end) ×2; ok:f1f7f2b8 (1 pending at run end) ×2; ok:44748ff1 (1 pending at run end) ×1; ok:6dac188f (1 pending at run end) ×1; ok:cc7af3e0 (1 pending at run end) ×1; ok:76e9975e (1 pending at run end) ×1 |
| `03.cross-shard-call-with-deposit` | ok: ×9; ok: (1 pending at run end) ×3 |
| `04.cross-shard-failing-call-refund` | fail:panic ×9; fail:panic (2 pending at run end) ×2; receipts pending at run end ×1 |
| `05.transfers-multi-action` | ok: ×9; ok: (1 pending at run end) ×2; receipts pending at run end ×1 |
| `06.create-sub-account-other-shard` | ok: ×9; ok: (1 pending at run end) ×2; receipts pending at run end ×1 |
| `07.deploy-and-call` | ok: ×12 |
| `08.add-and-fund-gas-key` | ok: ×12 |
| `09.state-init-missing-code` | fail:global contract not found ×9; fail:global contract not found (2 pending at run end) ×2; receipts pending at run end ×1 |
| `10.burn-cross-shard` | ok: ×9; ok: (1 pending at run end) ×2; receipts pending at run end ×1 |
| `11.delete-missing-key` | fail:Account ×12 |
| `20.emit-cross-shard-then` | ok: +panic ×5; ok: +panic (2 pending at run end) ×2; ok: +panic (1 pending at run end) ×2; ok: (3 pending at run end) ×1; ok: +panic (4 pending at run end) ×1; ok: +panic (3 pending at run end) ×1 |
| `21.emit-then-panic` | fail:panic ×12 |
| `22.yield-create` | ok:d7166d65 (1 pending at run end) ×2; ok:99e63ed2 (1 pending at run end) ×2; ok:a73164c3 (1 pending at run end) ×2; ok:c793bba1 (1 pending at run end) ×2; ok:cd5cdad4 (1 pending at run end) ×2; ok:de29a9e4 (1 pending at run end) ×1; ok:ce22eae1 (1 pending at run end) ×1 |
| `23.cross-shard-call-with-deposit` | ok: ×7; ok: (1 pending at run end) ×4; receipts pending at run end ×1 |
| `24.cross-shard-failing-call-refund` | fail:panic ×7; fail:panic (2 pending at run end) ×3; receipts pending at run end ×2 |
| `25.transfers-multi-action` | ok: ×9; ok: (1 pending at run end) ×2; receipts pending at run end ×1 |
| `26.create-sub-account-other-shard` | ok: ×7; ok: (1 pending at run end) ×3; receipts pending at run end ×2 |
| `27.deploy-and-call` | ok: ×11; ok: (1 pending at run end) ×1 |
| `28.add-and-fund-gas-key` | ok: ×11; ok: (1 pending at run end) ×1 |
| `29.state-init-missing-code` | fail:global contract not found ×9; fail:global contract not found (2 pending at run end) ×2; receipts pending at run end ×1 |
| `30.burn-cross-shard` | ok: ×8; ok: (1 pending at run end) ×3; receipts pending at run end ×1 |
| `31.delete-missing-key` | fail:Account ×12 |
| `40.emit-cross-shard-then` | ok: +panic (1 pending at run end) ×4; ok: +panic (4 pending at run end) ×3; ok: +panic (3 pending at run end) ×3; ok: +panic (2 pending at run end) ×1; ok: (3 pending at run end) ×1 |
| `41.emit-then-panic` | fail:panic ×11; fail:panic (1 pending at run end) ×1 |
| `42.yield-create` | ok:04a9d2b0 (1 pending at run end) ×1; ok:b1d59265 (1 pending at run end) ×1; ok:80f68f09 (1 pending at run end) ×1; ok:00f49151 (1 pending at run end) ×1; ok:466585d3 (1 pending at run end) ×1; ok:01d7c18c (1 pending at run end) ×1; ok:691af10f (1 pending at run end) ×1; ok:215f351b (1 pending at run end) ×1; ok:a915fd5f (1 pending at run end) ×1; ok:fe2e1381 (1 pending at run end) ×1; ok:261eaa82 (1 pending at run end) ×1; ok:f2fb978b (1 pending at run end) ×1 |
| `43.cross-shard-call-with-deposit` | ok: (1 pending at run end) ×6; ok: ×4; receipts pending at run end ×1; tx not executed ×1 |
| `44.cross-shard-failing-call-refund` | fail:panic (2 pending at run end) ×5; fail:panic ×4; receipts pending at run end ×2; tx not executed ×1 |
| `45.transfers-multi-action` | ok: (1 pending at run end) ×6; ok: ×5; receipts pending at run end ×1 |
| `46.create-sub-account-other-shard` | ok: (1 pending at run end) ×5; ok: ×4; receipts pending at run end ×3 |
| `47.deploy-and-call` | ok: ×11; tx not executed ×1 |
| `48.add-and-fund-gas-key` | ok: ×11; tx not executed ×1 |
| `49.state-init-missing-code` | fail:global contract not found ×6; fail:global contract not found (2 pending at run end) ×5; receipts pending at run end ×1 |
| `50.burn-cross-shard` | ok: (1 pending at run end) ×4; receipts pending at run end ×4; ok: ×4 |
| `51.delete-missing-key` | fail:Account ×12 |

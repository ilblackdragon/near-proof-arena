# RollbackRefund: nearcore outcomes per step (4 runs)

| step | nearcore (first receipt; later failures) × runs |
|---|---|
| `00.deploy-global-hash` | ok: ×4 |
| `01.deploy-global-account` | ok: ×4 |
| `02.use-global-account-init` | ok: ×4 |
| `03.r0.state-init-missing-global-code` | fail:global contract not found ×4 |
| `04.r0.state-init-then-emit` | fail:BalanceExceeded ×4 |
| `05.r0.state-init-insufficient-deposit` | fail:LackBalanceForState ×4 |
| `06.r0.create-use-global-init-fail` | fail:panic ×4 |
| `07.r0.emit-then-panic` | fail:panic ×4 |
| `08.r0.emit-to-failing-callee` | ok: +panic ×4 |
| `09.r0.create-deploy-init-ok` | ok: ×4 |
| `10.r0.create-deploy-init-fail` | fail:panic ×4 |
| `11.r0.call-fail-deposit-refund` | fail:panic ×4 |
| `12.r0.ordinary-transfer` | ok: ×4 |
| `13.r0.local-emit-then-panic` | fail:panic ×4 |
| `14.r0.local-use-global-call-emit` | ok: +panic ×4 |
| `15.r1.state-init-missing-global-code` | fail:global contract not found ×4 |
| `16.r1.state-init-then-emit` | fail:BalanceExceeded ×4 |
| `17.r1.state-init-insufficient-deposit` | fail:LackBalanceForState ×4 |
| `18.r1.create-use-global-init-fail` | fail:panic ×4 |
| `19.r1.emit-then-panic` | fail:panic ×4 |
| `20.r1.emit-to-failing-callee` | ok: +panic ×4 |
| `21.r1.create-deploy-init-ok` | ok: ×4 |
| `22.r1.create-deploy-init-fail` | fail:panic ×4 |
| `23.r1.call-fail-deposit-refund` | fail:panic ×4 |
| `24.r1.ordinary-transfer` | ok: ×4 |
| `25.r1.local-emit-then-panic` | fail:panic ×4 |
| `26.r1.local-use-global-call-emit` | ok: +panic ×4 |
| `27.r2.state-init-missing-global-code` | fail:global contract not found ×4 |
| `28.r2.state-init-then-emit` | fail:BalanceExceeded ×4 |
| `29.r2.state-init-insufficient-deposit` | fail:LackBalanceForState ×4 |
| `30.r2.create-use-global-init-fail` | fail:panic ×4 |
| `31.r2.emit-then-panic` | fail:panic ×4 |
| `32.r2.emit-to-failing-callee` | ok: +panic ×4 |
| `33.r2.create-deploy-init-ok` | ok: ×4 |
| `34.r2.create-deploy-init-fail` | fail:panic ×4 |
| `35.r2.call-fail-deposit-refund` | fail:panic ×4 |
| `36.r2.ordinary-transfer` | ok: ×4 |
| `37.r2.local-emit-then-panic` | fail:panic ×4 |
| `38.r2.local-use-global-call-emit` | ok: +panic ×4 |
| `39.r3.state-init-missing-global-code` | fail:global contract not found ×4 |
| `40.r3.state-init-then-emit` | fail:BalanceExceeded ×4 |
| `41.r3.state-init-insufficient-deposit` | fail:LackBalanceForState ×4 |
| `42.r3.create-use-global-init-fail` | fail:panic ×4 |
| `43.r3.emit-then-panic` | fail:panic ×4 |
| `44.r3.emit-to-failing-callee` | ok: +panic ×4 |
| `45.r3.create-deploy-init-ok` | ok: ×4 |
| `46.r3.create-deploy-init-fail` | fail:panic ×4 |
| `47.r3.call-fail-deposit-refund` | fail:panic ×4 |
| `48.r3.ordinary-transfer` | ok: ×4 |
| `49.r3.local-emit-then-panic` | fail:panic ×4 |
| `50.r3.local-use-global-call-emit` | ok: +panic ×4 |

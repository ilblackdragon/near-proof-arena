# host-rows steps and nearcore receipt kinds

Seed 811 (the other three seeds give the same kinds per step). Kinds come from nearcore's stored
outcome tree (`xfam-0.json`), classified by `tools/d3/collect_xfam.py`; `value(ccc=r)` is a
`ccc` receipt whose returned first byte is `current_contract_code`'s result.

| step | signer → receiver | actions | receipt kinds (transaction receipt first) |
|---|---|---|---|
| `00.ccc.local` | s0hrow → s0hrow | FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value(ccc=1), value |
| `01.ccc.local.cross-shard` | s3hrall → s1hrow | FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value(ccc=1), value |
| `11.rta.self` | s0hrow → s0hrow | FunctionCall(rta, 0 B args, 20 Tgas, deposit 0) | value, value |
| `02.deploy-global-hash` | s0hrow → s0hrow | DeployGlobalContract(1134 B, CodeHash) | value, value |
| `03.deploy-global-account` | s3hrgacc → s3hrgacc | DeployGlobalContract(1134 B, AccountId) | value, value |
| `12.rta.cross-shard` | s1hrow → s0hrow | FunctionCall(rta, 0 B args, 20 Tgas, deposit 0) | value, value |
| `14.psr.transfer-absent` | s0hrow → s0hrow | FunctionCall(psr, 18 B args, 30 Tgas, deposit 0) | value, AccountDoesNotExist, value, value, value |
| `15.psr.transfer-ok` | s0hrow → s0hrow | FunctionCall(psr, 16 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `16.psr.call-rta-other` | s0hrow → s0hrow | FunctionCall(psr, 15 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `17.psr.call-rta-self` | s1hrow → s1hrow | FunctionCall(psr, 15 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `18.psr.bad-promise-index` | s0hrow → s0hrow | FunctionCall(psr, 16 B args, 30 Tgas, deposit 0) | HostError(InvalidPromiseIndex), value |
| `19.psr.joint-promise` | s1hrow → s1hrow | FunctionCall(psr, 16 B args, 30 Tgas, deposit 0) | HostError(CannotSetRefundToOnJointPromise), value |
| `20.psr.invalid-refund-id` | s0hrow → s0hrow | FunctionCall(psr, 11 B args, 30 Tgas, deposit 0) | HostError(InvalidAccountId), value |
| `21.psr.absent-refund-and-target` | s1hrow → s1hrow | FunctionCall(psr, 19 B args, 30 Tgas, deposit 0) | value, AccountDoesNotExist, value, AccountDoesNotExist, value |
| `23.iter-prefix` | s0hrow → s0hrow | FunctionCall(itp, 0 B args, 20 Tgas, deposit 0) | HostError(Deprecated), value |
| `24.iter-range` | s1hrow → s1hrow | FunctionCall(itr, 0 B args, 20 Tgas, deposit 0) | HostError(Deprecated), value |
| `25.iter-next` | s0hrow → s0hrow | FunctionCall(itn, 0 B args, 20 Tgas, deposit 0) | HostError(Deprecated), value |
| `26.iter-none` | s1hrow → s1hrow | FunctionCall(itok, 0 B args, 20 Tgas, deposit 0) | value, value |
| `28.gas.0` | s0hrow → s0hrow | FunctionCall(gas, 4 B args, 20 Tgas, deposit 0) | value, value |
| `04.use-global-hash` | s2hrglob → s2hrglob | UseGlobalContract(CodeHash(8ctNng2Q17V25tBf67pRPVpxNwxsGbRMShvzn8sEUN7t)) | value, value |
| `05.use-global-account` | s1hrgbya → s1hrgbya | UseGlobalContract(AccountId(AccountId("s3hrgacc"))) | value, value |
| `06.use-global-hash+ccc` | s3hrglob → s3hrglob | UseGlobalContract(CodeHash(8ctNng2Q17V25tBf67pRPVpxNwxsGbRMShvzn8sEUN7t)), FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value, value |
| `07.deploy+ccc` | s1hrdep → s1hrdep | DeployContract(1134 B), FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value, value |
| `27.iter-prefix.cross-shard` | s3hrall → s1hrow | FunctionCall(itp, 0 B args, 20 Tgas, deposit 0) | HostError(Deprecated), value |
| `29.gas.1000` | s1hrow → s1hrow | FunctionCall(gas, 4 B args, 20 Tgas, deposit 0) | value, value |
| `30.gas.23e6` | s1hrow → s1hrow | FunctionCall(gas, 4 B args, 20 Tgas, deposit 0) | value, value |
| `31.gas.over-prepaid` | s0hrow → s0hrow | FunctionCall(gas, 4 B args, 20 Tgas, deposit 0) | HostError(GasExceeded), value |
| `35.kg.addfull` | s2hrkg → s2hrkg | FunctionCall(addfull, 33 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `36.kg.addfc` | s2hrkg → s2hrkg | FunctionCall(addfc, 33 B args, 30 Tgas, deposit 0) | NewReceiptValidationError, value |
| `32.gas.1e6.300tgas` | s1hrow → s1hrow | FunctionCall(gas, 4 B args, 300 Tgas, deposit 0) | value, value |
| `33.gas.u32max.300tgas` | s0hrow → s0hrow | FunctionCall(gas, 4 B args, 300 Tgas, deposit 0) | HostError(GasLimitExceeded), value |
| `43.all.300tgas` | s3hrall → s3hrall | FunctionCall(run, 0 B args, 300 Tgas, deposit 0) | value, AccountDoesNotExist, AccountDoesNotExist, value, value, value |
| `34.gas.300000.cross-shard` | s3hrall → s0hrow | FunctionCall(gas, 4 B args, 300 Tgas, deposit 0) | value, value |
| `37.kg.fund` | s2hrkg → s2hrkg | FunctionCall(fund, 33 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `38.kg.addfund` | s2hrkg → s2hrkg | FunctionCall(addfund, 33 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `39.kg.fund-missing` | s2hrkg → s2hrkg | FunctionCall(fund, 33 B args, 30 Tgas, deposit 0) | value, GasKeyDoesNotExist, value, value, value |
| `40.kg.addfull-malformed` | s2hrkg → s2hrkg | FunctionCall(addfull, 4 B args, 30 Tgas, deposit 0) | HostError(InvalidPublicKey), value |
| `44.all.20tgas` | s3hrall → s3hrall | FunctionCall(run, 0 B args, 20 Tgas, deposit 0) | HostError(GasExceeded), value |
| `41.kg.fundto` | s2hrkg → s2hrkg | FunctionCall(fundto, 40 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `42.kg.addfull.cross-shard` | s0hrow → s2hrkg | FunctionCall(addfull, 33 B args, 30 Tgas, deposit 0) | value, value, value, value |
| `08.ccc.global-hash` | s2hrglob → s2hrglob | FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value(ccc=2), value |
| `09.ccc.global-account` | s1hrgbya → s1hrgbya | FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value(ccc=3), value |
| `45.all.300tgas.cross-shard` | s0hrow → s3hrall | FunctionCall(run, 0 B args, 300 Tgas, deposit 0) | value, AccountDoesNotExist, AccountDoesNotExist, value, value, value |
| `10.ccc.global-account.cross-shard` | s0hrow → s1hrgbya | FunctionCall(ccc, 0 B args, 20 Tgas, deposit 0) | value(ccc=3), value |
| `13.rta.global-hash` | s3hrall → s2hrglob | FunctionCall(rta, 0 B args, 20 Tgas, deposit 0) | value, value |
| `22.psr.global-account` | s1hrgbya → s1hrgbya | FunctionCall(psr, 16 B args, 30 Tgas, deposit 0) | value, value, value, value |

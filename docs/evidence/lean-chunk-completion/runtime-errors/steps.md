| step | signer → receiver | actions | nearcore receipt kinds |
|---|---|---|---|
| `00.call.s0rtload` | s0rtload → s0rtload | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LoadingError ×1, value ×2 |
| `01.call.s1rtfita` | s1rtfita → s1rtfita | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | value ×2 |
| `02.call.s1rtovra` | s1rtovra → s1rtovra | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LoadingError ×1, value ×2 |
| `03.call.s2rtfitb` | s2rtfitb → s2rtfitb | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | value ×2 |
| `04.call.s2rtovrb` | s2rtovrb → s2rtovrb | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LoadingError ×1, value ×2 |
| `05.call.s3rtfitc` | s3rtfitc → s3rtfitc | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | value ×2 |
| `06.call.s3rtovrc` | s3rtovrc → s3rtovrc | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LoadingError ×1, value ×2 |
| `07.call.s0rtcombo` | s0rtcombo → s0rtcombo | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LoadingError ×1, value ×2 |
| `08.call.s1rtlink` | s1rtlink → s1rtlink | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LinkError ×1, value ×2 |
| `09.call.s2rtbadty` | s2rtbadty → s2rtbadty | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LinkError ×1, value ×2 |
| `10.cross-shard-call.s0rtload` | s3rtx → s0rtload | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LoadingError ×1, value ×2 |
| `11.cross-shard-call.s1rtlink` | s3rtx → s1rtlink | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000000000000000000000000) | LinkError ×1, value ×2 |
| `12.emit-then.s0rtload` | s3rtx → s3rtx | FunctionCall(emit, 16 B args, 60 Tgas, deposit 0) | LoadingError ×1, value ×6 |
| `13.emit-then.s1rtlink` | s3rtx → s3rtx | FunctionCall(emit, 16 B args, 60 Tgas, deposit 0) | LinkError ×1, value ×6 |
| `17.missing-method.s0rtload` | s0rtload → s0rtload | FunctionCall(absent, 0 B args, 20 Tgas, deposit 0) | LoadingError ×1, value ×1 |
| `18.missing-method.s1rtlink` | s1rtlink → s1rtlink | FunctionCall(absent, 0 B args, 20 Tgas, deposit 0) | LinkError ×1, value ×1 |
| `14.emit-then.s1rtfita` | s3rtx → s3rtx | FunctionCall(emit, 16 B args, 60 Tgas, deposit 0) | value ×6 |
| `19.missing-method.s3rtovrc` | s3rtovrc → s3rtovrc | FunctionCall(absent, 0 B args, 20 Tgas, deposit 0) | LoadingError ×1, value ×1 |
| `15.emit-then.s0rtcombo+s2rtovrb` | s3rtx → s3rtx | FunctionCall(emit, 31 B args, 60 Tgas, deposit 0) | LoadingError ×2, value ×8 |
| `20.low-gas.s0rtload` | s0rtload → s0rtload | FunctionCall(main, 0 B args, 0 Tgas, deposit 0) | LoadingError ×1, value ×1 |
| `21.low-gas.s1rtlink` | s1rtlink → s1rtlink | FunctionCall(main, 0 B args, 0 Tgas, deposit 0) | HostError(GasExceeded) ×1, value ×1 |
| `16.emit-then.s2rtbadty+s3rtfitc` | s3rtx → s3rtx | FunctionCall(emit, 31 B args, 60 Tgas, deposit 0) | LinkError ×1, value ×8 |
| `22.low-gas.s1rtfita` | s1rtfita → s1rtfita | FunctionCall(main, 0 B args, 0 Tgas, deposit 0) | HostError(GasExceeded) ×1, value ×1 |
| `23.low-gas.s2rtovrb` | s2rtovrb → s2rtovrb | FunctionCall(main, 0 B args, 0 Tgas, deposit 0) | LoadingError ×1, value ×1 |
| `24.transfer-then-call.s1rtovra` | s3rtx → s1rtovra | Transfer(1000000000000000000000000), FunctionCall(main, 0 B args, 20 Tgas, deposit 0) | LoadingError ×1, value ×2 |
| `25.call-then-transfer.s0rtload` | s3rtx → s0rtload | FunctionCall(main, 0 B args, 20 Tgas, deposit 0), Transfer(1000000000000000000000000) | LoadingError ×1, value ×2 |
| `26.call-call.s2rtovrb` | s2rtovrb → s2rtovrb | FunctionCall(main, 0 B args, 20 Tgas, deposit 0), FunctionCall(main, 0 B args, 20 Tgas, deposit 0) | LoadingError ×1, value ×1 |
| `27.call-call.s1rtfita` | s1rtfita → s1rtfita | FunctionCall(main, 0 B args, 20 Tgas, deposit 0), FunctionCall(main, 0 B args, 20 Tgas, deposit 0) | value ×2 |
| `28.transfer-then-call.s1rtlink` | s3rtx → s1rtlink | Transfer(1000000000000000000000000), FunctionCall(main, 0 B args, 20 Tgas, deposit 0) | LinkError ×1, value ×2 |
| `29.deploy-call.rtunk_nosuch.s0rtdep` | s0rtdep → s0rtdep | DeployContract(61 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `32.deploy-call.rtunk_burngas.s1rtdep` | s1rtdep → s1rtdep | DeployContract(61 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `35.deploy-call.rtunk_sleep.s2rtdep` | s2rtdep → s2rtdep | DeployContract(64 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `38.deploy-call.rtunk_sandbox.s3rtdep` | s3rtdep → s3rtdep | DeployContract(71 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `30.deploy.rtunk_nosuch.s0rtdep` | s0rtdep → s0rtdep | DeployContract(61 B) | value ×2 |
| `33.deploy.rtunk_burngas.s1rtdep` | s1rtdep → s1rtdep | DeployContract(61 B) | value ×2 |
| `36.deploy.rtunk_sleep.s2rtdep` | s2rtdep → s2rtdep | DeployContract(64 B) | value ×2 |
| `39.deploy.rtunk_sandbox.s3rtdep` | s3rtdep → s3rtdep | DeployContract(71 B) | value ×2 |
| `31.call-deployed.rtunk_nosuch.s0rtdep` | s3rtx → s0rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `34.call-deployed.rtunk_burngas.s1rtdep` | s3rtx → s1rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `37.call-deployed.rtunk_sleep.s2rtdep` | s3rtx → s2rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `40.call-deployed.rtunk_sandbox.s3rtdep` | s3rtx → s3rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `41.deploy-call.rtunk_fwgas_env.s0rtdep` | s0rtdep → s0rtdep | DeployContract(68 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `44.deploy-call.rtunk_gas.s1rtdep` | s1rtdep → s1rtdep | DeployContract(56 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | value ×2 |
| `47.deploy-call.rtbad_storage_write.s2rtdep` | s2rtdep → s2rtdep | DeployContract(67 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `50.deploy-call.rtbad_value_return.s3rtdep` | s3rtdep → s3rtdep | DeployContract(61 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `42.deploy.rtunk_fwgas_env.s0rtdep` | s0rtdep → s0rtdep | DeployContract(68 B) | value ×2 |
| `45.deploy.rtunk_gas.s1rtdep` | s1rtdep → s1rtdep | DeployContract(56 B) | value ×2 |
| `48.deploy.rtbad_storage_write.s2rtdep` | s2rtdep → s2rtdep | DeployContract(67 B) | value ×2 |
| `51.deploy.rtbad_value_return.s3rtdep` | s3rtdep → s3rtdep | DeployContract(61 B) | value ×2 |
| `43.call-deployed.rtunk_fwgas_env.s0rtdep` | s3rtx → s0rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `46.call-deployed.rtunk_gas.s1rtdep` | s3rtx → s1rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | value ×2 |
| `49.call-deployed.rtbad_storage_write.s2rtdep` | s3rtx → s2rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `52.call-deployed.rtbad_value_return.s3rtdep` | s3rtx → s3rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `53.deploy-call.rtbad_input.s0rtdep` | s0rtdep → s0rtdep | DeployContract(58 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `56.deploy-call.rtbad_block_index.s1rtdep` | s1rtdep → s1rtdep | DeployContract(64 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `59.deploy-call.rtbad_panic.s2rtdep` | s2rtdep → s2rtdep | DeployContract(58 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `62.deploy-call.rtbad_promise_create.s3rtdep` | s3rtdep → s3rtdep | DeployContract(74 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `54.deploy.rtbad_input.s0rtdep` | s0rtdep → s0rtdep | DeployContract(58 B) | value ×2 |
| `57.deploy.rtbad_block_index.s1rtdep` | s1rtdep → s1rtdep | DeployContract(64 B) | value ×2 |
| `60.deploy.rtbad_panic.s2rtdep` | s2rtdep → s2rtdep | DeployContract(58 B) | value ×2 |
| `63.deploy.rtbad_promise_create.s3rtdep` | s3rtdep → s3rtdep | DeployContract(74 B) | value ×2 |
| `55.call-deployed.rtbad_input.s0rtdep` | s3rtx → s0rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `58.call-deployed.rtbad_block_index.s1rtdep` | s3rtx → s1rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `61.call-deployed.rtbad_panic.s2rtdep` | s3rtx → s2rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `64.call-deployed.rtbad_promise_create.s3rtdep` | s3rtx → s3rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `65.deploy-call.rtbad_read_register.s0rtdep` | s0rtdep → s0rtdep | DeployContract(68 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `68.deploy-call.rtprep_module.s1rtdep` | s1rtdep → s1rtdep | DeployContract(58 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `71.deploy-call.rtprep_internal.s2rtdep` | s2rtdep → s2rtdep | DeployContract(73 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `74.deploy-call.rtprep_memory.s3rtdep` | s3rtdep → s3rtdep | DeployContract(56 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Memory) ×1, value ×2 |
| `66.deploy.rtbad_read_register.s0rtdep` | s0rtdep → s0rtdep | DeployContract(68 B) | value ×2 |
| `69.deploy.rtprep_module.s1rtdep` | s1rtdep → s1rtdep | DeployContract(58 B) | value ×2 |
| `72.deploy.rtprep_internal.s2rtdep` | s2rtdep → s2rtdep | DeployContract(73 B) | value ×2 |
| `75.deploy.rtprep_memory.s3rtdep` | s3rtdep → s3rtdep | DeployContract(56 B) | value ×2 |
| `67.call-deployed.rtbad_read_register.s0rtdep` | s3rtx → s0rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `70.call-deployed.rtprep_module.s1rtdep` | s3rtx → s1rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `73.call-deployed.rtprep_internal.s2rtdep` | s3rtx → s2rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `76.call-deployed.rtprep_memory.s3rtdep` | s3rtx → s3rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Memory) ×1, value ×2 |
| `77.deploy-call.rtprep_table.s0rtdep` | s0rtdep → s0rtdep | DeployContract(56 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `80.deploy-call.rtprep_global.s1rtdep` | s1rtdep → s1rtdep | DeployContract(56 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `83.deploy-call.rtload.s2rtdep` | s2rtdep → s2rtdep | DeployContract(1011990 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `86.deploy-call.rtload2.s3rtdep` | s3rtdep → s3rtdep | DeployContract(1027734 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `78.deploy.rtprep_table.s0rtdep` | s0rtdep → s0rtdep | DeployContract(56 B) | value ×2 |
| `81.deploy.rtprep_global.s1rtdep` | s1rtdep → s1rtdep | DeployContract(56 B) | value ×2 |
| `84.deploy.rtload.s2rtdep` | s2rtdep → s2rtdep | DeployContract(1011990 B) | value ×2 |
| `87.deploy.rtload2.s3rtdep` | s3rtdep → s3rtdep | DeployContract(1027734 B) | value ×2 |
| `79.call-deployed.rtprep_table.s0rtdep` | s3rtx → s0rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `82.call-deployed.rtprep_global.s1rtdep` | s3rtx → s1rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | PrepareError(Instantiate) ×1, value ×2 |
| `85.call-deployed.rtload.s2rtdep` | s3rtx → s2rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `88.call-deployed.rtload2.s3rtdep` | s3rtx → s3rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `89.deploy-call.rtcombo.s0rtdep` | s0rtdep → s0rtdep | DeployContract(1012018 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `92.deploy-call.rtfitunk.s1rtdep` | s1rtdep → s1rtdep | DeployContract(1004034 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `95.deploy-call.rtfita.s2rtdep` | s2rtdep → s2rtdep | DeployContract(1004134 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | value ×2 |
| `98.deploy-call.rtovrc.s3rtdep` | s3rtdep → s3rtdep | DeployContract(1004162 B), FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `90.deploy.rtcombo.s0rtdep` | s0rtdep → s0rtdep | DeployContract(1012018 B) | value ×2 |
| `93.deploy.rtfitunk.s1rtdep` | s1rtdep → s1rtdep | DeployContract(1004034 B) | value ×2 |
| `96.deploy.rtfita.s2rtdep` | s2rtdep → s2rtdep | DeployContract(1004134 B) | value ×2 |
| `99.deploy.rtovrc.s3rtdep` | s3rtdep → s3rtdep | DeployContract(1004162 B) | value ×2 |
| `91.call-deployed.rtcombo.s0rtdep` | s3rtx → s0rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |
| `94.call-deployed.rtfitunk.s1rtdep` | s3rtx → s1rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LinkError ×1, value ×2 |
| `97.call-deployed.rtfita.s2rtdep` | s3rtx → s2rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | value ×2 |
| `100.call-deployed.rtovrc.s3rtdep` | s3rtx → s3rtdep | FunctionCall(main, 0 B args, 20 Tgas, deposit 1000) | LoadingError ×1, value ×2 |

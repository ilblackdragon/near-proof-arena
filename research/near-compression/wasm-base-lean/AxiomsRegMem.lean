import WasmBase.RegMem
import WasmBase.Main.RegMemLink
/-! Axiom audit for E2E milestone M1-a (`WasmBase/RegMem.lean`, `WasmBase/Main/RegMemLink.lean`).
Run `lake env lean AxiomsRegMem.lean`: every line must list only `propext`, `Classical.choice`,
`Quot.sound` (or no axioms). -/

-- the AIR (`WasmBase/RegMem.lean`)
#print axioms WasmBase.ifreg_air_len
#print axioms WasmBase.ifreg_air_22
#print axioms WasmBase.ifreg_air_27
#print axioms WasmBase.ifreg_air_base
#print axioms WasmBase.busRegRd_fresh
#print axioms WasmBase.boundary_no_211
#print axioms WasmBase.Chips.HostR.constraints_prefix
#print axioms WasmBase.Chips.RegW.constraints_prefix
#print axioms WasmBase.Chips.hidReadRegister_sig

-- the link (`WasmBase/Main/RegMemLink.lean`)
#print axioms WasmBase.writeBytes_eq
#print axioms WasmBase.writeBytes_facts
#print axioms WasmBase.read_register_h
#print axioms WasmBase.regGetH_ok
#print axioms WasmBase.read_register_run
#print axioms WasmBase.read_register_state
#print axioms WasmBase.heap_read_register
#print axioms WasmBase.regw_write_msgs
#print axioms WasmBase.regw_time_lt
#print axioms WasmBase.read_register_rows_heap
#print axioms WasmBase.regw_pub_result

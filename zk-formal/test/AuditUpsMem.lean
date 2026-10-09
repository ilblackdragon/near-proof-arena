import ZkFormal.NearV3.Render.Ups.GMem
import ZkFormal.NearV3.Render.Ups.MemSemantic

/-! Guards for signed carry arithmetic and its row encoding. -/

/-- info: 'ZkFormal.NearV3.Render.UpsGen.inside_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.inside_carry

/-- info: 'ZkFormal.NearV3.Render.UpsGen.outside_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.outside_carry

/-- info: 'ZkFormal.NearV3.Render.UpsGen.outside_last_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.outside_last_high

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_tE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_tE

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_cbE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_cbE

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_ccE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_ccE

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_coE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_coE

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_inside

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_outside

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_parent

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_input

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_extra' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_extra

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_initial

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_send_gate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_send_gate

/-- info: 'ZkFormal.NearV3.Render.UpsGen.mem_recv_gate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.mem_recv_gate

/-- info: 'ZkFormal.NearV3.Render.UpsGen.cMemCurrent_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.cMemCurrent_ok

/-- info: 'ZkFormal.NearV3.Render.UpsGen.cMemCarry_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.cMemCarry_ok

/-- info: 'ZkFormal.NearV3.Render.UpsGen.cMemLengths_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.cMemLengths_ok

/-- info: 'ZkFormal.NearV3.Render.UpsGen.cMem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.cMem_ok

/-- info: 'ZkFormal.NearV3.Render.UpsGen.coV_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.coV_bounds

/-- info: 'ZkFormal.NearV3.Render.UpsGen.co2V_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.co2V_bounds

/-- info: 'ZkFormal.NearV3.Render.UpsGen.cbV_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.cbV_bounds

/-- info: 'ZkFormal.NearV3.Render.UpsGen.NodeEncoding.memory_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.NodeEncoding.memory_result

/-- info: 'ZkFormal.NearV3.Render.UpsGen.memOk_of_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Render.UpsGen.memOk_of_semantics

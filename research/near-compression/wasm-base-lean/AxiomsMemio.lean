import WasmBase.Main.SoundHost
import WasmBase.Main.MemIOBus
import WasmBase.Main.RegSend
import WasmBase.Main.RegWalk
import WasmBase.MemIO
/-! Axiom audit for the `pq-host-memio` lane's headline theorems. -/

open WasmBase

-- the MEMIO view extension (`WasmBase/MemIO.lean`)
#print axioms WasmBase.heap_retime
#print axioms WasmBase.heap_retime_readByte
#print axioms WasmBase.BufOK.addr_lt
#print axioms WasmBase.ch_pair_vacuous

-- the HOSTB partition of the space-3 block (`WasmBase/Main/MemIOBus.lean`)
#print axioms WasmBase.hostb_inters_stk
#print axioms WasmBase.hostb_rowAct_iff
#print axioms WasmBase.hostb_inactive_nil
#print axioms WasmBase.hostb_part_ch_send
#print axioms WasmBase.hostb_part_ch_recv
#print axioms WasmBase.hostb_partition
#print axioms WasmBase.hostb_partition_prod
#print axioms WasmBase.hostb_partition_cons
#print axioms WasmBase.flatMap_prodCH_perm
#print axioms WasmBase.flatMap_consCH_perm
#print axioms WasmBase.host_hch
#print axioms WasmBase.host_buses

-- the HOSTB count/bit facts (`WasmBase/Main/HostChipBits.lean`)
#print axioms WasmBase.hostb_memCnt_bit
#print axioms WasmBase.hostb_touches_ch
#print axioms WasmBase.hostb_avoids_state

-- the REG group walk and its HOSTB interaction
#print axioms WasmBase.regLenAgree_group_of_holds
#print axioms WasmBase.reg_group_walk
#print axioms WasmBase.regLenAgree_lone_length
#print axioms WasmBase.reg_gap_wraparound
#print axioms WasmBase.reg_gap_lt
#print axioms WasmBase.reg_pos_lt_len
#print axioms WasmBase.hostb_r16_cases

-- the headline join statement
#print axioms WasmBase.wasm_base_exec_host_holds

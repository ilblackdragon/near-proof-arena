import StateM5a.FinalOrder
import StateM5a.IntakeKeys
import StateM5a.KeyOrder
import StateM5a.KeyDigest
import StateM5a.KcChain
import StateM5a.KeyLookups
import StateM5a.Tape
import StateM5a.DepthBound
import StateM5a.KeyDecode
import StateM5a.Steps
import StateM5a.RowBrF
import StateM5a.RowHloc
import StateM5a.RowFacts
import StateM5a.VerAssembly
import StateM5a.RowSnAll
import StateM5a.StepsT2
import StateM5a.Walk
import StateM5a.SerInj
import StateM5a.Refine
import StateM5a.FieldRows
import StateM5a.FieldRows2
import StateM5a.Layout
import StateM5a.Order
import StateM5a.Merkle
import StateM5a.KeyField
import StateM5a.Store
import StateM5a.FieldVer
import StateM5a.StepsBV
import StateM5a.Bus
import StateM5a.Traffic
import StateM5a.BusWalk
import StateM5a.FieldWalk
import StateM5a.Keep
import StateM5a.WsCost
import StateM5a.FieldWalk2
import StateM5a.FieldWsb
import StateM5a.DecodeBus
import StateM5a.DecodeWalk
import StateM5a.DecodeM5a
import StateM5a.DecodeShape
import StateM5a.BusSplit
import StateM5a.BusSplit2
import StateM5a.WsBus
import StateM5a.Sha512If
import StateM5a.StateView
import StateM5a.StateViewParams
import StateM5a.WsLen
import StateM5a.WsRaw
import StateM5a.WsSeg
import StateM5a.WsEntries
import StateM5a.ChipStub
import StateM5a.SnResp
import StateM5a.WalkEnd

/-! Axiom audit of the M5a lemmas (`lake build StateM5a.Audit` prints them): every theorem must
depend on `propext`, `Classical.choice`, `Quot.sound` at most. -/

#print axioms StateM5a.Steps.br_findRef
#print axioms StateM5a.Steps.br_upsert_descend
#print axioms StateM5a.Steps.br_upsert_new
#print axioms StateM5a.Steps.br_del_keep
#print axioms StateM5a.Steps.br_del_one
#print axioms StateM5a.Steps.leaf_findRef
#print axioms StateM5a.Steps.leaf_upsert
#print axioms StateM5a.Steps.leaf_del
#print axioms StateM5a.Steps.leafMem_eq
#print axioms StateM5a.Steps.ext_findRef
#print axioms StateM5a.Steps.ext_upsert
#print axioms StateM5a.Steps.ext_del_leaf
#print axioms StateM5a.Steps.applyChange_upsert
#print axioms StateM5a.Steps.applyChange_del
#print axioms StateM5a.Steps.ne_of_mismatch
#print axioms StateM5a.Steps.not_isPrefix_of_mismatch
#print axioms StateM5a.Steps.br_findValue
#print axioms StateM5a.Steps.br_del_absent
#print axioms StateM5a.Steps.br_del_same
#print axioms StateM5a.Steps.leaf_findRef_absent
#print axioms StateM5a.Steps.leaf_del_absent
#print axioms StateM5a.Steps.ext_findRef_absent
#print axioms StateM5a.Steps.ext_del_absent
#print axioms StateM5a.Steps.ext_del_same
#print axioms StateM5a.Steps.ext_del_branch
#print axioms StateM5a.Steps.commonPrefix_split
#print axioms StateM5a.Steps.wrapExt_cons
#print axioms StateM5a.Steps.leaf_split
#print axioms StateM5a.Steps.ext_split
#print axioms StateM5a.Steps.kids2_at
#print axioms StateM5a.Layout.kidsBitmap_eq
#print axioms StateM5a.Layout.hashes_eq
#print axioms StateM5a.Layout.block_at
#print axioms StateM5a.Layout.hexPrefix_eq
#print axioms StateM5a.Layout.hpAt_chunk
#print axioms StateM5a.Order.nibLt_bytesLt
#print axioms StateM5a.Merkle.write_access_sound
#print axioms StateM5a.KeyField.key_row_nibbles
#print axioms StateM5a.Walk.fchain_sound
#print axioms StateM5a.Walk.fchain_witness
#print axioms StateM5a.Walk.uchain_sound
#print axioms StateM5a.Walk.uchain_witness
#print axioms StateM5a.Walk.dchain_sound
#print axioms StateM5a.Walk.change_upsert
#print axioms StateM5a.Walk.change_del
#print axioms StateM5a.Walk.refinedBy_of_hash
#print axioms StateM5a.Walk.kids_at_refinedBy
#print axioms StateM5a.FieldRows.kcmp_fin_lt
#print axioms StateM5a.FieldRows.sn_mismatch_ne
#print axioms StateM5a.FieldRows.br_keep
#print axioms StateM5a.FieldRows.memChain_sound
#print axioms StateM5a.FieldRows.onehot_of_sum
#print axioms StateM5a.FieldRows.limb_eq
-- batched FINAL (M5a-2): the version store
#print axioms StateM5a.Store.exp_functional
#print axioms StateM5a.Store.rv_refinedBy
#print axioms StateM5a.Store.rv_collapse
#print axioms StateM5a.Store.change_step
#print axioms StateM5a.Store.upsert_step
#print axioms StateM5a.Store.find_step
#print axioms StateM5a.Store.batched_upserts
#print axioms StateM5a.FieldVer.br_vm_gsha
#print axioms StateM5a.FieldVer.br_vmn_gnew
#print axioms StateM5a.FieldVer.br_gsha_dig
#print axioms StateM5a.FieldVer.br_gsha_isn
#print axioms StateM5a.FieldVer.br_vid
#print axioms StateM5a.FieldVer.sn_vm_gsha
#print axioms StateM5a.FieldVer.sn_vmn_gnew
#print axioms StateM5a.FieldVer.sn_gsha_dig
#print axioms StateM5a.FieldVer.sn_vid
#print axioms StateM5a.FieldVer.sn_cont
#print axioms StateM5a.StepsBV.br_upsert_value
#print axioms StateM5a.StepsBV.br_del_value_keep
#print axioms StateM5a.StepsBV.br_del_value_absent
#print axioms StateM5a.SerInj.leN_inj
#print axioms StateM5a.SerInj.hexPrefix_inj
#print axioms StateM5a.SerInj.packNibbles_inj
#print axioms StateM5a.SerInj.kids_inj
#print axioms StateM5a.SerInj.slot_of_valueRef
#print axioms StateM5a.SerInj.nodeSerInj
#print axioms StateM5a.SerInj.refinedBy_of_hash'
#print axioms StateM5a.Refine.del_refinedBy
#print axioms StateM5a.Refine.kids_delAt_refinedBy
#print axioms StateM5a.Refine.squashBranch_refinedBy
#print axioms StateM5a.Refine.extendChild_refinedBy
#print axioms StateM5a.Refine.del_some
#print axioms StateM5a.Refine.dchain_witness
#print axioms StateM5a.Refine.change_del_witness
#print axioms StateM5a.Refine.findRef_refinedBy
#print axioms StateM5a.Refine.rows_refinedBy
#print axioms StateM5a.Refine.find_spec
#print axioms StateM5a.Refine.upsert_spec
#print axioms StateM5a.Refine.del_spec
#print axioms StateM5a.FieldRows2.prefix_flags
#print axioms StateM5a.FieldRows2.half_eq
#print axioms StateM5a.FieldRows2.sn_flags
#print axioms StateM5a.FieldRows2.sn_odd
#print axioms StateM5a.FieldRows2.sn_ha
#print axioms StateM5a.FieldRows2.sn_hplen
#print axioms StateM5a.FieldRows2.keyOf_getD
#print axioms StateM5a.FieldRows2.sn_hp
#print axioms StateM5a.FieldRows2.sn_hexPrefix
#print axioms StateM5a.FieldRows2.sum_one
#print axioms StateM5a.FieldRows2.sum_single
#print axioms StateM5a.FieldRows2.br_sel
#print axioms StateM5a.Store.del_step
#print axioms StateM5a.Store.batched_changes
#print axioms StateM5a.Bus.count_busList
#print axioms StateM5a.Bus.holds_perm
#print axioms StateM5a.Bus.perm_of_map_inj
#print axioms StateM5a.Bus.perm_decode
#print axioms StateM5a.Traffic.walk_unique
#print axioms StateM5a.Traffic.child_of
#print axioms StateM5a.Traffic.walk_rows
#print axioms StateM5a.Traffic.walk_sem
#print axioms StateM5a.Traffic.tch_chain
#print axioms StateM5a.Traffic.ver_recv
#print axioms StateM5a.Traffic.reqresp
#print axioms StateM5a.BusWalk.cl_collapse
#print axioms StateM5a.BusWalk.in_view
#print axioms StateM5a.BusWalk.out_view
#print axioms StateM5a.BusWalk.hashed_agree
#print axioms StateM5a.BusWalk.ver_store
#print axioms StateM5a.BusWalk.step_leafRep
#print axioms StateM5a.BusWalk.step_brDesc
#print axioms StateM5a.BusWalk.step_extDesc
#print axioms StateM5a.BusWalk.localOK_upsert
#print axioms StateM5a.BusWalk.localOK_delete
#print axioms StateM5a.BusWalk.localOK_find
#print axioms StateM5a.BusWalk.cl_wf
#print axioms StateM5a.BusWalk.in_view_wf
#print axioms StateM5a.BusWalk.rv_wf
#print axioms StateM5a.BusWalk.kcl_present_length
#print axioms StateM5a.BusWalk.same_res
#print axioms StateM5a.BusWalk.step_leafDel
#print axioms StateM5a.BusWalk.step_leafAbs
#print axioms StateM5a.BusWalk.step_extAbs
#print axioms StateM5a.BusWalk.step_extSame
#print axioms StateM5a.BusWalk.step_extLeaf
#print axioms StateM5a.BusWalk.step_extBranch
#print axioms StateM5a.BusWalk.step_brAbs
#print axioms StateM5a.BusWalk.step_brSame
#print axioms StateM5a.BusWalk.step_brKeep
#print axioms StateM5a.BusWalk.step_leafHit
#print axioms StateM5a.BusWalk.step_leafMiss
#print axioms StateM5a.BusWalk.step_extMiss
#print axioms StateM5a.BusWalk.step_extFind
#print axioms StateM5a.BusWalk.step_brFind
#print axioms StateM5a.BusWalk.step_brEmpty
#print axioms StateM5a.BusWalk.step_brVal
#print axioms StateM5a.BusWalk.step_brValAbs
#print axioms StateM5a.BusWalk.step_brDelVal
#print axioms StateM5a.BusWalk.step_brUpVal
#print axioms StateM5a.BusWalk.step_brNew
#print axioms StateM5a.BusWalk.chain_changes
#print axioms StateM5a.BusWalk.stepRows_of_sem
#print axioms StateM5a.BusWalk.bus_batched_changes
-- M5a-3: branch-value chain constructors (soundness through the extended matches)
-- M5a-3: the squash after a value delete (spec steps)
#print axioms StateM5a.StepsBV.br_del_value_one
#print axioms StateM5a.StepsBV.br_del_value_one_leaf
#print axioms StateM5a.StepsBV.br_del_value_one_ext
#print axioms StateM5a.StepsBV.br_del_value_one_branch
#print axioms StateM5a.StepsBV.br_del_value_one_hash
#print axioms StateM5a.StepsBV.br_del_value_none
-- M5a-3: `KeepsFW` weakened and proved; batched FINAL without it
#print axioms StateM5a.Keep.rp_mem
#print axioms StateM5a.Keep.rp_memD
#print axioms StateM5a.Keep.splitLeaf_rp
#print axioms StateM5a.Keep.splitExt_rp
#print axioms StateM5a.Keep.upsert_rp
#print axioms StateM5a.Keep.kids_upsert_rp
#print axioms StateM5a.Keep.extendChild_rp
#print axioms StateM5a.Keep.present_rp
#print axioms StateM5a.Keep.squashBranch_rp
#print axioms StateM5a.Keep.del_rp
#print axioms StateM5a.Keep.kids_delAt_rp
#print axioms StateM5a.Keep.slotOk_of_refines
#print axioms StateM5a.Keep.rp_wf
#print axioms StateM5a.Keep.krp_wf
#print axioms StateM5a.Keep.rp_of_refinedBy
#print axioms StateM5a.Keep.krp_of_refinedBy
#print axioms StateM5a.Keep.upsert_wf_of_rows
#print axioms StateM5a.Keep.del_wf_of_rows
#print axioms StateM5a.Keep.applyChange_wf_of_rows
#print axioms StateM5a.Store.not_keepsFW
#print axioms StateM5a.Store.full_rp
#print axioms StateM5a.Store.rp_full
#print axioms StateM5a.Store.full_upsert
#print axioms StateM5a.Store.full_del
#print axioms StateM5a.Store.full_applyChange
#print axioms StateM5a.Store.keepsFWRows
#print axioms StateM5a.Store.ChangeRowsW.rows
#print axioms StateM5a.Store.change_keep
#print axioms StateM5a.Store.batched_changes'
#print axioms StateM5a.Merkle.up_take
#print axioms StateM5a.Merkle.up_drop
#print axioms StateM5a.Merkle.root_succ_split
#print axioms StateM5a.Merkle.Upd.apply_length
#print axioms StateM5a.Merkle.batch_update_sound
#print axioms StateM5a.WsCost.chain_sound
#print axioms StateM5a.WsCost.chain_strict
#print axioms StateM5a.WsCost.chain_sound_any
#print axioms StateM5a.WsCost.leafLimb_inj
#print axioms StateM5a.WsCost.wsa_gap
#print axioms StateM5a.WsCost.wsp_keep
#print axioms StateM5a.WsCost.wsp_child
#print axioms StateM5a.WsCost.wsp_off
#print axioms StateM5a.WsCost.wsl_kd
#print axioms StateM5a.FieldWalk.br_gdn_gold
#print axioms StateM5a.FieldWalk.sn_bool
#print axioms StateM5a.FieldWalk2.sn_gdn_ops
#print axioms StateM5a.FieldWalk2.sn_gdn_isE
#print axioms StateM5a.FieldWalk2.sn_isE_a0
#print axioms StateM5a.FieldWalk2.sn_gdn_gwalk
#print axioms StateM5a.FieldWalk2.sn_gdn_walk
#print axioms StateM5a.FieldWalk2.sn_gdn_klen
#print axioms StateM5a.FieldWsb.wsb_index
#print axioms StateM5a.FieldWsb.wsb_row_inj
#print axioms StateM5a.DecodeBus.rowBusList_one
#print axioms StateM5a.DecodeBus.tableBusList_one
#print axioms StateM5a.DecodeBus.rowBusList_two
#print axioms StateM5a.DecodeBus.busList_extend
#print axioms StateM5a.DecodeWalk.rowsL_din
#print axioms StateM5a.DecodeWalk.rowsL_dout
#print axioms StateM5a.DecodeWalk.rowsL_uout
#print axioms StateM5a.DecodeWalk.rowsL_uin
#print axioms StateM5a.DecodeWalk.rootsOf_dn
#print axioms StateM5a.DecodeWalk.rootsOf_up
#print axioms StateM5a.DecodeM5a.busList_m5a
#print axioms StateM5a.DecodeM5a.br_gdn_g
#print axioms StateM5a.DecodeM5a.sn_gdn_g
#print axioms StateM5a.DecodeM5a.walk_traffic
#print axioms StateM5a.DecodeShape.walk_rootUniq
#print axioms StateM5a.DecodeShape.walk_deeper
#print axioms StateM5a.DecodeShape.walk_shape
#print axioms StateM5a.DecodeShape.air_batched_changes
#print axioms StateM5a.DecodeShape.air_batched_changesS
#print axioms StateM5a.WsBus.wm_orphan
#print axioms StateM5a.WsBus.wm_chain
#print axioms StateM5a.WsBus.rch_tops
#print axioms StateM5a.WsBus.rch_link
#print axioms StateM5a.WsBus.pt_rows_le_one
#print axioms StateM5a.WsBus.wsl_unique
#print axioms StateM5a.WsBus.seg_update
#print axioms StateM5a.WsBus.seg_root
#print axioms StateM5a.WsBus.seg_root_leaves
#print axioms StateM5a.Sha512If.comp_sound
#print axioms StateM5a.Sha512If.comp_iv
#print axioms StateM5a.Sha512If.comp_node
#print axioms StateM5a.Sha512If.wsp_hashes
#print axioms StateM5a.Sha512If.enc_inj
#print axioms StateM5a.StateView.ser_inj
#print axioms StateM5a.StateView.merkle_binding
#print axioms StateM5a.StateView.trie_binding
#print axioms StateM5a.StateView.wsRoot_binding
#print axioms StateM5a.StateView.stD_binding
#print axioms StateM5a.StateView.stD_binding_bad
#print axioms StateM5a.StateView.viewImpl_hst
#print axioms StateM5a.StateView.viewImpl_binding_st
#print axioms StateM5a.BusWalk.matRel_oLM
#print axioms StateM5a.BusWalk.sibRel_oLS
#print axioms StateM5a.BusWalk.sxRel_oEM
#print axioms StateM5a.BusWalk.epRel_oEP
#print axioms StateM5a.BusWalk.splitRel_oSL
#print axioms StateM5a.BusWalk.splitAns_of_spr
#print axioms StateM5a.BusWalk.spr_reqresp
#print axioms StateM5a.BusWalk.mat_reqresp
#print axioms StateM5a.BusWalk.sib_reqresp
#print axioms StateM5a.BusWalk.sx_reqresp
#print axioms StateM5a.BusWalk.step_leafSplit
#print axioms StateM5a.BusWalk.localOK_leafSplit
#print axioms StateM5a.BusWalk.step_brLeaf
#print axioms StateM5a.BusWalk.localOK_brLeaf
#print axioms StateM5a.BusWalk.step_brOne
#print axioms StateM5a.BusWalk.localOK_brOne
#print axioms StateM5a.BusWalk.step_extSplit
#print axioms StateM5a.BusWalk.localOK_extSplit
#print axioms StateM5a.BusWalk.step_brDescS
#print axioms StateM5a.BusWalk.step_extDescS
#print axioms StateM5a.BusWalk.localOK_S_of_leaf
#print axioms StateM5a.BusWalk.localOK_S_of_mode
#print axioms StateM5a.BusWalk.bus_batched_changesS
-- M5a-5: one upsert semantics (UChain.extSplit); SemUS / SemS are aliases of SemU / Sem
#print axioms StateM5a.Steps.ext_split'
#print axioms StateM5a.BusWalk.semUS_iff_semU
#print axioms StateM5a.BusWalk.semUS_upsert
#print axioms StateM5a.BusWalk.semS_eq_sem
#print axioms StateM5a.BusWalk.semS_iff_sem
#print axioms StateM5a.BusWalk.localOK_semS_iff
#print axioms StateM5a.BusWalk.localOK_extSplitS
#print axioms StateM5a.BusWalk.stepRowsS_of_stepRows
#print axioms StateM5a.BusWalk.stepRows_of_semS
#print axioms StateM5a.RowBr.br_flags
#print axioms StateM5a.RowBr.br_some_op
#print axioms StateM5a.RowBrF.localOK_oFD
#print axioms StateM5a.RowBrF.localOK_oFA
#print axioms StateM5a.RowBrF.localOK_oFV
#print axioms StateM5a.RowBrD.localOK_oDA
#print axioms StateM5a.RowBrD.localOK_oDS
#print axioms StateM5a.RowBrD.localOK_oDZ
#print axioms StateM5a.RowBrU.localOK_oUD
#print axioms StateM5a.RowBrK.localOK_oDH
#print axioms StateM5a.RowBrK.localOK_oDN
#print axioms StateM5a.RowBrN.br_mem_desc
#print axioms StateM5a.RowHloc.hloc_br
#print axioms StateM5a.RowHloc.hloc_cDc
#print axioms StateM5a.RowHloc.air_batched_changes_cDc
#print axioms StateM5a.StateView.shape_binding
#print axioms StateM5a.StateView.circuit_binding
#print axioms StateM5a.StateView.ser_ne_raw
#print axioms StateM5a.StateViewParams.tEnc_pf
#print axioms StateM5a.StateViewParams.vnat_pf
#print axioms StateM5a.StateViewParams.leafBlockN_inj
#print axioms StateM5a.StateViewParams.strip_ovl_inj
#print axioms StateM5a.StateViewParams.kv_ext
#print axioms StateM5a.StateViewParams.encRestB_inj
#print axioms StateM5a.StateViewParams.rawB_inj
#print axioms StateM5a.StateViewParams.rest_shapeB
#print axioms StateM5a.StateViewParams.proj_injB
#print axioms StateM5a.StateViewParams.stD_binding_B
#print axioms StateM5a.StateViewParams.viewImpl_hst_B
#print axioms StateM5a.WsLen.wsb_height
#print axioms StateM5a.WsLen.wsb_pos
#print axioms StateM5a.WsLen.wsb_real_iff
#print axioms StateM5a.WsLen.wsb_wsLen_le
#print axioms StateM5a.WsLen.wsb_leaves
#print axioms StateM5a.WsLen.wsl_ix
#print axioms StateM5a.WsLen.wsl_lt_wsLen
#print axioms StateM5a.WsRaw.descent
#print axioms StateM5a.WsRaw.lvl_lt
#print axioms StateM5a.WsRaw.pos_bound
#print axioms StateM5a.WsRaw.wsl_i_lt
#print axioms StateM5a.WsRaw.seg_lt
#print axioms StateM5a.WsRaw.pt_eq
#print axioms StateM5a.WsRaw.rch_eq
#print axioms StateM5a.WsSeg.root_inj
#print axioms StateM5a.WsSeg.seg_chain
#print axioms StateM5a.WsSeg.tops_lt
#print axioms StateM5a.WsSeg.wsl_top
#print axioms StateM5a.WsSeg.ws_compose
#print axioms StateM5a.WsSeg.wsAt_untouched
#print axioms StateM5a.WsSeg.wsAt_last
#print axioms StateM5a.WsSeg.ws_final
#print axioms StateM5a.WsDecode.comp_mem
#print axioms StateM5a.WsDecode.busList_ws
#print axioms StateM5a.WsDecode.rng_v
#print axioms StateM5a.WsDecode.rowDig_of
#print axioms StateM5a.WsDecode2.pt_traffic
#print axioms StateM5a.WsDecode2.rch_traffic
#print axioms StateM5a.WsDecode2.wm_traffic
#print axioms StateM5a.WsDecode3.rng_send_lt
#print axioms StateM5a.WsDecode3.wsp_rowF
#print axioms StateM5a.WsDecode3.wsp_ok
#print axioms StateM5a.WsDecode3.x_lt64
#print axioms StateM5a.WsDecode3.wsa_gap_rec
#print axioms StateM5a.WsDecode3.wsl_ok
#print axioms StateM5a.WsDecode3.wsl_leaf
#print axioms StateM5a.WsDecode3.ws_decoded
#print axioms StateM5a.WsDecode3.ws_decoded_final
#print axioms StateM5a.KeyDecode.key_inv
#print axioms StateM5a.KeyDecode.keyOf_eq_nibbles
#print axioms StateM5a.KeyDecode.key_row_get
#print axioms StateM5a.KeyDecode.key_row_len
#print axioms StateM5a.KeyDecode.nib_recv
#print axioms StateM5a.KeyDecode.klen_recv
#print axioms StateM5a.KeyDecode.nib_of_rcv
#print axioms StateM5a.KeyDecode.klen_of_rcv
#print axioms StateM5a.DepthBound.br_depth
#print axioms StateM5a.DepthBound.sn_depth
#print axioms StateM5a.DepthBound.walk_deeper'
#print axioms StateM5a.DepthBound.walk_shape'
#print axioms StateM5a.DepthBound.air_batched_changes'
#print axioms StateM5a.DepthBound.air_batched_changesS'
#print axioms StateM5a.Tape.limbBytes_pairs
#print axioms StateM5a.Tape.stdDec_std
#print axioms StateM5a.Tape.busList_tch
#print axioms StateM5a.Tape.wsb_j
#print axioms StateM5a.Tape.tch_perm
#print axioms StateM5a.Tape.root_of_row
#print axioms StateM5a.Tape.air_final
#print axioms StateM5a.KeyLookups.br_nib
#print axioms StateM5a.KeyLookups.sn_nib
#print axioms StateM5a.KeyLookups.sn_nib2
#print axioms StateM5a.KeyLookups.sn_klen_leaf
#print axioms StateM5a.KeyLookups.snc_nibA
#print axioms StateM5a.KeyLookups.kcmp_nib_xb
#print axioms StateM5a.WsTree.tree_msg
#print axioms StateM5a.WsTree.tree_top
#print axioms StateM5a.WsTree.tree_tops_le
#print axioms StateM5a.WsTree.tree_root
#print axioms StateM5a.WsDecode4.tree_traffic
#print axioms StateM5a.WsDecode4.wsn_ok
#print axioms StateM5a.WsDecode4.tree_premises
#print axioms StateM5a.WsDecode4.wsn_roots
#print axioms StateM5a.WsDecode4.ws_decoded_final2
#print axioms StateM5a.WsKey.key_inv
#print axioms StateM5a.WsKey.hkd_of
#print axioms StateM5a.WsKey.key_of_block
#print axioms StateM5a.WsKey.wsl_keys
#print axioms StateM5a.WsKey.ws_decoded_final3
#print axioms StateM5a.WsKey.open_eq_close
#print axioms StateM5a.KcChain.snc_c_range
#print axioms StateM5a.KcChain.snc_tot
#print axioms StateM5a.KcChain.sncDeeper
#print axioms StateM5a.KcChain.air_final'
#print axioms StateM5a.KeyDigest.snc_rid
#print axioms StateM5a.KeyDigest.key_byte
#print axioms StateM5a.KeyDigest.key_digest
#print axioms StateM5a.KeyDigest.kdig_recv
#print axioms StateM5a.KeyDigest.wsb_kd
#print axioms StateM5a.WsLeafF.block_fields
#print axioms StateM5a.WsLeafF.content_eq
#print axioms StateM5a.WsLeafF.wsb_leaf
#print axioms StateM5a.WsLeafF.wsl_okE
#print axioms StateM5a.WsLeafF.wsb_ph0_cur
#print axioms StateM5a.WsEntries.ws_entries
#print axioms StateM5a.KeyOrder.kcmp_back
#print axioms StateM5a.KeyOrder.ord_recv
#print axioms StateM5a.KeyOrder.wsbKdRange
#print axioms StateM5a.IntakeKeys.wsb_sorted
#print axioms StateM5a.IntakeKeys.wsb_kd_inj
#print axioms StateM5a.IntakeKeys.intakeKeysDistinct
#print axioms StateM5a.FinalOrder.sortKV_of_perm
#print axioms StateM5a.FinalOrder.final_key
#print axioms StateM5a.FinalOrder.wr_sorted
#print axioms StateM5a.FinalOrder.fc_sorted
#print axioms StateM5a.FinalOrder.air_final_sorted
#print axioms StateM5a.RowDec.cDc_std
#print axioms StateM5a.RowFacts.br_mono
#print axioms StateM5a.RowFacts.brRowFacts_of
#print axioms StateM5a.RowFacts.hloc_air
#print axioms StateM5a.RowFacts.air_final_sorted_cDc
#print axioms StateM5a.RowBrV2.localOK_oUV
#print axioms StateM5a.RowBrV2.localOK_oDV
#print axioms StateM5a.RowBrL.localOK_oDL
#print axioms StateM5a.RowBrV.br_nvlen
#print axioms StateM5a.RowBrUN.localOK_oUN
#print axioms StateM5a.RowBrD1.localOK_oD1
#print axioms StateM5a.RowHloc.walkOps_covered
#print axioms StateM5a.RowFacts.keyOf_bounds
#print axioms StateM5a.VerDec.dec_of_parts
#print axioms StateM5a.VerDec.brOld_dec
#print axioms StateM5a.VerRead.br_rd_part
#print axioms StateM5a.VerStore.br_oldOK
#print axioms StateM5a.VerStore.br_newOK
#print axioms StateM5a.VerStore.brVers_nodup
#print axioms StateM5a.VerAssembly.air_final_sorted_ver
#print axioms StateM5a.VerRead.br_ver_head
#print axioms StateM5a.ChipStub.holds_of_holdsX
#print axioms StateM5a.ChipStub.m5a_ifOK
#print axioms StateM5a.ChipStub.tape_ifOK
#print axioms StateM5a.ChipStub.precheck_holds
#print axioms StateM5a.ChipStub.precheck_holds_tape
#print axioms StateM5a.ChipStub.stub_bus_premise
#print axioms StateM5a.ChipStub.stub_sendsOn_premise
#print axioms StateM5a.BrSer.ser_ok
#print axioms StateM5a.BrSer.grec_hashed
#print axioms StateM5a.BrDigest.br_byte
#print axioms StateM5a.BrDigest.node_hashed
#print axioms StateM5a.BrDigest.brHashed
#print axioms StateM5a.BrDigest.br_old_node
#print axioms StateM5a.BrDigest.br_new_node
#print axioms StateM5a.RowHloc.BrRangesW.full
#print axioms StateM5a.BrRange.br_NM_lt
#print axioms StateM5a.BrRange.br_M_lt
#print axioms StateM5a.BrRange.br_nmom_lt
#print axioms StateM5a.BrRange.brRangesW_of
#print axioms StateM5a.BrSib.br_row_unique
#print axioms StateM5a.BrSib.br_sib
#print axioms StateM5a.BrMat.br_mat
#print axioms StateM5a.RowSn.sn_flags'
#print axioms StateM5a.RowSnMsg.sn_uout
#print axioms StateM5a.RowSnF.sn_key_prefix
#print axioms StateM5a.RowSnF.localOK_oLF
#print axioms StateM5a.RowSnF.localOK_oEF
#print axioms StateM5a.RowSnM.sn_jm
#print axioms StateM5a.RowSnM.sn_mismatch
#print axioms StateM5a.RowSnM.localOK_oLA
#print axioms StateM5a.RowSnM.localOK_oEA
#print axioms StateM5a.RowSnM.localOK_oLZ
#print axioms StateM5a.RowSnM.localOK_oEZ
#print axioms StateM5a.RowSnD.localOK_oLD
#print axioms StateM5a.RowSnAll.hloc_sn
#print axioms StateM5a.RowSnN.sn_mem_eu
#print axioms StateM5a.RowSnN.sn_leaf_nmem
#print axioms StateM5a.RowSnN.localOK_oLR
#print axioms StateM5a.RowSnN.localOK_oEU
#print axioms StateM5a.RowSnE.sn_mem_eb
#print axioms StateM5a.RowSnE.localOK_oES
#print axioms StateM5a.RowSnE.localOK_oEB
#print axioms StateM5a.RowSnE.localOK_oED
#print axioms StateM5a.RowSnAll2.hloc_sn2
#print axioms StateM5a.SnDepthAll.sn_depth_all
#print axioms StateM5a.SnAssembly.sn_unom_lt
#print axioms StateM5a.SnAssembly.hloc_sn3
#print axioms StateM5a.SnAssembly.air_final_sorted_sn
#print axioms StateM5a.SnResp.resp_key
#print axioms StateM5a.SnResp.snSibOK_of
#print axioms StateM5a.SnResp.snMatOK_of
#print axioms StateM5a.SnResp.air_final_sorted_sn2
#print axioms StateM5a.WalkEnd.terminal_deepest
#print axioms StateM5a.WalkEnd.sn_term_unique
#print axioms StateM5a.WalkEnd.br_above_term
#print axioms StateM5a.WalkEnd.oslApart

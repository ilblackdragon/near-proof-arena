import StateM5a.Steps
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
import StateM5a.Keep

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
-- M5a-3: branch-value chain constructors (soundness through the extended matches)
#print axioms StateM5a.Walk.uchain_sound
#print axioms StateM5a.Walk.dchain_sound
#print axioms StateM5a.Walk.uchain_witness
#print axioms StateM5a.Refine.dchain_witness
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

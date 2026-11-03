import StateM5a.Steps
import StateM5a.StepsT2
import StateM5a.Walk
import StateM5a.FieldRows
import StateM5a.Layout
import StateM5a.Order
import StateM5a.Merkle
import StateM5a.KeyField
import StateM5a.Store
import StateM5a.FieldVer
import StateM5a.StepsBV

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

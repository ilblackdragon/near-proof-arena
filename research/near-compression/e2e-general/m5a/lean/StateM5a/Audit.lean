import StateM5a.Steps
import StateM5a.StepsT2
import StateM5a.Layout
import StateM5a.Order
import StateM5a.Merkle
import StateM5a.KeyField

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

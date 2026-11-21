import M5T1.RxRow
import M5T1.T1
import M5T1.Obl
import M5T1.Bus
import M5T1.MsgSpec
import M5T1.MsgRow
import M5T1.MsgRowDg
import M5T1.MsgRowId
import M5T1.SegRt

/-! The axioms of every lane F headline theorem (standard axioms only). -/

#print axioms M5T1.chain_val
#print axioms M5T1.lin_val
#print axioms M5T1.RxField.rx_rel_of_row
#print axioms M5T1.SpecLink.consts
#print axioms M5T1.SpecLink.actExec_fc
#print axioms M5T1.SpecLink.refunds_fc
#print axioms M5T1.SpecLink.stake_fc
#print axioms M5T1.SpecLink.merge_fc
#print axioms M5T1.SpecLink.burnt_fc
#print axioms M5T1.SpecLink.totals_fc
#print axioms M5T1.SpecLink.validActs_fc
#print axioms M5T1.T1.t1_rel
#print axioms M5T1.T1.t1_spec
-- F-2
#print axioms M5T1.Obl.tmplSound_image
#print axioms M5T1.Obl.from_of_sound
#print axioms M5T1.Obl.e2e_sound_t1_from
#print axioms M5T1.Bus.recv_sender
#print axioms M5T1.Bus.rng_recv
#print axioms M5T1.Bus.rx_rel_of_holds
#print axioms M5T1.MsgSpec.rl_spec
#print axioms M5T1.MsgSpec.key_spec
#print axioms M5T1.MsgSpec.acct_spec
#print axioms M5T1.MsgSpec.rref_spec
#print axioms M5T1.MsgSpec.part_spec
#print axioms M5T1.MsgSpec.leaf_link
#print axioms M5T1.MsgRow.sch_row
#print axioms M5T1.MsgRow.msg_walk
#print axioms M5T1.MsgRow.span_of
#print axioms M5T1.MsgRow.dg_digest
#print axioms M5T1.MsgRow.dg_digest'
#print axioms M5T1.SegRt.carried_eq
#print axioms M5T1.SegRt.const_eq
#print axioms M5T1.SegRt.segSoundRt_enter_from

import M5T1.RxRow
import M5T1.T1
import M5T1.Obl
import M5T1.Bus
import M5T1.MsgSpec
import M5T1.MsgRow
import M5T1.MsgRowDg
import M5T1.MsgRowId
import M5T1.SegRt
import M5T1.EnterC
import M5T1.T1Enter
import M5T1.SplitC
import M5T1.ResumeC
import M5T1.T1Resume
import M5T1.ResumeF
import M5T1.SeC
import M5T1.T1Se

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
#print axioms M5T1.SegRt.copy_sem
#print axioms M5T1.SegRt.num_sem
#print axioms M5T1.EnterC.enter_relC
#print axioms M5T1.EnterC.enter_relC8
#print axioms M5T1.EnterC.enter_notInit
#print axioms M5T1.T1Enter.t1_ent_holds
#print axioms M5T1.T1Enter.t1_enter_nonvac
#print axioms M5T1.T1Enter.t1_enter_opens
#print axioms M5T1.SplitC.split_sound_relC
#print axioms M5T1.SplitC.glue_of
#print axioms M5T1.SplitC.rt_relC8

-- F-4: the resume leaf
#print axioms M5T1.RbSem.rb_out
#print axioms M5T1.AccDef.chainDig_pad
#print axioms M5T1.ResumeC.rsView_viewE
#print axioms M5T1.ResumeC.resume_engHalf
#print axioms M5T1.ResumeC.resume_relC8
#print axioms M5T1.ResumeC.rt_relC8_full
#print axioms M5T1.ResumeC.enter_pos_laneB
#print axioms M5T1.T1Resume.t1_rb_constr
#print axioms M5T1.T1Resume.t1_acc0
#print axioms M5T1.T1Resume.t1_acc1
#print axioms M5T1.AccSem.acc_sound
#print axioms M5T1.ResumeF.rsHolds_of
-- F-5
#print axioms M5T1.RbSem.rb_fin_in
#print axioms M5T1.RbSem.preRec_ne_fin
#print axioms M5T1.SeSem.se_out
#print axioms M5T1.SeC.se_engHalf
#print axioms M5T1.SeC.fin_engHalf
#print axioms M5T1.SeC.finalize_relC8
#print axioms M5T1.T1Se.t1_se_constr
#print axioms M5T1.T1Se.t1_se_chain

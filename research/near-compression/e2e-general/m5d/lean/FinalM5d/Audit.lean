import FinalM5d.Tail
import FinalM5d.T1Check
import FinalM5d.RsCoeff
import FinalM5d.HbWhole
import FinalM5d.RsRow
import FinalM5d.RsByte
import FinalM5d.Split
import FinalM5d.BOut
import FinalM5d.MrkWalk

/-! Axiom audit of the M5d headline results: each must depend on `propext`, `Classical.choice`,
`Quot.sound` only (no `sorryAx`, no `Lean.ofReduceBool`). -/

#print axioms FinalM5d.Decode.decode_F1
#print axioms FinalM5d.Link.row_headerOk
#print axioms FinalM5d.FinRow.rowOK_of_constraints
#print axioms FinalM5d.FinRow.fin_headerOk
#print axioms FinalM5d.Tail.tailNew_outputsOf
#print axioms FinalM5d.Tail.final_template_sound
#print axioms FinalM5d.T1.t1_rowOK
#print axioms FinalM5d.T1.t1_window
#print axioms FinalM5d.T1.t1_outputs
#print axioms FinalM5d.T1.t1_headerOk
#print axioms FinalM5d.RsCoeff.coeff_linear
#print axioms FinalM5d.BusMem.recv_sent
#print axioms FinalM5d.BusMem.sent_recv
#print axioms FinalM5d.HbWhole.hb_bytes
#print axioms FinalM5d.HbWhole.fin_row0_act
#print axioms FinalM5d.HbWhole.final_template_sound_holds
#print axioms FinalM5d.RsRow.rs_parity_bit
#print axioms FinalM5d.RsRow.rs_parity_bit_holds
#print axioms FinalM5d.RsByte.rs_parity_byte
#print axioms FinalM5d.RsByte.rs_parity_byte_holds
#print axioms FinalM5d.Split.step_fin
#print axioms FinalM5d.Split.segSoundFinal_join
#print axioms FinalM5d.Split.final_join_headerOk
#print axioms FinalM5d.Split.segSoundInit_join
#print axioms FinalM5d.BOut.encCIF1_hdrF1
#print axioms FinalM5d.MrkWalk.walkLevel_eq
#print axioms FinalM5d.MrkWalk.walkRoot_eq

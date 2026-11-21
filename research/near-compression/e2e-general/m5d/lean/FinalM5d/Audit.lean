import FinalM5d.Tail
import FinalM5d.T1Check
import FinalM5d.RsCoeff

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

import Lean

/-!
# ZkFormal.Near.Render.Proof.RcptAttr — simp set `rcols` (column and state numerals of the `rcpt` table)
-/

register_simp_attr rcols

/-- Cells of the `rcpt` segment / claim rows, column by column (`Proof/RcptCol`). -/
register_simp_attr rseg
register_simp_attr rcl

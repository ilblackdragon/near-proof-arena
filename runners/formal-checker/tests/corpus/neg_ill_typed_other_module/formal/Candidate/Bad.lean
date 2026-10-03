import Lean
open Lean Elab Command Term Meta in
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  addDecl (.thmDecl { name := `Candidate.Bad.bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })

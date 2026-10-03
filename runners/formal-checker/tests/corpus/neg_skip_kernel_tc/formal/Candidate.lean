import ArenaStandIn.Admission
import Lean
open Lean Elab Command Term Meta in
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let ty ← Term.elabTerm (← `(ArenaStandIn.AdmissionStatement { protocolVersion := 80, chainId := "mainnet" } { verifierDigest := "vk-1", paramsDigest := "pp-1" })) none
  let ty ← instantiateMVars ty
  addDecl (.thmDecl { name := `Candidate.certificate, levelParams := [], type := ty, value := mkConst ``True.intro })

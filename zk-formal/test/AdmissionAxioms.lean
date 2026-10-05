/-
CI axiom gate for the zk-formal admission certificates (.github/workflows/ci.yml,
job `lean (zk-formal)`; audit finding A07). Run from `zk-formal/` after
`lake build`:

    lake env lean test/AdmissionAxioms.lean

Fails (non-zero exit, Lean error) if either theorem depends on any axiom other
than `propext`, `Classical.choice`, `Quot.sound` — in particular `sorryAx`,
`Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`) or a project axiom.
This checks axioms only: explicit hypotheses such as `L6Facts` of
`near_admission` remain open obligations and are not discharged here.
-/
import Lean
import ZkFormal.Toy.Certificate
import ZkFormal.NearAssembly.Certificate

open Lean Elab Command

/-- `#assert_standard_axioms c`: error unless `c` exists and its axiom closure
is contained in the standard three. -/
elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !allowed.contains a)
  if bad.isEmpty then
    logInfo m!"AXIOMS-OK {n}: {axs.toList}"
  else
    throwError "AXIOMS-FORBIDDEN {n} depends on non-standard axioms {bad.toList} (all: {axs.toList})"

#print axioms ZkFormal.Toy.toy_admission
#print axioms ZkFormal.NearAssembly.near_admission

#assert_standard_axioms ZkFormal.Toy.toy_admission
#assert_standard_axioms ZkFormal.NearAssembly.near_admission

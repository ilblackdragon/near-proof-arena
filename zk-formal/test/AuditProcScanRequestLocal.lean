import ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyEnd
import ZkFormal.NearV3.Candidates.ProcScanRequestInteriorFrame
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyInterior
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyTerminal
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyBoundary
import ZkFormal.NearV3.Candidates.ProcScanRequestBody
import ZkFormal.NearV3.Candidates.ProcScanRequestLocal

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag.mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag.mask

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag.terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag.terminal

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBodyEnd.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBodyEnd.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestInteriorFrame.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestInteriorFrame.frame

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBodyInterior.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBodyInterior.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBodyTerminal.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBodyTerminal.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBodyBoundary.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBodyBoundary.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestBody.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestBody.physical

/-- info: 'ZkFormal.NearV3.Candidates.ProcScanRequestLocal.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcScanRequestLocal.physical

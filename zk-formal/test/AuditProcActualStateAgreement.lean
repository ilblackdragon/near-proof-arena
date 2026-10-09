import ZkFormal.NearV3.Candidates.ProcActualStateAgreement

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualStateAgreement.grant_fold_allowance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualStateAgreement.grant_fold_allowance

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualStateAgreement.distribute_allowance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualStateAgreement.distribute_allowance

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualStateAgreement.core_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualStateAgreement.core_state

/-- info: 'ZkFormal.NearV3.Candidates.ProcActualStateAgreement.scheduled_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcActualStateAgreement.scheduled_state

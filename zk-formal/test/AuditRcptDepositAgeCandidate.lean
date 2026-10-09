import ZkFormal.NearV3.Assembly.RcptDepositAgeCandidate

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.depositConstraintsWith_original' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.depositConstraintsWith_original

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.depositConstraintsWith_length' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.depositConstraintsWith_length

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_deposit_age_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_deposit_age_bound

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.candidate_deposit_age_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.candidate_deposit_age_nat

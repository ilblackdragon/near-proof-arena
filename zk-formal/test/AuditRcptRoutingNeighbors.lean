import ZkFormal.NearV3.Assembly.RcptRoutingNeighbors

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.receiver_not_final' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.receiver_not_final

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.planned_receiver_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.planned_receiver_next

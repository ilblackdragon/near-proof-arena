import ZkFormal.NearV3.Assembly.RcptRoutingNext

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.routing_next_active' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.routing_next_active

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.routing_next_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.routing_next_position

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.routing_receiver_next_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.routing_receiver_next_cells

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.routing_receiver_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.routing_receiver_local

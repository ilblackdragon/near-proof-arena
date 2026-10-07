import ZkFormal.V3.Integration

/-! Guard the trusted assumptions of the aligned-size admission path. -/

/-- info: 'ZkFormal.Size.rollAligned_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.Size.rollAligned_of_layout

/-- info: 'ZkFormal.Size.sizeBoundD_le_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.Size.sizeBoundD_le_aligned

/-- info: 'ZkFormal.Size.sizeBoundD_le_alignedP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.Size.sizeBoundD_le_alignedP

/-- info: 'ZkFormal.Size.admission_v2_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.Size.admission_v2_honest

/-- info: 'ZkFormal.Size.V3.padded_twoSha_hint_margin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.Size.V3.padded_twoSha_hint_margin

/-- info: 'ZkFormal.Size.V3.padded_caps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.Size.V3.padded_caps

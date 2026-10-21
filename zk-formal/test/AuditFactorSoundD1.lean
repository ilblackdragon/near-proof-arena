import ZkFormal.NearV3.D1.F1.FactorSound

/-! Guard the assumptions of F1 (`FactorSoundD1 B0`): the main theorem and the top-level lemmas
of the new modules `ZkFormal/NearV3/D1/F1/{WitnessCodec, ClaimGuards, CheckD1}`. -/

/-- info: 'ZkFormal.NearV3.D1.Link.factorSoundD1_B0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.Link.factorSoundD1_B0

/-- info: 'ZkFormal.NearV3.D1.F1.AppTr.ofCF' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.AppTr.ofCF

/-- info: 'ZkFormal.NearV3.D1.F1.AppTr.congr' does not depend on any axioms -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.AppTr.congr

/-- info: 'ZkFormal.NearV3.D1.F1.AppTr.bind' does not depend on any axioms -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.AppTr.bind

/-- info: 'ZkFormal.NearV3.D1.F1.AppTr.bindConst' does not depend on any axioms -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.AppTr.bindConst

/-- info: 'ZkFormal.NearV3.D1.F1.AppTr.pure'' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.AppTr.pure'

/-- info: 'ZkFormal.NearV3.D1.F1.AppTr.throw'' does not depend on any axioms -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.AppTr.throw'

/-- info: 'ZkFormal.NearV3.D1.F1.takeAcc_append_le' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.takeAcc_append_le

/-- info: 'ZkFormal.NearV3.D1.F1.consumed_append_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.consumed_append_append

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pU8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pU8

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pU16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pU16

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pU32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pU32

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pU64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pU64

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pU128' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pU128

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pHash

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pBytes

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTake' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTake

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pAccountId' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pAccountId

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pPublicKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pPublicKey

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pSignature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pSignature

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pCongestion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pCongestion

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pValidatorStake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pValidatorStake

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTrieSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTrieSplit

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pBwRequest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pBwRequest

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pBwRequests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pBwRequests

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pChunkInner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pChunkInner

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pReceipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pReceipt

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pPathItem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pPathItem

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pEntry

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTransition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTransition

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pOption' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pOption

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pMany' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pMany

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pVec

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_txFieldsTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_txFieldsTail

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTxFields_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTxFields_false

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTxFields_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTxFields_true

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTxFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTxFields

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_nonceMode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_nonceMode

/-- info: 'ZkFormal.NearV3.D1.F1.txTail_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.txTail_app

/-- info: 'ZkFormal.NearV3.D1.F1.appTr_pTxD1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.appTr_pTxD1

/-- info: 'ZkFormal.NearV3.D1.F1.lift_label' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.lift_label

/-- info: 'ZkFormal.NearV3.D1.F1.pU32_label' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.pU32_label

/-- info: 'ZkFormal.NearV3.D1.F1.pVec_label_ok' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.pVec_label_ok

/-- info: 'ZkFormal.NearV3.D1.F1.decodeTxVec_spec' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.decodeTxVec_spec

/-- info: 'ZkFormal.NearV3.D1.F1.stateWitnessD1Of_eq' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.stateWitnessD1Of_eq

/-- info: 'ZkFormal.NearV3.D1.F1.decodeStateWitnessD1_encodeSWD1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.decodeStateWitnessD1_encodeSWD1

/-- info: 'ZkFormal.NearV3.D1.F1.decodeWitnessFile_encodeSWD1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.decodeWitnessFile_encodeSWD1

/-- info: 'ZkFormal.NearV3.D1.F1.witnessOfD1_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.witnessOfD1_codec

/-- info: 'ZkFormal.NearV3.D1.F1.prepClaimD1_guards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.prepClaimD1_guards

/-- info: 'ZkFormal.NearV3.D1.F1.claimGuards_of_prepD1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.claimGuards_of_prepD1

/-- info: 'ZkFormal.NearV3.D1.F1.checkD1_witnessOfD1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.D1.F1.checkD1_witnessOfD1

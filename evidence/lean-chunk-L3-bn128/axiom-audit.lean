import NearSpecV3.Wasm.CryptoHost
open NearSpecV3 NearSpecV3.Wasm NearSpecV3.AltBn128
-- field ops + bridges
#print axioms AltBn128.Fq.add_mod
#print axioms AltBn128.Fq.mul_mod
#print axioms AltBn128.Fq.sub_mod
#print axioms AltBn128.Fq.neg_mod
#print axioms AltBn128.Fq.cast_add
#print axioms AltBn128.Fq.cast_mul
#print axioms AltBn128.Fq.cast_sub
#print axioms AltBn128.Fq.q_pos
-- membership
#print axioms AltBn128.dbl_defect_int
#print axioms AltBn128.add_defect_int
#print axioms AltBn128.dbl_membership_int
#print axioms AltBn128.add_membership_scaled
-- codec / pairing structure
#print axioms AltBn128.productIsOne_nil
#print axioms AltBn128.chunksExact_nil
-- the three host arms and the table
#print axioms hostAltBn128G1Multiexp
#print axioms hostAltBn128G1Sum
#print axioms hostAltBn128PairingCheck
#print axioms cryptoHostCall

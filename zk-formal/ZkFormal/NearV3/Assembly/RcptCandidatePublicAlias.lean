import ZkFormal.NearV3.Assembly.RcptCandidateTokenSequence
-- Source PublicAlias.lean SHA256: 3e482ba34815fdc14bea4b9a1b5222a123008d38ee2649c05fea404a0353619c.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptWellformed

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Algebra ZkFormal.Near

/-- Byte range alone does not make a four-byte public count injective in BabyBear. -/
theorem count_u32_alias :
    Bytes8 [1,0,0,120] ∧ leN' [1,0,0,120]=P ∧
    ((1+256*0+65536*0+16777216*120:Nat):Fp)=(0:Fp) ∧ P≠0 := by
  constructor
  · simp [Bytes8]
  · decide

/-- The same alias applies to a valid minimum eight-byte body length. -/
theorem body_u32_alias :
    Bytes8 [9,0,0,120] ∧ leN' [9,0,0,120]=P+8 ∧
    ((9+256*0+65536*0+16777216*120:Nat):Fp)=(8:Fp) ∧ P+8≠8 := by
  constructor
  · simp [Bytes8]
  · decide

/-- Required public natural ranges for decoding the active field-compressed totals.
These must come from the actual native preparation/public binding. -/
structure ReceiptPublicRanges (pub : List Fp) : Prop where
  count : leN' (pubBytes pub PH_N 4)<P
  body : leN' (pubBytes pub PH_BLEN 4)<P

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

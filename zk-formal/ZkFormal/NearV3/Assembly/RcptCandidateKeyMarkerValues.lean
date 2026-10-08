import ZkFormal.NearV3.Assembly.RcptCandidateKeyMarkerFields
-- Source KeyMarkerValues.lean SHA256: e04583dffe00dafe6001c4fa72c4ffafcc883a75e6a88df8076c196dedbfe348.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyMarkerFields

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Key-type serialization is the actual constant register byte. -/
theorem key_kind_byte {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sKT=1) (hf : tr.cell tt q fs=1) :
    tr.cell tt q b=tr.cell tt q RcptV3.kt := by
  rw [b_reg0 hL hq (by simp [regStates]) hs]
  have hh := reg_load hL hq (l:=[c RcptV3.kt]) (by simp [loads]) hs hf 0 (by decide)
  exact hh

/-- Canonical natural metadata for the receiver end marker. -/
theorem key_receiver_end_value {q rN LvN  : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sRID=1) (hf : tr.cell tt q fs=1)
    (hr : tr.cell tt q RcptV3.r=(rN:Fp))
    (hl : tr.cell tt q RcptV3.Lv=(LvN:Fp)) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      ([[rN,2+2*LvN,SYM_END,1]] : List Msg).map Msg.toFp := by
  rw [key_receiver_end_row hL hq hs hf,hr,hl]
  simp only [Msg.toFp,List.map_cons,List.map_nil,←natCast_eq,natCast_add,natCast_mul]
  try rw [show ((2:Nat):Fp)=(2:Fp) by decide]
  try rw [show ((0:Nat):Fp)=(0:Fp) by decide]
  try rw [show ((1:Nat):Fp)=(1:Fp) by decide]

/-- Canonical natural metadata for the access type marker. -/
theorem key_access_type_value {q rN   : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sT0=1) (hf : tr.cell tt q fs=1)
    (hr : tr.cell tt q RcptV3.r=(rN:Fp))
    (he : tr.cell tt q ee=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      ([[W_AK+rN,0,0,0],[W_AK+rN,1,2,0]] : List Msg).map Msg.toFp := by
  rw [key_access_type_row hL hq hs he,hr]
  simp only [Msg.toFp,List.map_cons,List.map_nil,←natCast_eq,natCast_add,natCast_mul]
  try rw [show ((0:Nat):Fp)=(0:Fp) by decide]
  try rw [show ((1:Nat):Fp)=(1:Fp) by decide]
  try rw [show ((2:Nat):Fp)=(2:Fp) by decide]
  have hw : (rN:Fp)+(W_AK:Nat)=(W_AK:Nat)+(rN:Fp) := by grind
  rw [hw]

/-- Canonical natural metadata for the access separator marker. -/
theorem key_access_separator_value {q rN LsN  : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sSL=1) (hf : tr.cell tt q fs=1)
    (hr : tr.cell tt q RcptV3.r=(rN:Fp))
    (he : tr.cell tt q ee=1)
    (hl : tr.cell tt q RcptV3.Ls=(LsN:Fp)) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      ([[W_AK+rN,2+2*LsN,0,0],[W_AK+rN,3+2*LsN,2,0]] : List Msg).map Msg.toFp := by
  rw [key_access_separator_row hL hq hs he hf,hr,hl]
  simp only [Msg.toFp,List.map_cons,List.map_nil,←natCast_eq,natCast_add,natCast_mul]
  try rw [show ((2:Nat):Fp)=(2:Fp) by decide]
  try rw [show ((3:Nat):Fp)=(3:Fp) by decide]
  try rw [show ((0:Nat):Fp)=(0:Fp) by decide]
  have hw : (rN:Fp)+(W_AK:Nat)=(W_AK:Nat)+(rN:Fp) := by grind
  rw [hw]

/-- Canonical natural metadata for the access kind marker. -/
theorem key_access_kind_value {q rN LsN ktN : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sKT=1) (hf : tr.cell tt q fs=1)
    (hr : tr.cell tt q RcptV3.r=(rN:Fp))
    (he : tr.cell tt q ee=1)
    (hl : tr.cell tt q RcptV3.Ls=(LsN:Fp))
    (hk : tr.cell tt q RcptV3.kt=(ktN:Fp)) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      ([[W_AK+rN,4+2*LsN,0,0],[W_AK+rN,5+2*LsN,ktN,0]] : List Msg).map Msg.toFp := by
  rw [key_access_kind_row hL hq hs he,hr,hl]
  rw [key_kind_byte hL hq hs hf,hk]
  simp only [Msg.toFp,List.map_cons,List.map_nil,←natCast_eq,natCast_add,natCast_mul]
  try rw [show ((4:Nat):Fp)=(4:Fp) by decide]
  try rw [show ((5:Nat):Fp)=(5:Fp) by decide]
  try rw [show ((2:Nat):Fp)=(2:Fp) by decide]
  try rw [show ((0:Nat):Fp)=(0:Fp) by decide]
  have hw : (rN:Fp)+(W_AK:Nat)=(W_AK:Nat)+(rN:Fp) := by grind
  rw [hw]

/-- Canonical natural metadata for the access end marker. -/
theorem key_access_end_value {q rN LsN ktN : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sGP=1) (hf : tr.cell tt q fs=1)
    (hr : tr.cell tt q RcptV3.r=(rN:Fp))
    (he : tr.cell tt q ee=1)
    (hl : tr.cell tt q RcptV3.Ls=(LsN:Fp))
    (hk : tr.cell tt q RcptV3.kt=(ktN:Fp)) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      ([[W_AK+rN,70+2*LsN+64*ktN,SYM_END,1]] : List Msg).map Msg.toFp := by
  rw [key_access_end_row hL hq hs he hf,hr,hl,hk]
  simp only [Msg.toFp,List.map_cons,List.map_nil,←natCast_eq,natCast_add,natCast_mul]
  try rw [show ((70:Nat):Fp)=(70:Fp) by decide]
  try rw [show ((2:Nat):Fp)=(2:Fp) by decide]
  try rw [show ((64:Nat):Fp)=(64:Fp) by decide]
  try rw [show ((1:Nat):Fp)=(1:Fp) by decide]
  have hw : (rN:Fp)+(W_AK:Nat)=(W_AK:Nat)+(rN:Fp) := by grind
  rw [hw]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

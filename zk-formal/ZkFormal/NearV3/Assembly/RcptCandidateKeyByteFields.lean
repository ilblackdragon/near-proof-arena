import ZkFormal.NearV3.Assembly.RcptCandidateKeyNibbleValues
-- Source KeyByteFields.lean SHA256: 9d002aec978c710e18281f6c552648ce5353f81b31a9440314df84260bd4d26e.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyNibbleValues

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Receiver rows emit the canonical natural-byte nibble messages, in byte order. -/
theorem key_receiver_field {s start len rN : Nat} (hf : RFld tr tt s start len sV)
    (hH : start+len≤tr.height tt) (hr : tr.cell tt s RcptV3.r=(rN:Fp)) :
    (List.range' start len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      (symbolMsgs rN 2 ((colAt tr tt start len b).flatMap (fun v => [v/16,v%16]))).map Msg.toFp := by
  rw [symbolMsgs_nibbles,colAt_len,List.range'_eq_map_range,List.flatMap_map,List.map_flatMap]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  have hq : start+k<tr.height tt := by omega
  rw [key_receiver_row hL hq (hf.fld.st k hk)]
  obtain ⟨hh,hl⟩ := key_character_nibbles hL hq (Or.inr (Or.inl rfl)) (hf.fld.st k hk)
  rw [hh,hl,hf.consts k hk RcptV3.r (by simp [rconsts]),hr,hf.fld.idx k hk,colAt_get _ _ _ _ _ _ hk]
  simp only [List.map_cons,List.map_nil,Msg.toFp,←natCast_eq,natCast_add,natCast_mul]
  have h2 : ((2:Nat):Fp)=2 := by decide
  have h1 : ((1:Nat):Fp)=1 := by decide
  have h0 : ((0:Nat):Fp)=0 := by decide
  rw [h2,h1,h0]
  have he : (3:Fp)+2*(k:Fp)=2+2*(k:Fp)+1 := by grind
  rw [he]

/-- Refunded signer rows emit the canonical signer-byte nibble sequence. -/
theorem key_signer_field {s start len rN : Nat} (hf : RFld tr tt s start len sS)
    (hH : start+len≤tr.height tt) (hr : tr.cell tt s RcptV3.r=(rN:Fp))
    (he : tr.cell tt s ee=1) :
    (List.range' start len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      (symbolMsgs (W_AK+rN) 2 ((colAt tr tt start len b).flatMap (fun v => [v/16,v%16]))).map Msg.toFp := by
  rw [symbolMsgs_nibbles,colAt_len,List.range'_eq_map_range,List.flatMap_map,List.map_flatMap]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  have hq : start+k<tr.height tt := by omega
  have heq : tr.cell tt (start+k) ee=1 := (hf.consts k hk ee (by simp [rconsts])).trans he
  rw [key_access_signer_row hL hq (hf.fld.st k hk) heq]
  obtain ⟨hh,hl⟩ := key_character_nibbles hL hq (Or.inr (Or.inr rfl)) (hf.fld.st k hk)
  rw [hh,hl,hf.consts k hk RcptV3.r (by simp [rconsts]),hr,hf.fld.idx k hk,colAt_get _ _ _ _ _ _ hk]
  simp only [List.map_cons,List.map_nil,Msg.toFp,←natCast_eq,natCast_add,natCast_mul]
  have h2 : ((2:Nat):Fp)=2 := by decide
  have h1 : ((1:Nat):Fp)=1 := by decide
  have h0 : ((0:Nat):Fp)=0 := by decide
  rw [h2,h1,h0]
  have hw : (rN:Fp)+(W_AK:Nat)=(W_AK:Nat)+(rN:Fp) := by grind
  have ht : (3:Fp)+2*(k:Fp)=2+2*(k:Fp)+1 := by grind
  rw [hw,ht]

/-- Refunded public-key bytes produce their canonical nibbles after the signer and key type. -/
theorem key_public_field {s start len rN LsN : Nat} (hf : RFld tr tt s start len sPK)
    (hH : start+len≤tr.height tt) (hr : tr.cell tt s RcptV3.r=(rN:Fp))
    (hls : tr.cell tt s RcptV3.Ls=(LsN:Fp)) (he : tr.cell tt s ee=1) :
    (List.range' start len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      (symbolMsgs (W_AK+rN) (6+2*LsN) ((colAt tr tt start len b).flatMap (fun v => [v/16,v%16]))).map Msg.toFp := by
  rw [symbolMsgs_nibbles,colAt_len,List.range'_eq_map_range,List.flatMap_map,List.map_flatMap]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  have hq : start+k<tr.height tt := by omega
  have heq : tr.cell tt (start+k) ee=1 := (hf.consts k hk ee (by simp [rconsts])).trans he
  rw [key_access_public_key_row hL hq (hf.fld.st k hk) heq]
  obtain ⟨hh,hl⟩ := key_public_nibbles hL hq (hf.fld.st k hk) heq
  rw [hh,hl,hf.consts k hk RcptV3.r (by simp [rconsts]),hr,
    hf.consts k hk RcptV3.Ls (by simp [rconsts]),hls,hf.fld.idx k hk,colAt_get _ _ _ _ _ _ hk]
  simp only [List.map_cons,List.map_nil,Msg.toFp,←natCast_eq,natCast_add,natCast_mul]
  have h6 : ((6:Nat):Fp)=6 := by decide
  have h2 : ((2:Nat):Fp)=2 := by decide
  have h1 : ((1:Nat):Fp)=1 := by decide
  have h0 : ((0:Nat):Fp)=0 := by decide
  rw [h6,h2,h1,h0]
  have hw : (rN:Fp)+(W_AK:Nat)=(W_AK:Nat)+(rN:Fp) := by grind
  have ht : (7:Fp)+2*(LsN:Fp)+2*(k:Fp)=6+2*(LsN:Fp)+2*(k:Fp)+1 := by grind
  rw [hw,ht]

/-- Entire access-byte fields disappear when the refund gate is disabled. -/
theorem key_access_field_silent {s start len X : Nat} (hf : RFld tr tt s start len X)
    (hH : start+len≤tr.height tt) (hx : X∈[sT0,sS,sKT,sPK]) (he : tr.cell tt s ee=0) :
    (List.range' start len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  exact key_access_byte_silent hL (by omega) hx (hf.fld.st k hk)
    ((hf.consts k hk ee (by simp [rconsts])).trans he)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

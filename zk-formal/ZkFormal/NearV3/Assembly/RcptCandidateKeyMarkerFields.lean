import ZkFormal.NearV3.Assembly.RcptCandidateKeyByteFields
-- Source KeyMarkerFields.lean SHA256: 068b409d03f7b165cd4a81b71a377d46e78ba7bac2354a99aa10a5e3fba5e8ac.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyByteFields

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- All three marker fields contribute exactly their first physical row. -/
theorem key_marker_field {s start len X : Nat} (hf : RFld tr tt s start len X)
    (hH : start+len≤tr.height tt) (hx : X=sRID ∨ X=sSL ∨ X=sGP) :
    (List.range' start len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      rowTraffic RcptV3.interactions tr tt start pub B_KEYNIB true := by
  have hp := hf.fld.pos
  rw [flatMap_window _ start len 0 1 (by omega)]
  · simp only [Nat.add_zero,List.range'_one,List.flatMap_singleton]
  · intro k hk ho
    have hfs : tr.cell tt (start+k) fs=0 := by rw [hf.fld.fs k hk,if_neg (by omega)]
    rcases hx with rfl|rfl|rfl
    · exact key_receiver_end_silent hL (by omega) (hf.fld.st k hk) hfs
    · exact key_access_marker_silent hL (by omega) (Or.inl rfl) (hf.fld.st k hk) (Or.inr hfs)
    · exact key_access_marker_silent hL (by omega) (Or.inr rfl) (hf.fld.st k hk) (Or.inr hfs)

/-- The physical receiver-length field contributes exactly its two zero-prefix symbols. -/
theorem Layout.key_prefix_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    (List.range' (y.s+(4+y.Lp)) 4).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      [[rN,0,0,0],[rN,1,0,0]].map Msg.toFp := by
  have hm : (sVL,4+y.Lp,4)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F := lay.flds _ hm
  have hfin := lay.fin
  have htot : 8+y.Lp≤y.tot := by unfold RS.tot total Vt; split <;> omega
  unfold RS.tot at htot
  have hkz : ∀k,k<4 → tr.cell tt (y.s+(4+y.Lp)+k) kz=if k<2 then 1 else 0 := by
    intro k hk
    rw [show y.s+(4+y.Lp)+k=y.s+(4+y.Lp+k) by omega,kz_row hL lay _ (by omega)]
    by_cases hc : k<2
    · rw [if_pos hc,if_pos (by omega)]
    · rw [if_neg hc,if_neg (by omega)]
  have hrow : ∀k,k<4 → rowTraffic RcptV3.interactions tr tt (y.s+(4+y.Lp)+k) pub B_KEYNIB true=
      if k<2 then [[rN,k,0,0]].map Msg.toFp else [] := by
    intro k hk
    have hq : y.s+(4+y.Lp)+k<tr.height tt := by omega
    by_cases h2 : k<2
    · rw [if_pos h2,key_receiver_prefix_row hL hq (F.fld.st k hk) (by rw [hkz k hk,if_pos h2]),
        F.consts k hk RcptV3.r (by simp [rconsts]),hr,F.fld.idx k hk]
      simp only [Msg.toFp,List.map_cons,List.map_nil,←natCast_eq]
      rw [show ((0:Nat):Fp)=(0:Fp) by decide]
    · rw [if_neg h2]
      exact key_receiver_prefix_silent hL hq (F.fld.st k hk) (by rw [hkz k hk,if_neg h2])
  rw [List.range'_eq_map_range,List.flatMap_map]
  have hmap : (List.range 4).flatMap (fun k => rowTraffic RcptV3.interactions tr tt (y.s+(4+y.Lp)+k) pub B_KEYNIB true)=
      (List.range 4).flatMap (fun k => if k<2 then [[rN,k,0,0]].map Msg.toFp else []) :=
    flatMap_congr' (fun k hk => hrow k (List.mem_range.mp hk))
  rw [hmap]
  simp [List.range_succ]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

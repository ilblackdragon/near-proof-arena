import ZkFormal.NearV3.Rcpt.Extract.V.SignerTrafficRows

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Exact selected-character messages of a concrete receiver/signer field. -/
theorem srec_field {s start len rN : Nat} (sd : Bool)
    (hf : RFld tr tt s start len (if sd then sV else sS))
    (hr : tr.cell tt s RcptV3.r=(rN : Fp)) :
    (List.range' start len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC sd)=
      (((List.range len).filter (fun k => decide (tr.cell tt (start+k) (if sd then gV else gS)=1))).map
        (fun k => [rN,k,cv tr tt (start+k) (if sd then b else sx)] : Nat→Msg)).map Msg.toFp := by
  rw [List.range'_eq_map_range,List.flatMap_map,List.map_map,←gated_list]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  rw [rowT_srec]
  have hh := hf.consts k hk RcptV3.r (by simp [rconsts])
  have hi := hf.fld.idx k hk
  simp only [gt,hh,hr,hi,decide_eq_true_eq,Function.comp_def]
  simp only [Msg.toFp,List.map_cons,List.map_nil,cv,Fp.ofNat_toNat,natCast_eq]

/-- Receiver traffic is confined to its actual receiver-string field. -/
theorem Layout.srec_receiver_window {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC true)=
      (List.range' (y.s+(8+y.Lp)) y.Lv).flatMap
        (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC true) := by
  have hm : (sV,8+y.Lp,y.Lv)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := h.fin
  simp only at hl
  apply flatMap_window _ y.s y.tot (8+y.Lp) y.Lv hl
  intro j hj hout
  exact srec_silent hL (by unfold RS.tot at hj; omega) true (st_row hL h hm j hj hout)

/-- Signer traffic is confined to its actual signer-string field. -/
theorem Layout.srec_signer_window {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC false)=
      (List.range' (y.s+(45+y.Lp+y.Lv)) y.Ls).flatMap
        (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC false) := by
  have hm : (sS,45+y.Lp+y.Lv,y.Ls)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := h.fin
  simp only at hl
  apply flatMap_window _ y.s y.tot (45+y.Lp+y.Lv) y.Ls hl
  intro j hj hout
  exact srec_silent hL (by unfold RS.tot at hj; omega) false (st_row hL h hm j hj hout)

end ZkFormal.NearV3.RcptV3Proof

import ZkFormal.NearV3.Rcpt.Extract.V.AccessTrafficRows

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def accessCounterMsgs (sd : Bool) (_r : Nat) (x : RcptE) : List Msg :=
  if x.ee ∧ x.akf=0 then [[x.akk,x.aku+(if sd then 1 else 0)]] else []

/-- Access-counter messages agree with both unchanged semantic traffic functions. -/
theorem accessCounterMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) (sd : Bool) :
    indexedReceiptMsgs tr tt bs (accessCounterMsgs sd)=
      (if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_AKC
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_AKC) := by
  rw [indexedReceiptMsgs_view]
  cases sd <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,rcptSends3,rcptRecvs3,
      show B_AKC≠B_BYTES by decide,show B_AKC≠B_RCL by decide,List.nil_append]
  all_goals
    apply flatMap_congr'
    intro j _
    apply flatMap_congr'
    intro x _
    simp [rSends,rRecvs,accessCounterMsgs,B_MEM,B_BYTES,B_KEYNIB,B_RIDS,B_MPOS,B_SREC,B_AKC,B_FINAL,B_DIGEST]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Actual access-counter lookup and successor, enabled exactly by the extracted
system/self receipt and present access-key flag. -/
theorem Layout.access_counter {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (sd : Bool) :
    (List.range' y.s y.tot).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_AKC sd)=
      (accessCounterMsgs sd 0 (rcptOf tr tt y)).map Msg.toFp := by
  rw [h.akc_window hL,rowT_akc]
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hf := h.flds _ hm
  have hfin := h.fin
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hl
  have hq : y.s+(40+y.Lp+y.Lv)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(40+y.Lp+y.Lv)) sT0=1 := by simpa using hf.fld.st 0 (by simp)
  have he : tr.cell tt (y.s+(40+y.Lp+y.Lv)) ee=tr.cell tt y.s ee := by
    simpa using hf.consts 0 (by simp) ee (by simp [rconsts])
  rw [akc_gate hL hq,hs,he]
  have hee := isBool hL (r:=y.s) (by omega) (x:=ee) (by simp [boolCols])
  have hfk := isBool hL hq (x:=fkF) (by simp [boolCols])
  have g00 : (0:Fp)*1*(1-0)=0 := by decide
  have g01 : (0:Fp)*1*(1-1)=0 := by decide
  have g10 : (1:Fp)*1*(1-0)=1 := by decide
  have g11 : (1:Fp)*1*(1-1)=0 := by decide
  have z0 : (0:Fp).toNat=0 := by decide
  have z1 : (1:Fp).toNat=1 := by decide
  have succ_cast (a : Fp) : Fp.ofNat (a.toNat+1)=a+1 := by
    change ((a.toNat+1:Nat):Fp)=_
    rw [natCast_add,natCast_eq,Fp.ofNat_toNat]
    rfl
  rcases hee with hee|hee <;> rcases hfk with hfk|hfk <;> cases sd <;>
    simp [succ_cast,g00,g01,g10,g11,z0,z1,accessCounterMsgs,rcptOf,hee,hfk,gt,cv,Msg.toFp,natCast_add,natCast_eq,Fp.ofNat_toNat] <;> congr 3 <;> grind

/-- Complete access-key counter traffic, in both directions, for every receipt
and all header/padding rows of the physical table. -/
theorem ListChain.access_counter_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_AKC sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_AKC
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_AKC).map Msg.toFp) := by
  rw [←accessCounterMsgs_view]
  apply h.indexed_traffic hL
  · intro B hB
    exact (h.blocks B hB).header_akc hL sd
  · intro q hq ha
    exact akc_silent hL hq (noState hL hq ha sT0 (by simp [states])) sd
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact hw.access_counter hL sd

end ZkFormal.NearV3.RcptV3Proof

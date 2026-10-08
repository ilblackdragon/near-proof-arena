import ZkFormal.NearV3.Render.Ups.CompactExtract.Physical
import ZkFormal.NearV3.Render.Ups.CompactByteTraffic
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows

/-- The removed SPOST receive is identically silent on compact rows. Every
remaining bus message agrees with the existing extracted-row representation. -/
theorem compactMsgs_eq {C D : URow} (hv : C vb=0) (b : Nat) (sd : Bool) :
    compactMsgs C D b sd=uMsgs C D b sd := by
  simp [compactMsgs,compactInteractions,uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,hv,cast_ofNat,cast0]

/-- Inactive physical rows emit no messages on any bus. -/
theorem quiet {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) (hD : ∀x,D x<P)
    (ha : C act=0) (b : Nat) (sd : Bool) : compactMsgs C D b sd=[] := by
  rw [compactMsgs_eq (noValue ok hC)]
  have hh:=currentKinds ok hC
  have hw : C wt3=0 := by omega
  exact UpsRows.quiet (oldRowOk ok hC hw) hC hD ha b sd
end ZkFormal.NearV3.Render.UpsRelay.Extract

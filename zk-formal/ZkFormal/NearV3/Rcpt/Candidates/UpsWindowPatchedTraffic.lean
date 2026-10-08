import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowCounterPatch
import ZkFormal.Near.Extract.BusCount

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl Render.UpsRelay

/-- The actual six UPB fields of a physical row, excluding its counter. -/
def windowFieldKey (tr : Trace Fp) (t r : Nat) : List Fp :=
  [Fp.ofNat K_NPOST+Fp.ofNat 16*tr.cell t r UpsV3.sN,
    tr.cell t r UpsV3.spos,tr.cell t r UpsV3.rb,tr.cell t r UpsV3.plen,
    tr.cell t r UpsV3.pdep,tr.cell t r UpsV3.rcid]

theorem patched_window_row (tr : Trace Fp) (t r : Nat) (rank : Nat→Nat)
    (pub : List Fp) (sd : Bool) :
    rowTraffic compactInteractions (patchWindowCounters tr t rank) t r pub B_UPB sd=
      if tr.cell t r UpsV3.rd=1 then
        [windowFieldKey tr t r++[Fp.ofNat (rank r+(if sd then 1 else 0))]] else [] := by
  cases sd <;> by_cases hr : tr.cell t r UpsV3.rd=1 <;>
    simp only [UpsV3.rd] at hr <;>
    simp [rowTraffic,compactInteractions,UpsV3.interactions,send,recv,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
      B_UPB,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_EDGE,B_BMAP,B_MEMD,
      UpsV3.upbMsg,mid,smul,c,k,patchWindowCounters,hr,
      UpsV3.rd,UpsV3.u,UpsV3.sN,UpsV3.spos,UpsV3.rb,UpsV3.plen,UpsV3.pdep,UpsV3.rcid,
      windowFieldKey]

  all_goals simp only [←ofNat_add',←ofNat_mul',Fp.ofNat_toNat]
  all_goals first | rfl | exact ⟨rfl,rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

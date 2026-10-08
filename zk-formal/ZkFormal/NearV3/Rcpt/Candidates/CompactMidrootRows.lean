import ZkFormal.NearV3.Rcpt.Candidates.CompactWalkRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

set_option maxHeartbeats 800000

theorem compact_midroot_send (C D : URow) : compactMsgs C D B_MIDROOT true=[] := by
  simp [compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_EDGE,B_BMAP,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD]

theorem compact_midroot_recv (C D : URow) :
    compactMsgs C D B_MIDROOT false=
      if Fp.ofNat (C UpsV3.sf)=1 then
        [reduceMessage ([C UpsV3.tau,C UpsV3.rootRid]++(List.range 32).map (fun i=>C (UpsV3.reg i)))] else [] := by
  simp [compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_EDGE,B_BMAP,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,UpsV3.regs,reduceMessage,List.map_map,Function.comp_def]
  split <;> simp_all

theorem compact_midroot_silent (C D : URow) (hs : C UpsV3.sf=0) :
    compactMsgs C D B_MIDROOT false=[] := by
  rw [compact_midroot_recv,hs]
  have hz : ¬(Fp.ofNat 0=1):=by decide
  simp only [hz,ite_false]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

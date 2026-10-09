import ZkFormal.NearV3.Candidates.ProcCodecPresenceTraffic
namespace ZkFormal.NearV3.Candidates.ProcCodecPriorReadTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.Chacha.Table.E

/-- Bus68 contains only the actual prior-state query. -/
theorem codec_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions tr t r pub 68 false =
      List.replicate (if tr.cell t r Codec.fA*tr.cell t r Codec.e2=1 then 1 else 0)
        [tr.cell t r Codec.tau,tr.cell t r Codec.kidx,tr.cell t r Codec.apR,tr.cell t r Codec.bigR] := by
  simp [ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,c,
    B_SPOST,ZkFormal.NearV3.Sched.B_S0F,ZkFormal.NearV3.Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP,
    B_BYTES,B_DIGEST,B_VBYTES,ProcPriorCodecActual.idLo,ProcPriorCodecActual.idMid,
    ProcPriorCodecActual.idHi,ProcPriorCodecActual.idByte,smul]

end ZkFormal.NearV3.Candidates.ProcCodecPriorReadTraffic

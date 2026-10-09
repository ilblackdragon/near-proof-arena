import ZkFormal.NearV3.Candidates.ProcCodecPresenceTraffic
namespace ZkFormal.NearV3.Candidates.ProcCodecPublicIdTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.Chacha.Table.E

def message (tau sender : Fp) (byte : Nat→Fp) : List Fp :=
  [tau,sender,byte 0+(256*byte 1+65536*byte 2),
    byte 3+(256*byte 4+65536*byte 5),byte 6+256*byte 7]

/-- Bus70 contains only the actual public-ID interaction. -/
theorem codec_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions tr t r pub 70 true =
      List.replicate (if tr.cell t r Codec.rs*tr.cell t r Codec.nzb=1 then 1 else 0)
        (message (tr.cell t r Codec.tau) (tr.cell t r Codec.srcC)
          (fun i=>tr.cell t r (Codec.prbit i))) := by
  unfold message
  simp [ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,c,
    B_SPOST,B_S0F,ZkFormal.NearV3.Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP,
    B_BYTES,B_DIGEST,B_VBYTES,ProcPriorCodecActual.idLo,ProcPriorCodecActual.idMid,
    ProcPriorCodecActual.idHi,ProcPriorCodecActual.idByte,smul]
  right
  constructor
  · congr 2 <;> congr 1 <;> decide +kernel
  constructor
  · congr 2 <;> congr 1 <;> decide +kernel
  · congr 1 <;> congr 1 <;> decide +kernel

end ZkFormal.NearV3.Candidates.ProcCodecPublicIdTraffic

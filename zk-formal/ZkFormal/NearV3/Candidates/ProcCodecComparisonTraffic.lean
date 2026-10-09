import ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
import ZkFormal.NearV3.Candidates.ProcCodecComparisonCells
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

theorem messages (row : Nat→Fp) : ProcCodecConcatTraffic.messages row B_SCMP true=
    List.replicate (if row cg=1 then 1 else 0) [row cx,row cy,row cbit] := by
  simp [ProcCodecConcatTraffic.messages,ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,Codec.encG,Codec.shaId,Codec.aLE,Codec.oE,
    ProcPriorCodecActual.idLo,ProcPriorCodecActual.idMid,ProcPriorCodecActual.idHi,
    ZkFormal.Near.Dsl.mid,ZkFormal.Near.Dsl.smul,ZkFormal.Near.Dsl.c,ZkFormal.Near.Dsl.k,Function.comp_def,
    B_BYTES,Sched.B_SPLEN,B_SCMP,B_SPOST,B_S0F,B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0]

theorem nat_messages (row : Array Nat) : ProcCodecConcatTraffic.natMessages row B_SCMP true=
    List.replicate (if Fp.ofNat row[cg]! = 1 then 1 else 0) [Fp.ofNat row[cx]!,Fp.ofNat row[cy]!,Fp.ofNat row[cbit]!] :=
  messages _
end ZkFormal.NearV3.Candidates.ProcCodecComparisonTraffic

import ZkFormal.NearV3.Candidates.ProcPriorCodecActual
import ZkFormal.NearV3.Candidates.ProcPriorRawByteTraffic
namespace ZkFormal.NearV3.Candidates.ProcCodecPresenceTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.Chacha.Table.E

/-- Only the corrected presence interaction supplies SPOST; the retired
post-byte interaction is the fresh-value SHA relay on BYTES. -/
theorem codec_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions tr t r pub B_SPOST true =
      List.replicate (if tr.cell t r Codec.kF=1 then 1 else 0)
        [tr.cell t r Codec.tau,tr.cell t r Codec.pres,tr.cell t r Codec.vid] := by
  simp [ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,c,
    B_SPOST,B_S0F,ZkFormal.NearV3.Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP,
    B_BYTES,B_DIGEST,B_VBYTES]

theorem raw_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      tr t r pub B_SPOST false =
      List.replicate (if tr.cell t r ProcPriorRawFrame.first=1 then 1 else 0)
        [tr.cell t r ProcPriorRawFrame.tau,tr.cell t r ProcPriorRawFrame.present,
          tr.cell t r ProcPriorRawFrame.vid] := by
  simp [ProcPriorRawFrame.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,c,B_SPOST,B_VBYTES]

/-- Exact row join, including absence: presence is a message component and
never gates away a missing-state request. -/
theorem row_balance (codec raw : Trace Fp) (t r s : Nat) (pub : List Fp)
    (hg : codec.cell t r Codec.kF=raw.cell t s ProcPriorRawFrame.first)
    (ht : codec.cell t r Codec.tau=raw.cell t s ProcPriorRawFrame.tau)
    (hp : codec.cell t r Codec.pres=raw.cell t s ProcPriorRawFrame.present)
    (hv : codec.cell t r Codec.vid=raw.cell t s ProcPriorRawFrame.vid) :
    rowTraffic ProcPriorCodecActual.table.interactions codec t r pub B_SPOST true =
      rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
        raw t s pub B_SPOST false := by
  rw [codec_row,raw_row,hg,ht,hp,hv]
end ZkFormal.NearV3.Candidates.ProcCodecPresenceTraffic

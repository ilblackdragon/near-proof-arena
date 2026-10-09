import ZkFormal.NearV3.Candidates.ProcCodecPresenceGate
import ZkFormal.NearV3.Candidates.ProcRawPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecParameterTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPhysicalPadding
open ProcPriorCodecSideCarry ProcPriorCodecNativeHash SchedSetAll

theorem codec_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions tr t r pub 76 true =
      List.replicate (if tr.cell t r Codec.kF=1 then 1 else 0)
        [tr.cell t r Codec.tau,tr.cell t r Codec.nn] := by
  simp [ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    B_SPOST,B_S0F,ZkFormal.NearV3.Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP,
    B_BYTES,B_DIGEST,B_VBYTES]

theorem row (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t r pub 76 true =
      if r=0 then [[Fp.ofNat R.tau,Fp.ofNat R.n]] else [] := by
  rw [codec_row]
  change List.replicate (if cells out.rows r kF=1 then 1 else 0)
    [cells out.rows r tau,cells out.rows r nn]=_
  have hzero : Fp.ofNat 0=0 := rfl
  have hone : Fp.ofNat 1=1 := rfl
  have hl:=generated_length I R present vidV gb fwd out h
  by_cases hr:r<out.rows.size
  · rw [ProcCodecPhysicalRows.active_cells out.rows r hr]
    dsimp only
    simp only [ProcCodecPresenceGate.active I R present vidV gb fwd out h r hr]
    by_cases hz:r=0
    · subst r
      have hi:=ProcCodecGeneratedInstance.generated I R present vidV gb fwd out h
        out.rows[0]! (by simp [show 0<out.rows.size by omega])
      have ht:=hi tau (by decide +kernel)
      have hn:=hi nn (by decide +kernel)
      rw [ht,hn]
      simp [hzero,hone,instanceValue,instanceCells,lookup,tau,pres,vid,act,nn,NN,base,fair,itz,zt]
    · simp [hz,hzero,hone]
  · rw [padding_cells out.rows r (by omega)]
    have hz:r≠0 := by omega
    simp [hz,hzero,hone]

theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace out.rows codecPad) t r pub 76 true) =
      [[Fp.ofNat R.tau,Fp.ofNat R.n]] := by
  simp only [row I R present vid gb fwd out h]
  exact ProcRawPresencePhysical.singleton_range _ (by decide +kernel) _

theorem count (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t pub 76 true msg =
      [[Fp.ofNat R.tau,Fp.ofNat R.n]].count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical I R present vid gb fwd out h t pub)

end ZkFormal.NearV3.Candidates.ProcCodecParameterTraffic

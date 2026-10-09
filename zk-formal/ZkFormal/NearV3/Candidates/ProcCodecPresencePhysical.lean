import ZkFormal.NearV3.Candidates.ProcCodecPresenceGate
import ZkFormal.NearV3.Candidates.ProcRawPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPhysicalPadding
open ProcPriorCodecSideCarry ProcPriorCodecNativeHash SchedSetAll

theorem row (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t r pub B_SPOST true =
      if r=0 then [[Fp.ofNat R.tau,Fp.ofNat (b2n present),Fp.ofNat vidV]] else [] := by
  rw [ProcCodecPresenceTraffic.codec_row]
  change List.replicate (if cells out.rows r kF=1 then 1 else 0)
    [cells out.rows r tau,cells out.rows r pres,cells out.rows r vid]=_
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
      have hp:=hi pres (by decide +kernel)
      have hv:=hi vid (by decide +kernel)
      rw [ht,hp,hv]
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
      (SchedHeight.trace out.rows codecPad) t r pub B_SPOST true) =
      [[Fp.ofNat R.tau,Fp.ofNat (b2n present),Fp.ofNat vid]] := by
  simp only [row I R present vid gb fwd out h]
  exact ProcRawPresencePhysical.singleton_range _ (by decide +kernel) _

theorem count (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t pub B_SPOST true msg =
      [[Fp.ofNat R.tau,Fp.ofNat (b2n present),Fp.ofNat vid]].count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical I R present vid gb fwd out h t pub)

theorem main_balance (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (ht:R.tau=0)
    (prior : NearSpec.Bandwidth.State) (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t pub B_SPOST true msg =
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcPriorRawGen.trace prior vid present) t pub B_SPOST false msg := by
  rw [count I R present vid gb fwd out h,ProcRawPresencePhysical.count,ht]
  cases present <;> rfl
end ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical

import ZkFormal.NearV3.Candidates.ProcCodecSanityGate
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
import ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecSanityTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPhysicalPadding
open ProcPriorCodecAssignments ProcPriorCodecSideCarry ProcPriorCodecNativeHash SchedSetAll

theorem row_message (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions tr t r pub 74 false =
      List.replicate (if tr.cell t r Codec.kZ=1 then 1 else 0)
        [tr.cell t r Codec.tau,tr.cell t r Codec.sj,tr.cell t r Codec.bpre] := by
  simp [ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    B_SPOST,ZkFormal.NearV3.Sched.B_S0F,ZkFormal.NearV3.Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP,
    B_BYTES,B_DIGEST,B_VBYTES]

def priorByte (I : Input) (present : Bool) (j : Nat) : Nat :=
  if present then (I.prev.sanityHash.map UInt8.toNat)[j]! else 0

theorem hash_payload (I : Input) (R : Run) (present : Bool) (vidV j : Nat) :
    let row:=hashRow (instanceCells I R present vidV) (ProcPriorCodecNativeBytes.digest I present)
      (ProcPriorCodecNativeBytes.priorHash I present) present (5+24*(R.n*R.n)) j
    [Fp.ofNat row[tau]!,Fp.ofNat row[sj]!,Fp.ofNat row[bpre]!]=
      [Fp.ofNat R.tau,Fp.ofNat j,Fp.ofNat (priorByte I present j)] := by
  dsimp only
  rw [ProcPriorCodecHashReads.projection _ _ _ _ _ _ tau (by decide +kernel),
    ProcPriorCodecSideZero.hash_scalar I R present vidV _ _ _ j sj (by decide +kernel),
    ProcPriorCodecHashReads.prior_byte]
  cases present <;> simp [ProcPriorCodecHashReads.hashScalars,instanceCells,lookup,
    ProcPriorCodecNativeBytes.priorHash,priorByte,tau,sj,act,pres,vid,nn,NN,base,fair,itz,zt,
    kZ,dgg,pos,bpost,bpre,bsha,vbg,isj,esj]

theorem row (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (t r : Nat) (pub : List Fp) :
    rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad) t r pub 74 false=
      if 5+24*(R.n*R.n)≤r ∧ r<5+24*(R.n*R.n)+32 then
        [[Fp.ofNat R.tau,Fp.ofNat (r-(5+24*(R.n*R.n))),
          Fp.ofNat (priorByte I present (r-(5+24*(R.n*R.n))))]] else [] := by
  rw [row_message]
  change List.replicate (if cells out.rows r kZ=1 then 1 else 0)
    [cells out.rows r tau,cells out.rows r sj,cells out.rows r bpre]=_
  have hl:=generated_length I R present vidV gb fwd out h
  by_cases hr:r<out.rows.size
  · rw [ProcCodecPhysicalRows.active_cells out.rows r hr]
    dsimp only
    simp only [ProcCodecSanityGate.active I R present vidV gb fwd out h r hr]
    by_cases hh:5+24*(R.n*R.n)≤r ∧ r<5+24*(R.n*R.n)+32
    · simp only [ite_eq_left hh]
      change [[Fp.ofNat out.rows[r]![tau]!,Fp.ofNat out.rows[r]![sj]!,Fp.ofNat out.rows[r]![bpre]!]]=_
      have he:r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))):=by omega
      have hcell:=ProcCodecSuffixCells.hash_cell I R present vidV gb fwd out h
        (r-(5+24*(R.n*R.n))) (by omega)
      rw [←he] at hcell
      rw [hcell,hash_payload]
    · simp [hh,show Fp.ofNat 0≠(1:Fp) by decide +kernel]
  · rw [padding_cells out.rows r (by omega)]
    simp [show ¬(5+24*(R.n*R.n)≤r ∧ r<5+24*(R.n*R.n)+32) by omega]

theorem interval {α : Type} (a n total : Nat) (h:a+n≤total) (f : Nat→α) :
    (List.range total).flatMap (fun r=>if a≤r ∧ r<a+n then [f (r-a)] else [])=
    (List.range n).map f := by
  have he:total=(a+n)+(total-(a+n)):=by omega
  rw [he,List.range_add,List.range_add]
  simp only [List.flatMap_append,List.flatMap_map]
  have hpre:(List.range a).flatMap (fun r=>if a≤r ∧ r<a+n then [f (r-a)] else [])=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have :=List.mem_range.mp hr
    rw [ite_eq_right (by omega)]
  have hmid:(List.range n).flatMap (fun r=>if a≤a+r ∧ a+r<a+n then [f (a+r-a)] else [])=
      (List.range n).map f := by
    rw [List.map_eq_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro r hr
    have :=List.mem_range.mp hr
    rw [ite_eq_left (by omega)]
    congr 2
    omega
  have hpost:(List.range (total-(a+n))).flatMap (fun r=>
      if a≤a+n+r ∧ a+n+r<a+n then [f (a+n+r-a)] else [])=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    rw [ite_eq_right (by omega)]
  rw [hpre,hmid,hpost]
  simp

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn:R.n≤64)
    (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace out.rows codecPad) t r pub 74 false)=
    (List.range 32).map (fun j=>[Fp.ofNat R.tau,Fp.ofNat j,Fp.ofNat (priorByte I present j)]) := by
  simp only [row I R present vidV gb fwd out h]
  have hh:5+24*(R.n*R.n)+32≤2^22:=by
    have :=Nat.mul_le_mul hn hn
    omega
  exact interval (5+24*(R.n*R.n)) 32 (2^22) hh
    (fun j=>[Fp.ofNat R.tau,Fp.ofNat j,Fp.ofNat (priorByte I present j)])
end ZkFormal.NearV3.Candidates.ProcCodecSanityTraffic

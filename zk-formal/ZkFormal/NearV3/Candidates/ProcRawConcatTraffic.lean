import ZkFormal.NearV3.Candidates.ProcRawNativeLocal
import ZkFormal.NearV3.Candidates.ProcNativeBlockPresence
import ZkFormal.NearV3.Candidates.ProcInitialLinks
namespace ZkFormal.NearV3.Candidates.ProcRawConcatTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

def messages (row : Nat→Fp) (bus : Nat) (sd : Bool) : List (List Fp) :=
  rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
    ⟨fun _=>22,fun _ _=>row⟩ 0 0 [] bus sd

theorem row_messages (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75) tr t r pub bus sd =
      messages (tr.cell t r) bus sd := by
  simp [messages,ProcPriorRawFrame.interactions,rowTraffic,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k]

theorem zero_messages (bus : Nat) (sd : Bool) : messages (fun _=>0) bus sd=[] := by
  simp [messages,ProcPriorRawFrame.interactions,rowTraffic,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c]

theorem physical (bs : List NativeBlock) (hcap:(rows bs).length≤2^22)
    (t bus : Nat) (pub : List Fp) (sd : Bool) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75) (trace bs) t r pub bus sd)=
      bs.flatMap (fun b=>(blockRows b).flatMap (fun row=>messages row bus sd)) := by
  simp only [row_messages]
  change (List.range (2^22)).flatMap (fun r=>messages (cell bs r) bus sd)=_
  have he:2^22=(rows bs).length+(2^22-(rows bs).length) := by omega
  have hs:=congrArg List.range he
  rw [List.range_add] at hs
  rw [hs,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(rows bs).length)).flatMap
      (fun j=>messages (cell bs ((rows bs).length+j)) bus sd)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [padding bs _ (by omega),zero_messages]
  rw [hz,List.append_nil]
  have hm:=congrArg (fun xs=>xs.flatMap (fun row=>messages row bus sd))
    (map_getD_range (rows bs) (fun _=>0))
  simp only [List.flatMap_map] at hm
  change (List.range (rows bs).length).flatMap (fun r=>messages ((rows bs).getD r (fun _=>0)) bus sd)=_ at hm
  rw [show (List.range (rows bs).length).flatMap (fun r=>messages (cell bs r) bus sd)=
      (rows bs).flatMap (fun row=>messages row bus sd) from hm]
  simp only [rows,List.flatMap_assoc]

theorem count (bs : List NativeBlock) (hcap:(rows bs).length≤2^22)
    (t bus : Nat) (pub msg : List Fp) (sd : Bool) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace bs) t pub bus sd msg=
      (bs.flatMap (fun b=>(blockRows b).flatMap (fun row=>messages row bus sd))).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical bs hcap t bus pub sd)
end ZkFormal.NearV3.Candidates.ProcRawConcatTraffic

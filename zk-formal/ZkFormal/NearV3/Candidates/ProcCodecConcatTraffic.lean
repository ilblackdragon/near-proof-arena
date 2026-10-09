import ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
namespace ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Assembly.CodecDigest

def messages (row : Nat→Fp) (bus : Nat) (sd : Bool) : List (List Fp) :=
  rowTraffic ProcPriorCodecActual.table.interactions ⟨fun _=>22,fun _ _=>row⟩ 0 0 [] bus sd

theorem row_messages (tr : Trace Fp) (t r : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    rowTraffic ProcPriorCodecActual.table.interactions tr t r pub bus sd=messages (tr.cell t r) bus sd := by
  simp [messages,ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,Codec.encG,Codec.shaId,Codec.aLE,Codec.oE,
    ProcPriorCodecActual.idLo,ProcPriorCodecActual.idMid,ProcPriorCodecActual.idHi,
    ZkFormal.Near.Dsl.mid,ZkFormal.Near.Dsl.smul,ZkFormal.Near.Dsl.c,ZkFormal.Near.Dsl.k,Function.comp_def]

theorem zero_messages (bus : Nat) (sd : Bool) : messages (fun _=>0) bus sd=[] := by
  simp [messages,ProcPriorCodecActual.table,ProcPriorCodecActual.interactions,
    ProcPriorCodecParameter.table,Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    ProcPriorCodecActual.presence,ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,
    ProcPriorCodecActual.priorRead,ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    Render.UpsRelay.relay,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    Codec.encG,Codec.shaId,Codec.aLE,Codec.oE]
  all_goals grind

def natMessages (row : Array Nat) (bus : Nat) (sd : Bool) : List (List Fp) :=
  messages (fun c=>Fp.ofNat row[c]!) bus sd

theorem row_lookup (rows : Array (Array Nat)) :
    (List.range rows.size).map (fun r=>rows[r]!)=rows.toList := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range,Array.getElem_toList]
  simp [show i<rows.size by simpa using hj]

theorem physical (rows : Array (Array Nat)) (hcap:rows.size≤2^22)
    (t bus : Nat) (pub : List Fp) (sd : Bool) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace rows codecPad) t r pub bus sd)=
      rows.toList.flatMap (fun row=>natMessages row bus sd) := by
  simp only [row_messages]
  change (List.range (2^22)).flatMap (fun r=>messages (ProcCodecPhysicalPadding.cells rows r) bus sd)=_
  rw [show 2^22=rows.size+(2^22-rows.size) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-rows.size)).flatMap (fun j=>messages (ProcCodecPhysicalPadding.cells rows (rows.size+j)) bus sd)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [ProcCodecPhysicalPadding.padding_cells rows _ (by omega),zero_messages]
  rw [hz,List.append_nil,←row_lookup rows,List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr
  rw [ProcCodecPhysicalRows.active_cells rows r (List.mem_range.mp hr)]
  rfl

theorem blocks (bs : List NativeBlock) (hcap:(nativeBlockRows bs).size≤2^22)
    (t bus : Nat) (pub : List Fp) (sd : Bool) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t r pub bus sd)=
      bs.flatMap (fun b=>b.output.rows.toList.flatMap (fun row=>natMessages row bus sd)) := by
  rw [physical _ hcap]
  simp only [nativeBlockRows,List.toList_toArray,List.flatMap_assoc]
end ZkFormal.NearV3.Candidates.ProcCodecConcatTraffic

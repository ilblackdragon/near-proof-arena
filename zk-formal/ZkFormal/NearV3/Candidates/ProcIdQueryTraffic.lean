import ZkFormal.NearV3.Candidates.ProcRecordIdTraffic
import ZkFormal.NearV3.Candidates.ProcPriorIdTrace
namespace ZkFormal.NearV3.Candidates.ProcIdQueryTraffic
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def messages (req : Bool) (c : Nat→Fp) : List (List Fp) :=
  rowTraffic (ProcPriorIdTable.interactions 70 71 72 69)
    ⟨fun _=>22,fun _ _=>c⟩ 0 0 [] (if req then 71 else 72) (!req)
def events (req : Bool) (tau : Nat) (e : ProcPriorIds.Event) : List (List Fp) :=
  if e.isPublic then [] else [ProcRecordIdTraffic.packet req tau e]

theorem row (req : Bool) (c : Nat→Fp) : messages req c=
    List.replicate (if c 0*(1-c 6)=1 then 1 else 0)
      (if req then [c 1,c 5,c 2,c 3,c 4] else [c 1,c 5,c 7,c 8]) := by
  cases req
  all_goals simp [messages,ProcPriorIdTable.interactions,rowTraffic,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
    ProcPriorIdTable.notE,ProcPriorIdTable.act,ProcPriorIdTable.isPublic,
    ProcPriorIdTable.tau,ProcPriorIdTable.ordinal,ProcPriorIdTable.keyLo,
    ProcPriorIdTable.keyMid,ProcPriorIdTable.keyHi,ProcPriorIdTable.found,ProcPriorIdTable.index]
  all_goals first | rfl | grind

theorem generated (req : Bool) (ids : List Nat) (rs : List LinkAllowance)
    (a : ProcPriorIdRows.Row) (ha:a∈ProcPriorIdRows.rows ids rs)
    (next : Option ProcPriorIdRows.Row) (tau : Nat) :
    messages req (ProcPriorIdCells.cells a next tau)=events req tau a.event := by
  rw [row]
  cases hq:a.event.isPublic
  · have hr:=ProcPriorIdRows.query_row ids rs a ha hq
    cases req <;> simp [ProcPriorIdCells.cells,ProcPriorCells.bit,events,hq,hr,
      ProcRecordIdTraffic.packet,ProcRecordIdTraffic.request,ProcRecordIdTraffic.result]
    all_goals first | rfl | decide +kernel
  · cases req <;> simp [ProcPriorIdCells.cells,ProcPriorCells.bit,events,hq]
    all_goals first | rfl | decide +kernel

theorem native_perm (req : Bool) (tau : Nat) (ids : List Nat) (rs : List LinkAllowance) :
    ((ProcPriorIdRows.rows ids rs).flatMap (fun a=>events req tau a.event)).Perm
      ((ProcPriorIds.requestEvents ids rs).map (ProcRecordIdTraffic.packet req tau)) := by
  have hr:=ProcPriorIdRows.rowsFrom_events ⟨none,ProcPriorIdCarry.zero⟩ (ProcPriorIds.events ids rs)
  have he:=congrArg (fun es=>es.flatMap (events req tau)) hr
  simp only [List.flatMap_map] at he
  change (ProcPriorIdRows.rows ids rs).flatMap (fun a=>events req tau a.event)=_ at he
  rw [he]
  have hp:=List.Perm.flatMap_right (events req tau) (ProcPriorIds.events_perm ids rs)
  have hb:(ProcPriorIds.publicEvents ids++ProcPriorIds.requestEvents ids rs).flatMap (events req tau)=
      (ProcPriorIds.requestEvents ids rs).map (ProcRecordIdTraffic.packet req tau) := by
    simp [ProcPriorIds.publicEvents,ProcPriorIds.requestEvents,events,
      List.flatMap_append,List.flatMap_map,List.flatMap_assoc,List.map_flatMap]
  rw [hb] at hp
  exact hp
end ZkFormal.NearV3.Candidates.ProcIdQueryTraffic

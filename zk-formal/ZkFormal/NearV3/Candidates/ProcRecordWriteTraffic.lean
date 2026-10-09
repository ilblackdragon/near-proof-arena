import ZkFormal.NearV3.Candidates.ProcRecordAllTraffic
import ZkFormal.NearV3.Candidates.ProcPriorRecordSemantics
namespace ZkFormal.NearV3.Candidates.ProcRecordWriteTraffic
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest ProcRecordAllTraffic

def message (tau : Nat) (e : ProcPriorEvents.Event) : List Fp :=
  [Fp.ofNat tau,Fp.ofNat e.link,Fp.ofNat e.stamp,Fp.ofNat e.lo,ProcPriorCells.bit e.hi]

theorem row (c : Nat→Fp) : messages c 67 true=
    List.replicate (if c 22=1 then 1 else 0) [c 1,c 17*c 3+c 19,c 2,c 13,c 20] := by
  simp [messages,ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,
    Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ProcPriorRecordTable.link,
    ProcPriorRecordTable.writeGate,ProcPriorRecordTable.tau,ProcPriorRecordTable.record,
    ProcPriorRecordTable.senderIndex,ProcPriorRecordTable.receiverIndex,ProcPriorRecordTable.shards,
    ProcPriorRecordTable.lo,ProcPriorRecordTable.big]

theorem header (ids : List Nat) (tau : Nat) : messages (ProcPriorRecordCells.header ids tau) 67 true=[] := by
  rw [row]
  rfl

theorem record (ids : List Nat) (tau j : Nat) (r : LinkAllowance) :
    (ProcPriorRecordRows.rowsFor r j).flatMap
      (fun x=>messages (ProcPriorRecordCells.cell ids tau x) 67 true)=
    (((ProcPriorLookup.target ids r).map fun l=>ProcPriorEvents.Event.mk l j false
      (ProcPriorSummary.low r.allowance) (ProcPriorSummary.big r.allowance)).toList).map (message tau) := by
  have hc (s t : Nat) : Fp.ofNat s*Fp.ofNat ids.length+Fp.ofNat t=Fp.ofNat (s*ids.length+t) := by
    change (s:Fp)*(ids.length:Fp)+(t:Fp)=((s*ids.length+t:Nat):Fp)
    grind
  cases hs:indexOf ids r.sender <;> cases ht:indexOf ids r.receiver
  all_goals simp [ProcPriorRecordRows.rowsFor,row,ProcPriorRecordCells.cell,
    ProcPriorCells.bit,ProcPriorRecordRows.value,ProcPriorLookup.target,hs,ht,
    ProcPriorRecordLimbs.big_exact,message,ProcPriorSummary.low,ProcPriorIdLimbs.lo,hc]
  all_goals try rfl
  all_goals
    have hbig:=ProcPriorRecordLimbs.big_exact r.allowance
    cases hb:ProcPriorSummary.big r.allowance <;> simp_all
theorem indexed_zip {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun j=>(xs.getD j d,j))=xs.zipIdx := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have h:j<xs.length:=by simpa using hj
    simp [List.getElem_map,List.getElem_range,List.getElem_zipIdx,List.getD,
      List.getElem?_eq_getElem h]

theorem option_flatMap {α β : Type} (xs : List α) (f : α→Option β) :
    xs.flatMap (fun x=>(f x).toList)=xs.filterMap f := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>cases hx:f x <;> simp [hx,ih]

theorem block (ids : List Nat) (b : NativeBlock) :
    (ProcRecordConcatTraffic.blockRows ids b).flatMap (fun row=>messages row 67 true)=
      (ProcPriorEvents.writeEvents ids b.old.links).map (message b.run.tau) := by
  simp only [ProcRecordConcatTraffic.blockRows,List.flatMap_cons,header,List.nil_append,
    List.flatMap_assoc,List.flatMap_map,record]
  rw [←List.map_flatMap]
  apply congrArg (List.map (message b.run.tau))
  have hz:=congrArg (fun xs:List (NearSpec.Bandwidth.LinkAllowance×Nat)=>xs.flatMap
      (fun (r,j)=>((ProcPriorLookup.target ids r).map fun l=>ProcPriorEvents.Event.mk l j false
        (ProcPriorSummary.low r.allowance) (ProcPriorSummary.big r.allowance)).toList))
    (indexed_zip b.old.links ⟨0,0,0⟩)
  simp only [List.flatMap_map] at hz
  rw [hz,option_flatMap]
  rfl

theorem physical (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcRawConcatGeometry.rows bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace ids bs) t r pub 67 true)=
    bs.flatMap (fun b=>(ProcPriorEvents.writeEvents (ids b) b.old.links).map (message b.run.tau)) := by
  rw [ProcRecordAllTraffic.physical ids bs (Nat.le_trans (ProcRecordConcatTraffic.capacity ids bs) hcap)]
  simp only [block]
end ZkFormal.NearV3.Candidates.ProcRecordWriteTraffic

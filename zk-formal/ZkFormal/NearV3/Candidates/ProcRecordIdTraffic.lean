import ZkFormal.NearV3.Candidates.ProcRecordWriteTraffic
namespace ZkFormal.NearV3.Candidates.ProcRecordIdTraffic
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest ProcRecordAllTraffic

def request (tau : Nat) (e : ProcPriorIds.Event) : List Fp :=
  [Fp.ofNat tau,Fp.ofNat e.ordinal,Fp.ofNat (ProcPriorIdLimbs.lo e.key),
    Fp.ofNat (ProcPriorIdLimbs.mid e.key),Fp.ofNat (ProcPriorIdLimbs.hi e.key)]
def result (tau : Nat) (e : ProcPriorIds.Event) : List Fp :=
  [Fp.ofNat tau,Fp.ofNat e.ordinal,ProcPriorCells.bit e.result.isSome,Fp.ofNat (e.result.getD 0)]

theorem request_row (c : Nat→Fp) : messages c 71 true=
    List.replicate (if c 9*(c 4+c 5)=1 then 1 else 0)
      [c 1,2*c 2+c 5,c 13,c 14,c 15] := by
  simp [messages,ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,
    Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    ProcPriorRecordTable.queryGate,ProcPriorRecordTable.queryOrdinal,
    ProcPriorRecordTable.tau,ProcPriorRecordTable.record,ProcPriorRecordTable.sender,
    ProcPriorRecordTable.receiver,ProcPriorRecordTable.topLimb,ProcPriorRecordTable.lo,
    ProcPriorRecordTable.mid,ProcPriorRecordTable.hi]
  first | rfl | exact Or.inr rfl

theorem result_row (c : Nat→Fp) : messages c 72 false=
    List.replicate (if c 9*c 4=1 then 1 else 0) [c 1,2*c 2+c 5,c 16,c 17] ++
    List.replicate (if c 9*c 5=1 then 1 else 0) [c 1,2*c 2+c 5,c 18,c 19] := by
  simp [messages,ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,
    Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    ProcPriorRecordTable.queryOrdinal,ProcPriorRecordTable.tau,ProcPriorRecordTable.record,
    ProcPriorRecordTable.sender,ProcPriorRecordTable.receiver,ProcPriorRecordTable.topLimb,
    ProcPriorRecordTable.senderFound,ProcPriorRecordTable.senderIndex,
    ProcPriorRecordTable.receiverFound,ProcPriorRecordTable.receiverIndex]
  first | rfl | exact Or.inr rfl

theorem record (ids : List Nat) (tau j : Nat) (r : LinkAllowance) :
    (ProcPriorRecordRows.rowsFor r j).flatMap
      (fun x=>messages (ProcPriorRecordCells.cell ids tau x) 71 true)=
      [request tau ⟨r.sender,false,2*j,indexOf ids r.sender⟩,
       request tau ⟨r.receiver,false,2*j+1,indexOf ids r.receiver⟩] ∧
    (ProcPriorRecordRows.rowsFor r j).flatMap
      (fun x=>messages (ProcPriorRecordCells.cell ids tau x) 72 false)=
      [result tau ⟨r.sender,false,2*j,indexOf ids r.sender⟩,
       result tau ⟨r.receiver,false,2*j+1,indexOf ids r.receiver⟩] := by
  have ha (x:Fp):x+0=x:=by grind
  have hz (x:Fp):0+x=x:=by grind
  have h0:(2:Fp)*Fp.ofNat j=Fp.ofNat (2*j):=by change (2:Fp)*(j:Fp)=((2*j:Nat):Fp); grind
  have h1:Fp.ofNat (2*j)+1=Fp.ofNat (2*j+1):=by change ((2*j:Nat):Fp)+1=((2*j+1:Nat):Fp); grind
  constructor
  all_goals simp [ProcPriorRecordRows.rowsFor,request_row,result_row,ProcPriorRecordCells.cell,
    ProcPriorCells.bit,ProcPriorRecordRows.value,request,result,ha,hz,h0,h1]
  all_goals rfl
def packet (req : Bool) := if req then request else result

theorem record_mode (req : Bool) (ids : List Nat) (tau j : Nat) (r : LinkAllowance) :
    (ProcPriorRecordRows.rowsFor r j).flatMap (fun x=>messages
      (ProcPriorRecordCells.cell ids tau x) (if req then 71 else 72) req)=
    [packet req tau ⟨r.sender,false,2*j,indexOf ids r.sender⟩,
     packet req tau ⟨r.receiver,false,2*j+1,indexOf ids r.receiver⟩] := by
  cases req
  · exact (record ids tau j r).2
  · exact (record ids tau j r).1

theorem header (req : Bool) (ids : List Nat) (tau : Nat) :
    messages (ProcPriorRecordCells.header ids tau) (if req then 71 else 72) req=[] := by
  cases req
  · change messages _ 72 false=[]
    rw [result_row]; rfl
  · change messages _ 71 true=[]
    rw [request_row]; rfl

theorem block (req : Bool) (ids : List Nat) (b : NativeBlock) :
    (ProcRecordConcatTraffic.blockRows ids b).flatMap (fun row=>messages row (if req then 71 else 72) req)=
      (ProcPriorIds.requestEvents ids b.old.links).map (packet req b.run.tau) := by
  simp only [ProcRecordConcatTraffic.blockRows,List.flatMap_cons,header,List.nil_append,
    List.flatMap_assoc,List.flatMap_map,record_mode]
  have hz:=congrArg (fun xs:List (LinkAllowance×Nat)=>xs.flatMap (fun (r,j)=>
      [packet req b.run.tau ⟨r.sender,false,2*j,indexOf ids r.sender⟩,
       packet req b.run.tau ⟨r.receiver,false,2*j+1,indexOf ids r.receiver⟩]))
    (ProcRecordWriteTraffic.indexed_zip b.old.links ⟨0,0,0⟩)
  simp only [List.flatMap_map] at hz
  rw [hz]
  simp only [ProcPriorIds.requestEvents,List.map_flatMap,List.map_cons,List.map_nil]

theorem physical (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcRawConcatGeometry.rows bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace ids bs) t r pub (if req then 71 else 72) req)=
    bs.flatMap (fun b=>(ProcPriorIds.requestEvents (ids b) b.old.links).map (packet req b.run.tau)) := by
  rw [ProcRecordAllTraffic.physical ids bs (Nat.le_trans (ProcRecordConcatTraffic.capacity ids bs) hcap)]
  simp only [block]
end ZkFormal.NearV3.Candidates.ProcRecordIdTraffic

import ZkFormal.NearV3.Candidates.ProcRawRecordPhysical
namespace ZkFormal.NearV3.Candidates.ProcRecordConcatTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest

def blockRows (ids : List Nat) (b : NativeBlock) : List (Nat→Fp) :=
  ProcPriorRecordCells.header ids b.run.tau ::
    (List.range b.old.links.length).flatMap (fun j=>
      (ProcPriorRecordRows.rowsFor (b.old.links.getD j ⟨0,0,0⟩) j).map
        (ProcPriorRecordCells.cell ids b.run.tau))
def rows (ids : NativeBlock→List Nat) (bs : List NativeBlock) := bs.flatMap (fun b=>blockRows (ids b) b)
def trace (ids : NativeBlock→List Nat) (bs : List NativeBlock) : Trace Fp :=
  ⟨fun _=>22,fun _ r=>(rows ids bs).getD r (fun _=>0)⟩

theorem row_messages (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorRecordTable.interactions 75 71 72 67 76) tr t r pub 75 false=
      ProcPriorRecordTraffic.messages (tr.cell t r) := by
  simp [ProcPriorRecordTraffic.messages,ProcPriorRecordTable.interactions,rowTraffic,
    Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
    ProcPriorRecordTable.words,ProcPriorRecordTable.offset]

theorem zero_messages : ProcPriorRecordTraffic.messages (fun _=>0)=[] := by
  rw [ProcPriorRecordTraffic.row]
  decide +kernel

theorem block_length (ids : List Nat) (b : NativeBlock) :
    (blockRows ids b).length=1+9*b.old.links.length := by
  simp [blockRows,List.length_flatMap,ProcPriorRecordRows.rowsFor_length,
    List.map_const',List.sum_replicate_nat,Nat.mul_comm,Nat.add_comm]

theorem capacity (ids : NativeBlock→List Nat) (bs : List NativeBlock) :
    (rows ids bs).length≤(ProcRawConcatGeometry.rows bs).length := by
  induction bs with
  | nil => simp [rows,ProcRawConcatGeometry.rows]
  | cons b bs ih =>
    simp only [rows,ProcRawConcatGeometry.rows,List.flatMap_cons,List.length_append] at *
    rw [block_length,ProcRawConcatGeometry.block_length]
    unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length
    omega

theorem physical (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(rows ids bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRecordTable.interactions 75 71 72 67 76) (trace ids bs) t r pub 75 false)=
      bs.flatMap (fun b=>(List.range b.old.links.length).flatMap (fun j=>
        (ProcPriorRecordRows.rowsFor (b.old.links.getD j ⟨0,0,0⟩) j).flatMap
          (fun x=>ProcPriorRecordTraffic.messages (ProcPriorRecordCells.cell (ids b) b.run.tau x)))) := by
  simp only [row_messages]
  change (List.range (2^22)).flatMap (fun r=>ProcPriorRecordTraffic.messages ((rows ids bs).getD r (fun _=>0)))=_
  have he:2^22=(rows ids bs).length+(2^22-(rows ids bs).length) := by omega
  have hs:=congrArg List.range he
  rw [List.range_add] at hs
  rw [hs,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(rows ids bs).length)).flatMap
      (fun j=>ProcPriorRecordTraffic.messages ((rows ids bs).getD ((rows ids bs).length+j) (fun _=>0)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    have hn:(rows ids bs)[(rows ids bs).length+j]?=none:=List.getElem?_eq_none_iff.mpr (by omega)
    simp only [List.getD,hn,Option.getD_none,zero_messages]
  rw [hz,List.append_nil]
  have hm:=congrArg (fun xs=>xs.flatMap ProcPriorRecordTraffic.messages)
    (map_getD_range (rows ids bs) (fun _=>0))
  simp only [List.flatMap_map] at hm
  rw [hm]
  simp only [rows,List.flatMap_assoc,blockRows,List.flatMap_cons,ProcPriorRecordTraffic.header,
    List.nil_append,List.flatMap_map]

theorem balance (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hb:∀b∈bs,b.Valid) (hcap:(ProcRawConcatGeometry.rows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawConcatGeometry.trace bs) t pub 75 true msg=
    tableBusCount (ProcPriorRecordTable.interactions 75 71 72 67 76)
      (trace ids bs) t pub 75 false msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=((List.range (2^22)).flatMap _).count msg
  rw [ProcRawRecordPhysical.physical bs hb ids hcap,
    physical ids bs (Nat.le_trans (capacity ids bs) hcap)]
end ZkFormal.NearV3.Candidates.ProcRecordConcatTraffic

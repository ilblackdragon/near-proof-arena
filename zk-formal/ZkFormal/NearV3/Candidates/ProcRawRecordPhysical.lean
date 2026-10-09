import ZkFormal.NearV3.Candidates.ProcNativeRecordBalance
namespace ZkFormal.NearV3.Candidates.ProcRawRecordPhysical
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

theorem range_groups {α : Type} (n k : Nat) (f : Nat→List α) :
    (List.range (k*n)).flatMap f=
    (List.range n).flatMap (fun j=>(List.range k).flatMap (fun g=>f (k*j+g))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,List.range_add,List.flatMap_append,List.flatMap_map,ih,List.range_succ]
    simp

theorem header_silent (b : NativeBlock) (g : Nat) (hg:g<5) :
    ProcRawConcatTraffic.messages (blockCell b g) 75 true=[] := by
  change rowTraffic _ _ _ _ _ _ _=[]
  rw [ProcRawRecordTraffic.row]
  simp [blockCell,ProcRawConcatBoundary.stamp,ProcPriorRawGen.trace,
    ProcPriorRawSlots.header _ _ hg,ProcPriorRawGen.cells,ProcPriorRawGen.isRecord,
    ProcPriorCells.bit,ProcPriorRawFrame.rec,ProcPriorRawFrame.tau]

theorem hash_silent (b : NativeBlock) (g : Nat) (hg:g<32) :
    ProcRawConcatTraffic.messages (blockCell b (5+24*b.old.links.length+g)) 75 true=[] := by
  change rowTraffic _ _ _ _ _ _ _=[]
  rw [ProcRawRecordTraffic.row]
  simp [blockCell,ProcRawConcatBoundary.stamp,ProcPriorRawGen.trace,
    ProcPriorRawSlots.hash _ _ hg,ProcPriorRawGen.cells,ProcPriorRawGen.isRecord,
    ProcPriorCells.bit,ProcPriorRawFrame.rec,ProcPriorRawFrame.tau]

theorem block (b : NativeBlock) :
    (blockRows b).flatMap (fun row=>ProcRawConcatTraffic.messages row 75 true)=
    (List.range b.old.links.length).flatMap (fun j=>(List.range 24).flatMap
      (fun g=>ProcRawConcatTraffic.messages (blockCell b (5+24*j+g)) 75 true)) := by
  simp only [blockRows,List.flatMap_map]
  rw [show blockLength b=5+(24*b.old.links.length+32) by
    unfold blockLength ProcPriorRawSlots.length; omega]
  rw [List.range_add,List.flatMap_append,List.flatMap_map]
  have hh:(List.range 5).flatMap (fun g=>ProcRawConcatTraffic.messages (blockCell b g) 75 true)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro g hg
    exact header_silent b g (List.mem_range.mp hg)
  rw [hh,List.nil_append,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range 32).flatMap (fun g=>ProcRawConcatTraffic.messages
      (blockCell b (5+(24*b.old.links.length+g))) 75 true)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro g hg
    simpa only [Nat.add_assoc] using hash_silent b g (List.mem_range.mp hg)
  rw [hz,List.append_nil,range_groups]
  simp only [Nat.add_assoc]

theorem physical (bs : List NativeBlock) (hb:∀b∈bs,b.Valid)
    (ids : NativeBlock→List Nat) (hcap:(rows bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace bs) t r pub 75 true)=
    bs.flatMap (fun b=>(List.range b.old.links.length).flatMap (fun j=>
      (ProcPriorRecordRows.rowsFor (b.old.links.getD j ⟨0,0,0⟩) j).flatMap
        (fun x=>ProcPriorRecordTraffic.messages (ProcPriorRecordCells.cell (ids b) b.run.tau x)))) := by
  rw [ProcRawConcatTraffic.physical bs hcap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b h
  rw [block]
  exact ProcNativeRecordBalance.indexed b (hb b h) (ids b)
end ZkFormal.NearV3.Candidates.ProcRawRecordPhysical

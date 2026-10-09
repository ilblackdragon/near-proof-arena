import ZkFormal.NearV3.Candidates.ProcIdTaggedTraffic
import ZkFormal.NearV3.Candidates.ProcRecordWriteTraffic
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedPublic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest

def messages (c : Nat→Fp) := rowTraffic (ProcPriorIdTable.interactions 70 71 72 69)
  ⟨fun _=>22,fun _ _=>c⟩ 0 0 [] 70 false
def events (tau : Nat) (e : ProcPriorIds.Event) :=
  if e.isPublic then [ProcRecordIdTraffic.request tau e] else []

theorem row (c : Nat→Fp) : messages c=List.replicate (if c 0*c 6=1 then 1 else 0)
    [c 1,c 5,c 2,c 3,c 4] := by
  simp [messages,ProcPriorIdTable.interactions,rowTraffic,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
    ZkFormal.Chacha.Table.E.c,ProcPriorIdTable.act,ProcPriorIdTable.isPublic,
    ProcPriorIdTable.tau,ProcPriorIdTable.ordinal,ProcPriorIdTable.keyLo,
    ProcPriorIdTable.keyMid,ProcPriorIdTable.keyHi]

theorem row_messages (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorIdTable.interactions 70 71 72 69) tr t r pub 70 false=messages (tr.cell t r) := by
  simp [messages,ProcPriorIdTable.interactions,rowTraffic,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c]

theorem zero_messages : messages (fun _=>0)=[] := by
  rw [row]; decide +kernel

theorem generated (a : ProcIdTaggedCells.Tagged) (next : Option ProcIdTaggedCells.Tagged) :
    messages (ProcIdTaggedCells.cells a next)=events a.1 a.2.event := by
  rw [row]
  have hd : ∀c,c<10→ProcIdTaggedCells.cells a next c=ProcPriorIdCells.cells a.2 none a.1 c := by
    intro c hc
    rw [ProcIdTaggedCells.data a next c hc]
    exact ProcIdTaggedCells.data_next _ _ _ _ _ hc
  rw [hd 0 (by omega),hd 6 (by omega),hd 1 (by omega),hd 5 (by omega),
    hd 2 (by omega),hd 3 (by omega),hd 4 (by omega)]
  cases h:a.2.event.isPublic <;>
    simp [events,h,ProcPriorIdCells.cells,ProcPriorCells.bit,ProcRecordIdTraffic.request]
  all_goals first | rfl | decide +kernel

theorem physical (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcIdConcatTraffic.rows ids bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)) t r pub
      70 false)=
    bs.flatMap (fun b=>(ProcPriorIdRows.rows (ids b) b.old.links).flatMap
      (fun a=>events b.run.tau a.event)) := by
  let xs:=ProcIdTaggedRows.rows ids bs
  have hc:xs.length≤2^22:=by simpa [xs,ProcIdNativeLocal.length_eq] using hcap
  simp only [row_messages]
  change (List.range (2^22)).flatMap (fun r=>messages (ProcIdTaggedTrace.cell xs r))=_
  have he:2^22=xs.length+(2^22-xs.length):=by omega
  have hs:=congrArg List.range he
  rw [List.range_add] at hs
  rw [hs,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-xs.length)).flatMap
      (fun j=>messages (ProcIdTaggedTrace.cell xs (xs.length+j)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [ProcIdTaggedTrace.padding xs _ (by omega),zero_messages]
  rw [hz,List.append_nil]
  let d:ProcIdTaggedCells.Tagged:=(0,⟨⟨0,false,0,none⟩,none⟩)
  have hm:=congrArg (fun rs=>rs.flatMap (fun a=>events a.1 a.2.event)) (map_getD_range xs d)
  simp only [List.flatMap_map] at hm
  have hp:(List.range xs.length).flatMap (fun r=>messages (ProcIdTaggedTrace.cell xs r))=
      xs.flatMap (fun a=>events a.1 a.2.event) := by
    rw [←hm]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro j hj
    have h:j<xs.length:=List.mem_range.mp hj
    have hg:xs[j]?=some (xs.getD j d):=by simp [List.getD,List.getElem?_eq_getElem h]
    have hmem:xs.getD j d∈xs:=by
      simp only [List.getD,List.getElem?_eq_getElem h,Option.getD_some]
      exact List.getElem_mem h
    rw [ProcIdTaggedTrace.cell_some xs j _ hg]
    exact generated _ _
  rw [hp]
  simp only [xs,ProcIdTaggedRows.rows,ProcIdTaggedRows.block,List.flatMap_assoc,List.flatMap_map]

def packets (tau : Nat) (ids : List Nat) : List (List Fp) :=
  (List.range ids.length).map (fun j=>[Fp.ofNat tau,Fp.ofNat j,
    Fp.ofNat (ProcPriorIdLimbs.lo (ids.getD j 0)),Fp.ofNat (ProcPriorIdLimbs.mid (ids.getD j 0)),
    Fp.ofNat (ProcPriorIdLimbs.hi (ids.getD j 0))])

theorem native_perm (tau : Nat) (ids : List Nat) (rs : List NearSpec.Bandwidth.LinkAllowance) :
    ((ProcPriorIdRows.rows ids rs).flatMap (fun a=>events tau a.event)).Perm (packets tau ids) := by
  have hr:=ProcPriorIdRows.rowsFrom_events ⟨none,ProcPriorIdCarry.zero⟩ (ProcPriorIds.events ids rs)
  have he:=congrArg (fun es=>es.flatMap (events tau)) hr
  simp only [List.flatMap_map] at he
  change (ProcPriorIdRows.rows ids rs).flatMap (fun a=>events tau a.event)=_ at he
  rw [he]
  have hp:=List.Perm.flatMap_right (events tau) (ProcPriorIds.events_perm ids rs)
  have hb:(ProcPriorIds.publicEvents ids++ProcPriorIds.requestEvents ids rs).flatMap (events tau)=
      packets tau ids := by
    simp only [ProcPriorIds.publicEvents,ProcPriorIds.requestEvents,List.flatMap_append,
      List.flatMap_map,List.flatMap_assoc]
    simp only [events,ite_true,ite_false,List.flatMap_cons,List.flatMap_nil,
      List.nil_append,List.append_nil,List.flatMap_eq_nil_iff,implies_true]
    rw [←ProcRecordWriteTraffic.indexed_zip ids 0]
    simp [packets,ProcRecordIdTraffic.request,List.flatMap_map]
    generalize List.range ids.length=js
    induction js with
    | nil=>rfl
    | cons j js ih=>simp only [List.flatMap_cons,List.map_cons,List.singleton_append,ih]
  rw [hb] at hp
  exact hp

theorem count (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcIdConcatTraffic.rows ids bs).length≤2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)) t pub 70 false msg=
    (bs.flatMap (fun b=>packets b.run.tau (ids b))).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [physical ids bs hcap]
  apply List.Perm.count_eq
  clear hcap
  induction bs with
  | nil=>exact List.Perm.refl _
  | cons b bs ih=>exact (native_perm b.run.tau (ids b) b.old.links).append ih

end ZkFormal.NearV3.Candidates.ProcIdTaggedPublic

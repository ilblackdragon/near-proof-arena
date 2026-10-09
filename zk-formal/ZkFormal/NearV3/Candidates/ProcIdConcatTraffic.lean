import ZkFormal.NearV3.Candidates.ProcIdQueryTraffic
namespace ZkFormal.NearV3.Candidates.ProcIdConcatTraffic
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcIdQueryTraffic

def blockRows (ids : List Nat) (b : NativeBlock) : List (Nat→Fp) :=
  let xs:=ProcPriorIdRows.rows ids b.old.links
  (List.range xs.length).map (ProcPriorIdTrace.cells xs b.run.tau)
def rows (ids : NativeBlock→List Nat) (bs : List NativeBlock) := bs.flatMap (fun b=>blockRows (ids b) b)
def trace (ids : NativeBlock→List Nat) (bs : List NativeBlock) : Trace Fp :=
  ⟨fun _=>22,fun _ r=>(rows ids bs).getD r (fun _=>0)⟩

theorem row_messages (req : Bool) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic (ProcPriorIdTable.interactions 70 71 72 69) tr t r pub
      (if req then 71 else 72) (!req)=messages req (tr.cell t r) := by
  cases req
  all_goals simp [messages,ProcPriorIdTable.interactions,rowTraffic,Interaction.multNat,
    Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ProcPriorIdTable.notE]

theorem zero_messages (req : Bool) : messages req (fun _=>0)=[] := by
  rw [ProcIdQueryTraffic.row]
  cases req <;> decide +kernel

theorem block (req : Bool) (ids : List Nat) (b : NativeBlock) :
    (blockRows ids b).flatMap (messages req)=
      (ProcPriorIdRows.rows ids b.old.links).flatMap (fun a=>events req b.run.tau a.event) := by
  let xs:=ProcPriorIdRows.rows ids b.old.links
  let d:ProcPriorIdRows.Row:=⟨⟨0,false,0,none⟩,none⟩
  have hm:=congrArg (fun rs=>rs.flatMap (fun a=>events req b.run.tau a.event)) (map_getD_range xs d)
  simp only [List.flatMap_map] at hm
  unfold blockRows
  simp only [List.flatMap_map]
  rw [←hm]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  have h:j<xs.length:=List.mem_range.mp hj
  have hg:xs[j]?=some (xs.getD j d):=by simp [List.getD,List.getElem?_eq_getElem h]
  have hmem:xs.getD j d∈xs:=by simp only [List.getD,List.getElem?_eq_getElem h,Option.getD_some]; exact List.getElem_mem h
  rw [ProcPriorIdTrace.cells_some xs b.run.tau j _ hg]
  exact generated req ids b.old.links _ hmem _ b.run.tau

theorem physical (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(rows ids bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorIdTable.interactions 70 71 72 69) (trace ids bs) t r pub
      (if req then 71 else 72) (!req))=
    bs.flatMap (fun b=>(ProcPriorIdRows.rows (ids b) b.old.links).flatMap (fun a=>events req b.run.tau a.event)) := by
  simp only [row_messages]
  change (List.range (2^22)).flatMap (fun r=>messages req ((rows ids bs).getD r (fun _=>0)))=_
  have he:2^22=(rows ids bs).length+(2^22-(rows ids bs).length):=by omega
  have hs:=congrArg List.range he
  rw [List.range_add] at hs
  rw [hs,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(rows ids bs).length)).flatMap
      (fun j=>messages req ((rows ids bs).getD ((rows ids bs).length+j) (fun _=>0)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    have hn:(rows ids bs)[(rows ids bs).length+j]?=none:=List.getElem?_eq_none_iff.mpr (by omega)
    simp only [List.getD,hn,Option.getD_none,zero_messages]
  rw [hz,List.append_nil]
  have hm:=congrArg (fun xs=>xs.flatMap (messages req)) (map_getD_range (rows ids bs) (fun _=>0))
  simp only [List.flatMap_map] at hm
  rw [hm]
  simp only [rows,List.flatMap_assoc,block]

theorem count (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(rows ids bs).length≤2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69) (trace ids bs) t pub
      (if req then 71 else 72) (!req) msg=
    (bs.flatMap (fun b=>(ProcPriorIds.requestEvents (ids b) b.old.links).map
      (ProcRecordIdTraffic.packet req b.run.tau))).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [physical req ids bs hcap]
  have hp: (bs.flatMap (fun b=>(ProcPriorIdRows.rows (ids b) b.old.links).flatMap (fun a=>events req b.run.tau a.event))).Perm
      (bs.flatMap (fun b=>(ProcPriorIds.requestEvents (ids b) b.old.links).map (ProcRecordIdTraffic.packet req b.run.tau))) := by
    clear hcap
    induction bs with
    | nil=>exact List.Perm.refl _
    | cons b bs ih=>exact (native_perm req b.run.tau (ids b) b.old.links).append ih
  exact hp.count_eq msg
end ZkFormal.NearV3.Candidates.ProcIdConcatTraffic

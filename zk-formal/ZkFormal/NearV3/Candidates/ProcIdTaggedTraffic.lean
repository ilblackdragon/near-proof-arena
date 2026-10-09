import ZkFormal.NearV3.Candidates.ProcIdNativeLocal
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcIdQueryTraffic

theorem message_data (req : Bool) (a : ProcIdTaggedCells.Tagged)
    (next : Option ProcIdTaggedCells.Tagged) :
    messages req (ProcIdTaggedCells.cells a next)=
      messages req (ProcPriorIdCells.cells a.2 none a.1) := by
  simp only [row]
  have hd : ∀c,c<10→ProcIdTaggedCells.cells a next c=ProcPriorIdCells.cells a.2 none a.1 c := by
    intro c hc
    rw [ProcIdTaggedCells.data a next c hc]
    exact ProcIdTaggedCells.data_next _ _ _ _ _ hc
  rw [hd 0 (by omega),hd 6 (by omega),hd 1 (by omega),hd 5 (by omega),
    hd 2 (by omega),hd 3 (by omega),hd 4 (by omega),hd 7 (by omega),hd 8 (by omega)]

theorem generated (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (a : ProcIdTaggedCells.Tagged) (ha:a∈ProcIdTaggedRows.rows ids bs)
    (next : Option ProcIdTaggedCells.Tagged) :
    messages req (ProcIdTaggedCells.cells a next)=events req a.1 a.2.event := by
  rw [message_data]
  obtain ⟨b,hb,r,hr,rfl⟩:=ProcIdTaggedRows.mem_origin ids bs a ha
  exact ProcIdQueryTraffic.generated req (ids b) b.old.links r hr none b.run.tau

theorem physical (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcIdConcatTraffic.rows ids bs).length≤2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)) t r pub
      (if req then 71 else 72) (!req))=
    bs.flatMap (fun b=>(ProcPriorIdRows.rows (ids b) b.old.links).flatMap
      (fun a=>events req b.run.tau a.event)) := by
  let xs:=ProcIdTaggedRows.rows ids bs
  have hc:xs.length≤2^22:=by simpa [xs,ProcIdNativeLocal.length_eq] using hcap
  simp only [ProcIdConcatTraffic.row_messages]
  change (List.range (2^22)).flatMap (fun r=>messages req (ProcIdTaggedTrace.cell xs r))=_
  have he:2^22=xs.length+(2^22-xs.length):=by omega
  have hs:=congrArg List.range he
  rw [List.range_add] at hs
  rw [hs,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-xs.length)).flatMap
      (fun j=>messages req (ProcIdTaggedTrace.cell xs (xs.length+j)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [ProcIdTaggedTrace.padding xs _ (by omega),ProcIdConcatTraffic.zero_messages]
  rw [hz,List.append_nil]
  let d:ProcIdTaggedCells.Tagged:=(0,⟨⟨0,false,0,none⟩,none⟩)
  have hm:=congrArg (fun rs=>rs.flatMap (fun a=>events req a.1 a.2.event)) (map_getD_range xs d)
  simp only [List.flatMap_map] at hm
  have hp:(List.range xs.length).flatMap (fun r=>messages req (ProcIdTaggedTrace.cell xs r))=
      xs.flatMap (fun a=>events req a.1 a.2.event) := by
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
    exact generated req ids bs _ hmem _
  rw [hp]
  simp only [xs,ProcIdTaggedRows.rows,ProcIdTaggedRows.block,List.flatMap_assoc,List.flatMap_map]

theorem count_transport (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hcap:(ProcIdConcatTraffic.rows ids bs).length≤2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)) t pub
      (if req then 71 else 72) (!req) msg=
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdConcatTraffic.trace ids bs) t pub (if req then 71 else 72) (!req) msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=((List.range (2^22)).flatMap _).count msg
  rw [physical req ids bs hcap,ProcIdConcatTraffic.physical req ids bs hcap]
/-- Both actual request and result buses balance with the repaired locally valid trace. -/
theorem balance (req : Bool) (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hr:(ProcRawConcatGeometry.rows bs).length≤2^22)
    (hi:(ProcIdConcatTraffic.rows ids bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace ids bs) t pub (if req then 71 else 72) req msg=
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)) t pub
      (if req then 71 else 72) (!req) msg := by
  rw [count_transport req ids bs hi]
  exact ProcNativeIdBalance.balance req ids bs hr hi t pub msg

end ZkFormal.NearV3.Candidates.ProcIdTaggedTraffic

import ZkFormal.NearV3.Candidates.ProcDistCmpPhysical
namespace ZkFormal.NearV3.Candidates.ProcNativeDistComparisonTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Assembly.CodecDigest
open ProcNativeOldComparisonCapacity

theorem block_size (b:NativeBlock)(hn:b.run.n≤64)(hc:b.run.conv.length≤4096) :
    (sdRows b.run (distribution b)).size≤86209 := by
  have hd:=ProcDistRowCost.generated_cost _ b.run _ (distribution_eq b hn)
  have hn2:=Nat.mul_self_le_mul_self hn
  simp only [sdRows,Array.size_append,scan_rows_size]
  split <;> omega

theorem list_size (bs:List NativeBlock)(h:∀b∈bs,b.run.n≤64 ∧ b.run.conv.length≤4096) :
    (ProcDistCmpPhysical.rows bs).size≤86209*bs.length := by
  have hg:∀xs:List NativeBlock,(∀b∈xs,b.run.n≤64 ∧ b.run.conv.length≤4096)→
      (xs.flatMap (fun b=>(sdRows b.run (distribution b)).toList)).length≤86209*xs.length := by
    intro xs
    induction xs with
    | nil=>simp
    | cons b xs ih=>
      intro h
      have hb:=h b (by simp)
      have hsz:=block_size b hb.1 hb.2
      have ht:=ih (fun a ha=>h a (by simp [ha]))
      simp only [List.flatMap_cons,List.length_append,Array.length_toList,List.length_cons]
      omega
  exact hg bs h

theorem bounds {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs) :
    (ProcDistCmpPhysical.rows bs).size≤2758688 ∧ (ProcDistCmpPhysical.rows bs).size≤2^22 := by
  have hbounds:∀b∈bs,b.run.n≤64 ∧ b.run.conv.length≤4096 := by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    have hr:=(hc.indexed i b hi).1
    have hs:=prepD0_sched hp b.pub (List.mem_iff_getElem?.mpr ⟨i,hr.1⟩)
    have hcnt:=ProcActualRequestCount.run_count _ i b.run hr.2
    have hib:=(ProcPreparedSequence.input_bounds b.pub b.old hs).2.2
    exact ⟨(hc.valid b hb).2,by omega⟩
  have hh:=list_size bs hbounds
  have hlen:=hc.length
  constructor <;> omega

theorem physical {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs)
    (t:Nat)(pub:List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ScanDist.table.interactions
      (SchedHeight.trace (ProcDistCmpPhysical.rows bs) distPad) t r pub B_SCMP true)=
      (bs.flatMap (fun b=>(distribution b).cmps)).map cmpMsg :=
  ProcDistCmpPhysical.blocks bs (fun b hb=>(hc.valid b hb).2) (bounds hp bs hc).2 t pub

theorem count {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs)
    (t:Nat)(pub msg:List Fp) :
    tableBusCount ScanDist.table.interactions (SchedHeight.trace (ProcDistCmpPhysical.rows bs) distPad)
      t pub B_SCMP true msg=
      ((bs.flatMap (fun b=>(distribution b).cmps)).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical hp bs hc t pub)
end ZkFormal.NearV3.Candidates.ProcNativeDistComparisonTraffic

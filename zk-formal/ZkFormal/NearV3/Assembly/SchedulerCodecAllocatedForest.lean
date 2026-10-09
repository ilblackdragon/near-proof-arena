import ZkFormal.NearV3.Assembly.SchedulerCodecAllocatedIds
import ZkFormal.NearV3.Candidates.ProcNativePresenceBalance
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Retain the occurrence-sensitive prestate forest budget alongside the SAME
allocated Codec/RawFrame traces. Repeated prestates are charged repeatedly. -/
theorem accepted_allocated_forest {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs : List NativeBlock,bs.length≤32 ∧
      preBytes (bs.map (fun b=>b.witness.pre))≤B ∧
      (∀b∈bs,b.Valid ∧ b.run.n≤64) ∧
      (∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i ∧
        b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre) ∧
      (ProcRawConcatGeometry.rows bs).length≤B+1184 ∧
      (∀time pub,TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub ∧
        TableLocal (ProcPriorRawFrame.table B_SPOST 73 B_VBYTES 74 75)
          (ProcRawConcatGeometry.trace bs) time pub) ∧
      ∀time pub msg,tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub B_SPOST true msg=
        tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
          (ProcRawConcatGeometry.trace bs) time pub B_SPOST false msg := by
  obtain ⟨m,steps,last,hm,_,hv,hlen,hcount,_,_⟩:=checkD0a_native_trace hk hw h
  obtain ⟨bs,hs,hpre,hb⟩:=native_allocated_blocks hp hk hm hv hlen
  have hlen':bs.length≤32 := by omega
  have hvalid:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧
      TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [] := by
    intro b hmem
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hmem
    have hh:=hb i b hi
    exact ⟨hh.1,hh.2.1,hh.2.2.2.2 0 []⟩
  have horder:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i := fun i b hi=>(hb i b hi).2.2.1
  have hbytes:=checkD0a_preBytes hk hw h hm hv
  have hcharge:=ProcRawNativeBudget.total_bound bs (fun b hm=>(hvalid b hm).1)
  rw [hpre] at hcharge
  have hraw:(ProcRawConcatGeometry.rows bs).length≤B+1184 := by omega
  have hforest:preBytes (bs.map (fun b=>b.witness.pre))≤B := by
    rw [hpre]
    exact hbytes
  refine ⟨bs,hlen',hforest,fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩,
    fun i b hi=>⟨(hb i b hi).2.2.1,(hb i b hi).2.2.2.1⟩,hraw,?_,?_⟩
  · intro time pub
    exact ⟨ProcCodecNativeConcatLocal.indexed_table bs (by omega) hvalid horder time pub,
      ProcRawNativeLocal.table bs (fun b hm=>(hvalid b hm).1) horder (by omega) _ _ _ _ _ _ _⟩
  · exact ProcNativePresenceBalance.balance bs (fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩) hlen' (by omega)
end ZkFormal.NearV3.Assembly.CodecDigest

import ZkFormal.NearV3.Assembly.SchedulerCodecOrderedNative
import ZkFormal.NearV3.Candidates.ProcRawNativeBudget
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Preserve the exact native prestate occurrences, including repeats. -/
theorem implicit_pre_list (k : WalkD0) (vids : Nat→Nat)
    (steps : List ImplicitStepV3) (bs : List NativeBlock) (hlen:bs.length=steps.length)
    (hb:∀i e b,steps[i]?=some e→bs[i]?=some b→MissingBlockAt k vids (1+i) e b) :
    bs.map (fun b=>b.witness.pre)=steps.map ImplicitStepV3.pre := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi hj
  simp only [List.length_map] at hi hj
  have hh:=hb i steps[i] bs[i] (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hi)
  simpa using hh.2.1

/-- Accepted execution supplies Codec and RawFrame local traces from the SAME
ordered state reads. The input-byte budget charges every native prestate
occurrence; no distinct-key or current-layout prior-size assumption is used. -/
theorem accepted_tables {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (hB:B≤2000000) (vids : Nat→Nat) :
    ∃bs : List NativeBlock,bs.length≤32 ∧
      (∀b∈bs,b.Valid ∧ b.run.n≤64) ∧
      (∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i) ∧
      (ProcRawConcatGeometry.rows bs).length≤B+1184 ∧
      (∀time pub,TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub) ∧
      ∀time pb lb bb sb rb pub,TableLocal (ProcPriorRawFrame.table pb lb bb sb rb)
        (ProcRawConcatGeometry.trace bs) time pub := by
  obtain ⟨m,steps,last,hm,_,hv,hlen,hcount,_,_⟩ := checkD0a_native_trace hk hw h
  obtain ⟨main,tail,htail,_,hpre,hAt,hb⟩ := native_ordered_blocks hp hk hm hv hlen vids
  have hlen' : (main::tail).length≤32 := by simp only [List.length_cons]; omega
  have hvalid : ∀b∈main::tail,b.Valid ∧ b.run.n≤64 ∧
      TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [] := by
    intro b hmem
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hmem
    have hh := hb i b hi
    exact ⟨hh.1,hh.2.1,hh.2.2.2 0 []⟩
  have horder : ∀(i : Nat)(b : NativeBlock),(main::tail)[i]?=some b→b.run.tau=i :=
    fun i b hi=>(hb i b hi).2.2.1
  have he : (main::tail).map (fun b=>b.witness.pre)=m.pre::steps.map ImplicitStepV3.pre := by
    simp only [List.map_cons,hpre,implicit_pre_list k vids steps tail htail hAt]
  have hbytes := checkD0a_preBytes hk hw h hm hv
  have hcharge := ProcRawNativeBudget.total_bound (main::tail) (fun b hm=>(hvalid b hm).1)
  rw [he] at hcharge
  have hraw : (ProcRawConcatGeometry.rows (main::tail)).length≤B+1184 := by omega
  refine ⟨main::tail,hlen',fun b hm=>⟨(hvalid b hm).1,(hvalid b hm).2.1⟩,horder,hraw,?_,?_⟩
  · exact ProcCodecNativeConcatLocal.indexed_table _ (by omega) hvalid horder
  · exact ProcRawNativeLocal.table _ (fun b hm=>(hvalid b hm).1) horder (by omega)
end ZkFormal.NearV3.Assembly.CodecDigest

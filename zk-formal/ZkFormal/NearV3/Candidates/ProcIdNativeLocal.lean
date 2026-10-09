import ZkFormal.NearV3.Candidates.ProcIdTaggedTrace
import ZkFormal.NearV3.Sched.Link.SoundPrep
namespace ZkFormal.NearV3.Candidates.ProcIdNativeLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest

theorem length_eq (ids : NativeBlock→List Nat) (bs : List NativeBlock) :
    (ProcIdTaggedRows.rows ids bs).length=(ProcIdConcatTraffic.rows ids bs).length := by
  simp [ProcIdTaggedRows.rows,ProcIdTaggedRows.block,ProcIdConcatTraffic.rows,
    ProcIdConcatTraffic.blockRows,List.length_flatMap]

theorem bounds (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hv:∀b∈bs,b.Valid) (hi:∀b∈bs,∀id∈ids b,id<2^64)
    (ho:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i) (hk:bs.length≤32) :
    ∀a∈ProcIdTaggedRows.rows ids bs,a.1<32 ∧ a.2.event.key<2^64 := by
  intro a ha
  obtain ⟨b,hb,r,hr,rfl⟩:=ProcIdTaggedRows.mem_origin ids bs a ha
  obtain ⟨j,hj⟩:=List.mem_iff_getElem?.mp hb
  have hjl:j<bs.length:=(List.getElem?_eq_some_iff.mp hj).1
  refine ⟨by rw [ho j b hj]; omega,?_⟩
  apply ProcPriorIdRanges.event_key (ids b) b.old.links (hi b hb) (ProcRecordConcatActive.native_links b (hv b hb))
  rw [←ProcPriorIdRows.rowsFrom_events ⟨none,ProcPriorIdCarry.zero⟩ (ProcPriorIds.events (ids b) b.old.links)]
  exact List.mem_map.mpr ⟨r,hr,rfl⟩

theorem table (ids : NativeBlock→List Nat) (bs : List NativeBlock)
    (hv:∀b∈bs,b.Valid) (hi:∀b∈bs,∀id∈ids b,id<2^64)
    (ho:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i) (hk:bs.length≤32)
    (hcap:(ProcIdConcatTraffic.rows ids bs).length<2^22) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorIdTable.table 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)) t pub := by
  apply ProcIdTaggedTrace.table _ (by rw [length_eq]; exact hcap)
    (bounds ids bs hv hi ho hk) (ProcIdTaggedRows.first ids bs)
  exact ProcIdTaggedRows.chain ids bs 0 (by simpa using ho)

/-- Prepared scheduler IDs supply the range obligation without restricting acceptance. -/
theorem prepared {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) (bs : List NativeBlock)
    (hv : ∀b∈bs,b.Valid) (hpub : ∀b∈bs,b.pub∈p.sched)
    (ho : ∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hk : bs.length≤32)
    (hcap : (ProcIdConcatTraffic.rows (fun b=>b.pub.ids) bs).length<2^22)
    (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorIdTable.table 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) t pub := by
  apply table _ bs hv (fun b hb=>ZkFormal.NearV3.Sched.prepD0_ids64 hp b.pub (hpub b hb)) ho hk hcap

theorem suffix (ids : NativeBlock→List Nat) (bs : List NativeBlock) (t r : Nat)
    (hr:(ProcIdConcatTraffic.rows ids bs).length≤r) :
    (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows ids bs)).cell t r=(fun _=>0) := by
  apply ProcIdTaggedTrace.padding
  rw [length_eq]
  exact hr
end ZkFormal.NearV3.Candidates.ProcIdNativeLocal

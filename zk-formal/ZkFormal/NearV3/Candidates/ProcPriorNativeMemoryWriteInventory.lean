import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryWrites
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorRows ProcPriorEvents
open ZkFormal.NearV3.Assembly.CodecDigest

def eventWrites (tau : Nat) (es : List Event) : List (List Fp) :=
  es.flatMap (fun e=>if e.query then [] else [ProcRecordWriteTraffic.message tau e])

theorem write_rows (b : NativeBlock) : writeMessages (tagged b)=eventWrites b.run.tau (events b.pub.ids b.old.links) := by
  have hmap:=rowsFrom_events ⟨none,ProcPriorCarry.zero⟩ (events b.pub.ids b.old.links)
  change (rows b.pub.ids b.old.links).map (·.event)=events b.pub.ids b.old.links at hmap
  rw [writeMessages,tagged,List.flatMap_map,eventWrites,←hmap,List.flatMap_map]
  rfl

/-- Sorting preserves duplicate writes and their original record ordinals. -/
theorem event_writes_perm (ids : List Nat) (rs : List NearSpec.Bandwidth.LinkAllowance) (tau : Nat) :
    (eventWrites tau (events ids rs)).Perm
      ((writeEvents ids rs).map (ProcRecordWriteTraffic.message tau)) := by
  have hp:=List.Perm.flatMap_right (fun e=>if e.query then [] else [ProcRecordWriteTraffic.message tau e]) (events_perm ids rs)
  change (eventWrites tau (events ids rs)).Perm (eventWrites tau (writeEvents ids rs++queryEvents ids rs)) at hp
  have hq:eventWrites tau (queryEvents ids rs)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro e he
    simp only [(query_source ids rs e he).2.2.1,ite_true]
  have hw:eventWrites tau (writeEvents ids rs)=
      (writeEvents ids rs).map (ProcRecordWriteTraffic.message tau) := by
    unfold eventWrites
    have hh:(writeEvents ids rs).flatMap (fun e=>if e.query then [] else [ProcRecordWriteTraffic.message tau e])=
      (writeEvents ids rs).flatMap (fun e=>[ProcRecordWriteTraffic.message tau e]) := by
      apply ProcCodecPublicIdEnumeration.flat_congr
      intro e he
      have hfalse:e.query=false:=(write_source ids rs e he).choose_spec.2.2.1
      simp only [hfalse,Bool.false_eq_true,ite_false]
    rw [hh]
    have hm:∀xs : List Event,xs.flatMap (fun e=>[ProcRecordWriteTraffic.message tau e])=
        xs.map (ProcRecordWriteTraffic.message tau) := by
      intro xs
      induction xs with
      | nil=>rfl
      | cons x xs ih=>simp [ih]
    exact hm _
  have he:eventWrites tau (writeEvents ids rs++queryEvents ids rs)=eventWrites tau (writeEvents ids rs) := by
    unfold eventWrites
    rw [List.flatMap_append]
    change eventWrites tau (writeEvents ids rs)++eventWrites tau (queryEvents ids rs)=_
    rw [hq,List.append_nil]
    rfl
  rw [he,hw] at hp
  exact hp

theorem tagged_writes_perm (b : NativeBlock) :
    (writeMessages (tagged b)).Perm
      ((writeEvents b.pub.ids b.old.links).map (ProcRecordWriteTraffic.message b.run.tau)) := by
  rw [write_rows]
  exact event_writes_perm _ _ _

theorem all_writes_perm (bs : List NativeBlock) :
    (writeMessages (allRows bs)).Perm
      (bs.flatMap (fun b=>(writeEvents b.pub.ids b.old.links).map (ProcRecordWriteTraffic.message b.run.tau))) := by
  induction bs with
  | nil=>exact .nil
  | cons b bs ih=>
    have hp:=tagged_writes_perm b
    simp only [allRows,List.flatMap_cons,writeMessages,List.flatMap_append] at *
    exact hp.append ih
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory

import ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorRows ProcPriorEvents
open ZkFormal.NearV3.Assembly.CodecDigest

def eventQueries (tau : Nat) (es : List Event) : List (List Fp) :=
  es.flatMap (fun e=>if e.query then [(ProcPriorCodecQueries.message tau e).map Fp.ofNat] else [])

theorem query_rows (b : NativeBlock) : queryMessages (tagged b)=eventQueries b.run.tau (events b.pub.ids b.old.links) := by
  have hmap:=rowsFrom_events ⟨none,ProcPriorCarry.zero⟩ (events b.pub.ids b.old.links)
  change (rows b.pub.ids b.old.links).map (·.event)=events b.pub.ids b.old.links at hmap
  rw [queryMessages,tagged,List.flatMap_map,eventQueries,←hmap,List.flatMap_map]
  apply ProcCodecPublicIdEnumeration.flat_congr
  intro a _
  cases hq:a.event.query <;> cases hh:a.event.hi <;>
    simp [queryMessage,ProcPriorCodecQueries.message,ProcPriorCells.bit,hq,hh,show Fp.ofNat 0=0 from rfl,show Fp.ofNat 1=1 from rfl]

theorem event_queries_perm (ids : List Nat) (rs : List NearSpec.Bandwidth.LinkAllowance) (tau : Nat) :
    (eventQueries tau (events ids rs)).Perm
      ((queryEvents ids rs).map (fun e=>(ProcPriorCodecQueries.message tau e).map Fp.ofNat)) := by
  have hp:= List.Perm.flatMap_right (fun e=>if e.query then [(ProcPriorCodecQueries.message tau e).map Fp.ofNat] else []) (events_perm ids rs)
  change (eventQueries tau (events ids rs)).Perm (eventQueries tau (writeEvents ids rs++queryEvents ids rs)) at hp
  have hw:eventQueries tau (writeEvents ids rs)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro e he
    have hq: e.query=false := (write_source ids rs e he).choose_spec.2.2.1
    simp only [hq,Bool.false_eq_true,ite_false]
  have hq:eventQueries tau (queryEvents ids rs)=
      (queryEvents ids rs).map (fun e=>(ProcPriorCodecQueries.message tau e).map Fp.ofNat) := by
    unfold eventQueries
    have hh: (queryEvents ids rs).flatMap (fun e=>if e.query then [(ProcPriorCodecQueries.message tau e).map Fp.ofNat] else [])=
      (queryEvents ids rs).flatMap (fun e=>[(ProcPriorCodecQueries.message tau e).map Fp.ofNat]) := by
      apply ProcCodecPublicIdEnumeration.flat_congr
      intro e he
      simp only [(query_source ids rs e he).2.2.1,ite_true]
    rw [hh]
    have hm:∀xs : List Event,xs.flatMap (fun e=>[(ProcPriorCodecQueries.message tau e).map Fp.ofNat])=
        xs.map (fun e=>(ProcPriorCodecQueries.message tau e).map Fp.ofNat) := by
      intro xs
      induction xs with
      | nil=>rfl
      | cons x xs ih=>simp [ih]
    exact hm _
  have he:eventQueries tau (writeEvents ids rs++queryEvents ids rs)=eventQueries tau (queryEvents ids rs) := by
    unfold eventQueries
    rw [List.flatMap_append]
    change eventQueries tau (writeEvents ids rs)++eventQueries tau (queryEvents ids rs)=_
    rw [hw,List.nil_append]
    rfl
  rw [he,hq] at hp
  exact hp

theorem tagged_queries_perm (b : NativeBlock) :
    (queryMessages (tagged b)).Perm
      ((queryEvents b.pub.ids b.old.links).map (fun e=>(ProcPriorCodecQueries.message b.run.tau e).map Fp.ofNat)) := by
  rw [query_rows]
  exact event_queries_perm _ _ _
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory

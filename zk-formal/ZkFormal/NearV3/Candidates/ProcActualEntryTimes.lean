import ZkFormal.NearV3.Candidates.ProcActualAfterMemoryReduction
import ZkFormal.NearV3.Candidates.ProcModelTime
namespace ZkFormal.NearV3.Candidates.ProcActualEntryTimes
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayEntry

def times (s : Acc) : List Nat := (ProcActualEntryTransition.entries s).toList.map Entry.ts

theorem step_times (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (s out : Acc) (h : step I cv rd sh T x s=.ok (.yield out)) :
    times out=times s++[ProcPushSortContract.stampTime cv.size rd.bucket[x]!.ts] := by
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals simp [times,ProcActualEntryTransition.entries,ProcPushSortContract.stampTime]

theorem loop_times (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T : Nat) (xs : List Nat) (s out : Acc)
    (h : forIn xs s (step I cv rd sh T)=.ok out) :
    times out=times s++xs.map (fun x=>ProcPushSortContract.stampTime cv.size rd.bucket[x]!.ts) := by
  induction xs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv rd sh T x s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,_,_,_⟩ := ProcActualEntryTransition.step_effect I cv rd sh T x s next
        (NearSpecV3.Rng.ofSeed I.seed) he
      simp only [he,bind,Except.bind] at h
      rw [ih next h,step_times I cv rd sh T x s next he]
      simp [List.append_assoc]

theorem batch_times (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T : Nat) (s out : Acc)
    (h : forIn (List.range rd.bucket.length) s (step I cv rd sh T)=.ok out) :
    times out=times s++rd.bucket.map (fun b=>ProcPushSortContract.stampTime cv.size b.ts) := by
  have hh := loop_times I cv rd sh T _ s out h
  have he := ProcActualEntryTransition.map_indices rd.bucket
  have hm := congrArg (List.map (fun b : Push=>ProcPushSortContract.stampTime cv.size b.ts)) he
  simp only [List.map_map,Function.comp_def] at hm
  rw [hm] at hh
  exact hh

theorem translated_bucket (R T start : Nat) (bs : List Push) (hR : R≤T0)
    (ht : R≤start) (hT : T=T0+(start-R))
    (ho : bs.Pairwise (fun a b=>a.ts<b.ts)) (hb : ∀b∈bs,b.ts<start) :
    (bs.map (fun b=>ProcPushSortContract.stampTime R b.ts)).Pairwise (·<·) ∧
      ∀t∈bs.map (fun b=>ProcPushSortContract.stampTime R b.ts),t<T := by
  constructor
  · apply List.pairwise_map.mpr
    exact ho.imp (fun {a b} hab=>ProcPushSortContract.stamp_strict R hR a.ts b.ts hab)
  · intro t hm
    obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hm
    have hh := ProcPushSortContract.stamp_strict R hR b.ts start (hb b hb')
    have he : ProcPushSortContract.stampTime R start=T := by
      simp [ProcPushSortContract.stampTime,show ¬start<R by omega,hT]
    rw [he] at hh
    exact hh
theorem entry_compare (es : List Entry) (T i : Nat)
    (ho : es.Pairwise (fun a b=>a.ts<b.ts)) (hb : ∀e∈es,e.ts<T) (hi : i<es.length) :
    check (es.toArray[i]!.ts < (if i+1=es.toArray.size then T else es.toArray[i+1]!.ts))
      "bucket ts order"=.ok () := by
  have he : es.toArray[i]!.ts=es[i].ts := by simp [getElem!_pos,hi]
  by_cases hl : i+1=es.length
  · have ht := hb es[i] (List.getElem_mem hi)
    simp only [List.size_toArray,hl,ite_true,he,ht,decide_true,check,pure,Except.pure]
  · have hn : i+1<es.length := by omega
    have ht := List.pairwise_iff_getElem.mp ho i (i+1) hi hn (by omega)
    have he' : es.toArray[i+1]!.ts=es[i+1].ts := by simp [getElem!_pos,hn]
    simp only [List.size_toArray,hl,ite_false,he,he',ht,decide_true,check,ite_true,pure,Except.pure]

/-- Exact timestamp map suffices to discharge every indexed bucket comparison. -/
theorem mapped_checks (es : List Entry) (ts : List Nat) (T : Nat)
    (he : es.map Entry.ts=ts) (ho : ts.Pairwise (·<·)) (hb : ∀t∈ts,t<T) :
    ∀i,i<es.length → check (es.toArray[i]!.ts <
      (if i+1=es.toArray.size then T else es.toArray[i+1]!.ts)) "bucket ts order"=.ok () := by
  intro i hi
  have ho' : es.Pairwise (fun a b=>a.ts<b.ts) := by
    apply List.pairwise_map.mp
    rw [he]; exact ho
  apply entry_compare es T i ho' _ hi
  intro e hm
  apply hb
  rw [←he]
  exact List.mem_map_of_mem hm
end ZkFormal.NearV3.Candidates.ProcActualEntryTimes

import ZkFormal.NearV3.Candidates.ProcNativeBucket
namespace ZkFormal.NearV3.Candidates.ProcNativePush
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers ProcNativeGrant

def toPM (p : Push) : PM := ⟨p.key,p.z,p.ts,p.v⟩

theorem step_pushes (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (K z t v : Nat) (st : PState) (hs : Inv n M st) (hv : Valid reqs v) :
    (stepE n allowed reqs K z t v (native st)).2=
      (ProcPushEntries.pushOf K z (ProcEntryEvent.event n allowed reqs.toArray[v/64]! v t st)).map toPM := by
  have hrest : reqs.toArray[v/64]!.incs.drop (v%64+1)≠[] ↔
      (v%64+1==reqs.toArray[v/64]!.incs.length)=false := by
    simp only [ne_eq,List.drop_eq_nil_iff,beq_eq_false_iff_ne]
    have := hv.2
    omega
  unfold stepE
  rw [ProcNativeBucket.reqAt_source reqs v hv]
  simp only [List.drop_eq_getElem_cons hv.2]
  have hd : reqs.toArray[v/64]!.incs.getD (v%64) 0=reqs.toArray[v/64]!.incs[v%64]'hv.2 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hv.2,Option.getD_some]
  rw [←hd,grant_native n M hM allowed st hs]
  simp only [hrest,ProcPushEntries.pushOf,ProcEntryEvent.event,native,zNext,
    Bool.and_eq_true,Bool.not_eq_true']
  split <;> simp_all only [List.map_cons,List.map_nil,toPM]
end ZkFormal.NearV3.Candidates.ProcNativePush

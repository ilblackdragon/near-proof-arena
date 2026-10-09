import ZkFormal.NearV3.Rcpt.Candidates.NativeMidrootRecords
import ZkFormal.NearV3.Rcpt.Candidates.CompactRootRanks

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

/-- Indexed native structural output digests, preserving instance order. -/
def nativeRootRecords (start : Nat) : List PTrie→List ZkFormal.Near.Msg
  | []=>[]
  | t::ts=>([start+1]++t.hashOf.map UInt8.toNat)::nativeRootRecords (start+1) ts

theorem nativeRootRecords_length (start : Nat) (ts : List PTrie) :
    (nativeRootRecords start ts).length=ts.length := by
  induction ts generalizing start with
  | nil=>rfl
  | cons t ts ih=>simp only [nativeRootRecords,List.length_cons,ih]

theorem nativeRootRecords_get : ∀(ts : List PTrie)(start i : Nat)(t : PTrie),ts[i]?=some t→
    (nativeRootRecords start ts)[i]?=some ([start+i+1]++t.hashOf.map UInt8.toNat)
  | [],_,_,_,h=>by simp at h
  | a::ts,start,0,t,h=>by simp only [List.getElem?_cons_zero,Option.some.injEq] at h;subst t;rfl
  | a::ts,start,i+1,t,h=>by
    have ih:=nativeRootRecords_get ts (start+1) i t h
    simpa only [nativeRootRecords,List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

theorem allocated_root_records (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hcount : insts.length=us.length)
    (hi : ∀(tau : Nat)(u : SchedulerUpsertWitness)(I : UpsInst),us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I) :
    insts.map (fun I=>[I.tau+1]++I.post)=nativeRootRecords 0 (us.map (fun u=>u.run.output)) := by
  apply List.ext_getElem
  · simp only [List.length_map,nativeRootRecords_length,hcount]
  · intro i hi' hu'
    have hib : i<insts.length:=by simpa only [List.length_map] using hi'
    have hub : i<us.length:=by omega
    have ha:=hi i us[i] insts[i] (by simp [hub]) (by simp [hib])
    have hr:=nativeRootRecords_get (us.map (fun u=>u.run.output)) 0 i (us[i]).run.output (by simp [hub])
    have he:=(List.getElem?_eq_some_iff.mp hr).2
    simp only [List.getElem_map,he,ha.1,ha.2.2.1,Nat.zero_add]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

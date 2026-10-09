import ZkFormal.NearV3.Rcpt.Candidates.NativeRootRecords
import ZkFormal.NearV3.Assembly.NativeTrace

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

def nativeInputRoots (start : Nat) : List PTrie→List ZkFormal.Near.Msg
  | []=>[]
  | t::ts=>([start]++t.hashOf.map UInt8.toNat)::nativeInputRoots (start+1) ts

/-- Native loop order gives exact ROOT conservation, not merely root set equality. -/
theorem implicit_root_chain {k : WalkD0} {root last : Bytes} {pairs : List (Blk×Transition)}
    {steps : List ImplicitStepV3} (h : ImplicitTraceValid k root pairs steps last) (start : Nat) :
    ([start]++root.map UInt8.toNat)::nativeRootRecords start (steps.map ImplicitStepV3.post)=
      nativeInputRoots start (steps.map ImplicitStepV3.pre)++[[start+steps.length]++last.map UInt8.toNat] := by
  induction h generalizing start with
  | nil root=>simp [nativeRootRecords,nativeInputRoots]
  | cons root b t rest steps post last hrun hpost htail ih=>
    have hr:=implicit_run_root_length hrun
    have hpre : (partialTrie t.values root [keyDelayedIdx,keyBwState]).hashOf=root:=
      (built_spec t.values trieFuel root [keyDelayedIdx,keyBwState] hr).1
    simp only [List.map_cons,nativeRootRecords,nativeInputRoots,List.cons_append,List.length_cons,hpre]
    simpa only [List.cons_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      congrArg (List.cons ([start]++root.map UInt8.toNat)) (ih (start+1))

theorem main_implicit_root_chain {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ([0]++k.slotB2.prevStateRoot.map UInt8.toNat)::
      nativeRootRecords 0 (m.result.trie::steps.map ImplicitStepV3.post)=
      nativeInputRoots 0 (m.pre::steps.map ImplicitStepV3.pre)++
        [[steps.length+1]++last.map UInt8.toNat] := by
  simp only [nativeRootRecords,nativeInputRoots,Nat.zero_add,List.cons_append,hm.preRoot]
  apply congrArg (List.cons _)
  simpa only [List.cons_append,Nat.add_comm] using (implicit_root_chain hv 1)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

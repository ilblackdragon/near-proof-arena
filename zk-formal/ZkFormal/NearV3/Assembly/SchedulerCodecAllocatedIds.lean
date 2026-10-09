import ZkFormal.NearV3.Assembly.SchedulerCodecOrderedValueIds
import ZkFormal.NearV3.Assembly.SchedulerCodecRawAccepted
import ZkFormal.NearV3.Assembly.SchedulerPriorValueId
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Render.UpsGen Rcpt.Candidates.NodePostUpdate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def nativePriorIds (trees : List PTrie) (i : Nat) : Nat :=
  match trees[i]? with
  | none=>0
  | some tree=>priorValueId (trees.take i) tree

/-- Choose IDs from the actual allocated prestate forest BEFORE generating
Codec rows, and retain their equality for every generated instance. -/
theorem native_allocated_blocks {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length=k.implicitBlks.length) :
    ∃bs : List NativeBlock,bs.length=steps.length+1 ∧
      bs.map (fun b=>b.witness.pre)=m.pre::steps.map ImplicitStepV3.pre ∧
      ∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.Valid ∧ b.run.n≤64 ∧ b.run.tau=i ∧
        b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre ∧
        ∀time pub,TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) time pub := by
  let trees:=m.pre::steps.map ImplicitStepV3.pre
  obtain ⟨main,tail,htail,_,hpre,hAt,hb⟩:=native_ordered_blocks_ids hp hw hm hv hlen (nativePriorIds trees)
  have he:(main::tail).map (fun b=>b.witness.pre)=trees := by
    simp only [List.map_cons,hpre,implicit_pre_list k (nativePriorIds trees) steps tail htail hAt,trees]
  refine ⟨main::tail,by simp [htail],he,?_⟩
  intro i b hi
  have hh:=hb i b hi
  have ht:trees[i]?=some b.witness.pre := by
    rw [←he,List.getElem?_map,hi]
    rfl
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_,hh.2.2.2.2⟩
  rw [he,hh.2.2.2.1]
  simp [nativePriorIds,ht]
theorem allocated_present (bs : List NativeBlock)
    (hids:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→
      b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre)
    (pre post : List NativeBlock) (b : NativeBlock) (he:bs=pre++b::post)
    (hb:b.Valid) (bytes : Bytes) (hp:b.prior=some bytes) :
    (forestStoreViews (bs.map (fun b=>b.witness.pre))).values[b.vid]?=some (seedValue b.vid bytes) := by
  have hi:bs[pre.length]?=some b := by simp [he]
  have hid:=hids _ _ hi
  have ht:((bs.map (fun b=>b.witness.pre)).take pre.length)=pre.map (fun b=>b.witness.pre) := by
    simp [he,List.map_append]
  rw [ht] at hid
  have hr:=hb.2.1
  rw [hp] at hr
  rw [hid]
  simpa [he,List.map_append] using present (pre.map (fun b=>b.witness.pre))
    (post.map (fun b=>b.witness.pre)) b.witness.pre bytes hr

end ZkFormal.NearV3.Assembly.CodecDigest

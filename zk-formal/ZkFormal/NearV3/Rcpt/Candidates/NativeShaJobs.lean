import ZkFormal.NearV3.Rcpt.Candidates.NativeViewShaRows
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaJobs

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpecV3 Assembly Render.UpsGen

/-- Node identifiers follow physical view order, including repeated occurrences. -/
def nativeNodeShaJobsFrom (n : Nat) : List NodeS3 → List Render.Msg
  | [] => []
  | s::ss => ⟨msgId K_NPRE n,s.v.ser false⟩::⟨msgId K_NPOST n,s.v.ser true⟩::
      nativeNodeShaJobsFrom (n+1) ss

/-- Empty value records emit no VPRE byte/digest job. -/
def nativeValueShaJobs : List ValE → List Render.Msg
  | [] => []
  | v::vs => (if v.bytes=[] then [] else [⟨msgId K_VPRE v.vid,v.bytes⟩])++nativeValueShaJobs vs

def nativeShaJobs (ns : List NodeS3) (vs : List ValE) : List Render.Msg :=
  nativeNodeShaJobsFrom 0 ns++nativeValueShaJobs vs

theorem nativeNodeShaJobs_rows (n : Nat) (ns : List NodeS3) :
    ((nativeNodeShaJobsFrom n ns).map (fun m => Render.rowsOf m.bytes.length)).sum=
      nodePairShaRows ns := by
  induction ns generalizing n with
  | nil => simp [nativeNodeShaJobsFrom,nodePairShaRows]
  | cons s ss ih =>
    simp only [nativeNodeShaJobsFrom,List.map_cons,List.sum_cons,nodePairShaRows] at *
    rw [ih]
    omega

theorem nativeValueShaJobs_rows (vs : List ValE) :
    ((nativeValueShaJobs vs).map (fun m => Render.rowsOf m.bytes.length)).sum≤
      hashRows (vs.map (fun v => v.bytes.length)) := by
  induction vs with
  | nil => simp [nativeValueShaJobs,hashRows]
  | cons v vs ih =>
    simp only [nativeValueShaJobs,List.map_cons,hashRows,List.map_map,
      Function.comp_def,List.sum_cons] at *
    split <;> simp_all only [List.nil_append,List.cons_append,List.map_cons,
      List.sum_cons,List.map_nil,List.sum_nil,List.append_nil] <;> omega

theorem nativeShaJobs_rows (ns : List NodeS3) (vs : List ValE) :
    ((nativeShaJobs ns vs).map (fun m => Render.rowsOf m.bytes.length)).sum≤
      nodeValueShaRows ns vs := by
  have hv := nativeValueShaJobs_rows vs
  simp only [nativeShaJobs,List.map_append,List.sum_append,nativeNodeShaJobs_rows,nodeValueShaRows]
  omega

/-- The bound applies to final updated views, not just the seed, provided their
prestate occurrence lengths are those of the same accepted native execution. -/
theorem accepted_updated_nativeShaJobs {cb wb : NearSpec.Bytes} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : NearSpec.Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hs : steps.length≤31)
    (hgood : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true)
    (ns : List NodeS3) (vs : List ValE) (hn : NodeWf3 ns)
    (hpre : ns.map (fun s => (s.v.ser false).length)=
      ((m.pre::steps.map ImplicitStepV3.pre).flatMap occs).map (fun t => (nodeEnc t).length))
    (hval : vs.map (fun v => v.bytes.length)=
      (forestBytes (m.pre::steps.map ImplicitStepV3.pre)).map List.length) :
    ((nativeShaJobs ns vs).map (fun m => Render.rowsOf m.bytes.length)).sum≤2925275 := by
  have hb := checkD0a_preBytes hk hw hc hm hv
  have ha := forest_sha_amortized (m.pre::steps.map ImplicitStepV3.pre) hgood
  have he := updated_native_rows ns vs _ hn hpre hval
  have hj := nativeShaJobs_rows ns vs
  simp only [List.length_cons,List.length_map] at ha
  unfold B0 at hb
  omega

end ZkFormal.NearV3.Rcpt.Candidates

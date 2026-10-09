import ZkFormal.NearV3.Assembly.TraceHeads
import ZkFormal.NearV3.Assembly.AppliedSeeds

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Concrete execution views. Source dictionary and per-source receipt grouping
are still separate; the singleton receipt list preserves exact applied order. -/
def executionViews (k : WalkD0) (w : StateWitness) (m : MainExecutionV3)
    (steps : List ImplicitStepV3) (dictionary : List DictionaryEntryV3) : ExtV3 :=
  {traceStoreViews (runtimePairs m steps) with
   receipts := [receiptListSeed (appliedReceipts k w)], dictionary := dictionary}

theorem executionViews_applied {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {dictionary : List DictionaryEntryV3} {bs : Bytes}
    (hw : decodeStateWitness bs = .ok w) :
    (executionViews k w m steps dictionary).applied = appliedReceipts k w := by
  simpa only [executionViews, ExtV3.applied, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using receiptListSeed_applied (k := k) hw

theorem executionViews_main {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {dictionary : List DictionaryEntryV3} {bs : Bytes}
    (hm : m.NativeValid k w) (hd : decodeStateWitness bs = .ok w)
    (hw : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    m.Valid k (executionViews k w m steps dictionary) := by
  apply hm.normalized hm.root_length
  · change (traceStoreViews (runtimePairs m steps)).store 0 = _
    rw [traceStoreViews_store, runtimePairs_pre]
    exact forestStoreViews_store hw hc rfl
  · exact executionViews_applied hd
  · change (traceStoreViews (runtimePairs m steps)).post 0 = _
    rw [traceStoreViews_post (show (runtimePairs m steps)[0]? = some (m.pre,m.result.trie) from rfl)]
    exact hm.postRoot

theorem executionViews_implicit {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {dictionary : List DictionaryEntryV3} {pairs : List (Blk × Transition)} {last : Bytes}
    (hv : ImplicitTraceValid k m.result.trie.hashOf pairs steps last)
    (hw : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    ImplicitRunV3 k (executionViews k w m steps dictionary) 1 m.result.trie.hashOf
      (pairs.map Prod.fst) last := by
  apply hv.normalized
  exact runtimePairs_implicit_views hv m hw hc

/-- Accepted native executions have concrete store/head/receipt payload views.
Source authentication, header equality and whole GoodV3 remain separate. -/
theorem checkD0a_execution_views {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (dictionary : List DictionaryEntryV3) :
    ∃ m steps last, m.Valid k (executionViews k w m steps dictionary) ∧
      ImplicitRunV3 k (executionViews k w m steps dictionary) 1 m.result.trie.hashOf
        k.implicitBlks last := by
  obtain ⟨m,steps,last,hm,_,hv,hlen,_,hc,hf⟩ := checkD0a_native_trace hk hw h
  have hd := hw
  unfold decodeW at hd
  obtain ⟨⟨bs,codes⟩,_,hd⟩ := ReexecV3D0.bind_ok' hd
  have hi := executionViews_implicit (w := w) (dictionary := dictionary) hv hf hc
  have hn := hv.length
  simp only [List.length_zip] at hn
  rw [List.map_fst_zip (by omega)] at hi
  exact ⟨m,steps,last,executionViews_main hm hd hf hc,hi⟩

end ZkFormal.NearV3.Assembly

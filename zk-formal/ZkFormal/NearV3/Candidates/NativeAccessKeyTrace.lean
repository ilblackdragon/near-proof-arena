import ZkFormal.NearV3.Candidates.NativeAccessKeyProviders
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestAllocation
import ZkFormal.NearV3.Assembly.Compute

namespace ZkFormal.NearV3.Candidates.NativeAccessKeyTrace
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Rcpt.Candidates.NodePostUpdate ZkFormal.Air
open NativeAccessKeyProviders

/-- Construct the real access-key table from accepted execution. One provider
per original VID, with the actual number of conditional receipt uses, including
empty/all-absent batches. No caller-supplied encoding or traffic premise. -/
theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hc:checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm:m.NativeValid k w)
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (tt : Nat) (pub : List Algebra.Fp) :
    let es:=providers m.pre (appliedReceipts k w)
    AkeyWf es ∧ (∀e∈es,∀b∈e.bytes,b<256) ∧
    TableLocal AkeyV3.table (akeyTraceAligned es) tt pub ∧
    TableTraffic AkeyV3.interactions (akeyTraceAligned es) tt pub (akeyTraffic es) ∧
    (∀msg,tableBusCount AkeyV3.interactions (akeyTraceAligned es) tt pub B_VBYTES true msg=
      cnt ((selected m.pre (appliedReceipts k w)).eraseDups.flatMap
        (fun i=>emitAt i 0 (((NearSpecV3.valsOf m.pre).getD i []).map UInt8.toNat))) msg) := by
  have hwell:m.pre.wf=true:=by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  have hbytes:=checkD0a_preBytes hk hw hc hm hv
  have hcount:=(forest_allocation_counts (m.pre::steps.map ImplicitStepV3.pre) hbytes).2
  have hvals:(NearSpecV3.valsOf m.pre).length<Algebra.P:=by
    simp only [forestBytes,List.flatMap_cons,List.length_append] at hcount
    rw [native_valsOf_eq]
    unfold Algebra.P
    omega
  have hgas:k.slotB2.gasLimit≤maxGasLimitD0:=by
    have hh:=(relD0a_iff B0 cb wb).mpr hc
    simpa only [a1,hk,decide_eq_true_eq] using hh.2.1
  have hreceipts:=applyNewChunk_receipt_bound hm.run hgas
  have hvalid:=NativeAccessKeyValidation.newchunk_valid (TrieShape.of_wf _ hwell) hm.run
  have hWf:=provider_wf hvalid (by omega) hvals
  have ht:=akey_aligned_complete (providers m.pre (appliedReceipts k w)) ⟨hWf.last,hWf.rows⟩ tt pub
  refine ⟨hWf,fun e he=>(provider_bytes hvalid e he).2.2,ht.1,ht.2.1,?_⟩
  intro msg
  rw [(ht.2.1 B_VBYTES msg).1]
  change cnt (akeySends (providers m.pre (appliedReceipts k w)) B_VBYTES) msg=_
  rw [byte_inventory hvalid]

end ZkFormal.NearV3.Candidates.NativeAccessKeyTrace

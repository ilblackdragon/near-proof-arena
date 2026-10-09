import ZkFormal.NearV3.Assembly.NativeWitnessSize
import ZkFormal.NearV3.Assembly.NativePayload
import ZkFormal.NearV3.Assembly.PrepClaimComplete
import ZkFormal.NearV3.Assembly.PrepBodyComplete

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- Actual accepted bytes admit a concrete prepared semantic execution and a
nonexpanding encoded witness. Shape and canonical/unfolded amendments remain
separate obligations before this can instantiate all of GoodV3. -/
theorem checkD0a_prepared_fields {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ()) :
    ∃ m steps last p, let x := nativeExecutionViews k w m steps
      m.NativeValid k w ∧
      prepD0 cb (nativeHint k w m) = .ok p ∧
      SourceSemanticsV3 k x ∧ m.Valid k x ∧
      ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
      HeaderSemanticsV3 k (nativeHint k w m) p m last ∧
      (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608 ∧
      ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000 := by
  obtain ⟨m,steps,last,hm,ht,hv,hlen,_,hcap,hf⟩ := checkD0a_native_trace hk hw h
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,_⟩ := checkD0_native_steps hk hw hc
  obtain ⟨raw,codes,hfile,hd,hraw,hepoch,hinner,hhash⟩ := checkD0_witness_fields hk hw hc
  have hsize := nativeExecutionViews_witness_size hd hm hv hcount hf hcap hepoch hinner hhash
  have hi := executionViews_implicit (w := w)
    (dictionary := sourceDictionarySeeds (sourceKeysV3 k) w.entries) hv hf hcap
  rw [List.map_fst_zip (by omega : k.implicitBlks.length ≤ w.implicit.length)] at hi
  obtain ⟨pc,hpc⟩ := checkD0a_prepClaim_exists hk hw h
  have hh := checkD0_header_of_trace hk hw hc hm ht
  have hr := (relD0a_iff B cb wb).mpr h
  have hg : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1,hk,decide_eq_true_eq] using hr.2.1
  obtain ⟨p,hp,hheader⟩ := prepD0_native_success hpc hk hm hh hd hg
  exact ⟨m,steps,last,p,hm,hp,checkD0a_source_semantics hk hw h m steps,
    executionViews_main hm hd hf hcap,hi,hheader,Nat.le_trans hsize hraw,
    nativeExecutionViews_main_payload hm hf hcap⟩

end ZkFormal.NearV3.Assembly

import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupWhole
import ZkFormal.NearV3.Rcpt.Candidates.NativeJointRequestBounds
import ZkFormal.NearV3.Assembly.ReceiptWellformed

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.UpsGen Assembly Qv Qv.Candidates.CombinedWalkGen

/-- Full native acceptance discharges every forest, key, identifier and aggregate
row bound needed by the concrete ranked Walk table. -/
theorem accepted_same_lookup_physical {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a 2000000 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Resolve) (t : Nat) (pub : List Fp) :
    ∃v : MainValues,∃ws : List WalkR,
      v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve)=some ws ∧
      TableLocal {WalkV3.table with maxLog:=22} (nativeWalkTrace (rankWalks [] ws)) t pub ∧
      TableTraffic WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) t pub (walkTraffic3 (rankWalks [] ws)) ∧
      ∀Is : List Render.UpsInst,Is.length≤32→
        (walkEdgeKeys (ws++upsWalkInventory Is)).length<Algebra.P ∧
        (walkBmapKeys (ws++upsWalkInventory Is)).length<Algebra.P := by
  have hc : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff 2000000 cb wb).mpr h).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hc
  have hsteps : steps.length≤31 := by
    have hs:=hv.length
    simp only [List.length_zip] at hs
    omega
  have htrees : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  obtain ⟨v,hvalid,hreads,ws,hws⟩:=native_execution_all_lookups hm hv resolve
  have hbytes:=checkD0a_preBytes hk hw h hm hv
  have hgas : k.slotB2.gasLimit≤maxGasLimitD0 := by
    have hh:=(relD0a_iff 2000000 cb wb).mpr h
    simpa only [a1,hk,decide_eq_true_eq] using hh.2.1
  have hn:=applyNewChunk_receipt_bound hm.run hgas
  have hreceipt : ∀r∈appliedReceipts k w,r.wf=true := by
    have hd:=hw
    unfold decodeW at hd
    obtain ⟨⟨raw,codes⟩,_,hd⟩:=ReexecV3D0.bind_ok' hd
    exact appliedReceipts_wf hd
  have hbuffer : (v.buffered.map List.length).getD 0≤2000000 := by
    have hread:=hreads.2.1
    cases hb : v.buffered with
    | none=>simp [hb]
    | some b=>
      rw [hb] at hread
      simpa only [hb,Option.map_some,Option.getD_some] using
        checkD0a_read_bound hk hw h hm hv (t:=m.pre) (by simp) hread
  have hg:=main_group_count_bound v hvalid hbuffer
  have hp : (((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))).map Prod.fst)=
      m.pre::steps.map ImplicitStepV3.pre := by simp [List.map_map,Function.comp_def]
  have hphysical:=native_all_walk_physical _ _ _ _ _ resolve ws hws
    (by simpa only [hp] using htrees) (by simpa only [hp] using hbytes)
    (by simp only [List.length_cons,List.length_map];change steps.length+1≤2013265921;omega)
    hreceipt hn hg (by simp only [List.length_map];omega) t pub
  refine ⟨v,ws,hvalid,hreads,hws,hphysical.1,hphysical.2,?_⟩
  intro Is hi
  exact native_joint_counter_ranges _ _ _ _ _ resolve ws Is hws hreceipt hn hg
    (by simp only [List.length_map];omega) hi

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

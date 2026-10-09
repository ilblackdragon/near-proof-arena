import ZkFormal.NearV3.Rcpt.Candidates.UpsCellPayload

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

theorem keyEdges3_arity (n : Nat) (k : List Nat) (e : Msg)
    (h : e∈keyEdges3 n k) : e.length=6 := by
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp h
  rfl

theorem edgesOf3_arity (n : Nat) (s : NodeS3) (e : Msg)
    (h : e∈edgesOf3 n s) : e.length=6 := by
  cases hv : s.v with
  | leaf k v m =>
    simp only [edgesOf3,hv,List.mem_append] at h
    rcases h with (h|h)|h
    · exact keyEdges3_arity n k e h
    · cases v <;> simp_all
    · simp only [List.mem_singleton] at h
      rw [h];rfl
  | ext k c m =>
    simp only [edgesOf3,hv,List.mem_append] at h
    rcases h with h|h
    · exact keyEdges3_arity n k.dropLast e h
    · cases c <;> cases hh : k.getLast? <;> simp_all
  | branch v cs m =>
    simp only [edgesOf3,hv,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨⟨c,j⟩,_,hh⟩:=List.mem_filterMap.mp h
      cases c <;> simp_all
      rw [←hh];rfl
    · cases v with
      | none=>simp at h
      | some v=>cases v <;> simp_all

theorem provider_edge_arity (hs : List HeadE) (ss : List NodeS3) (e : Msg)
    (h : e∈headEdgeKeys hs++nodeEdgeKeys ss) : e.length=6 := by
  rcases List.mem_append.mp h with h|h
  · obtain ⟨a,_,rfl⟩:=List.mem_map.mp h
    rfl
  · obtain ⟨⟨s,n⟩,_,he⟩:=List.mem_flatMap.mp h
    exact edgesOf3_arity n s e he

theorem native_ups_edge_arity (pairs : List (PTrie×PTrie)) (run : TreeRun)
    (I : Render.UpsInst) (ho : InstOk I) (hp : ExactNativeWalkProviders pairs run I)
    (hci : I.ci=run.terminal.ix) (t : Nat) (ht : t<4) (hm : (step I t).mode≤1) :
    (step I t).e.length=6 :=
  provider_edge_arity _ _ _ (native_ups_active_edges pairs run I ho hp hci t ht hm)

theorem native_synced_edge_cells (pairs : List (PTrie×PTrie)) (run : TreeRun)
    (I : Render.UpsInst) (ho : InstOk I) (hp : ExactNativeWalkProviders pairs run I)
    (hci : I.ci=run.terminal.ix) (t : Nat) (ht : t<4) (hm : (step I t).mode≤1)
    (sd : Bool) :
    upsEdgeCells (syncUps I) t sd=
      ((step I t).e++[(step I t).u+(if sd then 1 else 0)]).map (fun (n : Nat)=>(n:Int)) :=
  synced_edge_cells I t sd hm (native_ups_edge_arity pairs run I ho hp hci t ht hm)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

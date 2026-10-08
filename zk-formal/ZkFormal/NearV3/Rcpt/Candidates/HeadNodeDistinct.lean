import ZkFormal.NearV3.Rcpt.Candidates.NativeProviderCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem keyEdges3_symbol (n : Nat) (k : List Nat) (hk : ∀x∈k,x<16)
    (e : Msg) (h : e∈keyEdges3 n k) : e.getD 2 0<17 := by
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
  have hi':=List.mem_range.mp hi
  have hb:=hk k[i] (List.getElem_mem hi')
  simp only [List.getD_cons_succ,List.getD_cons_zero]
  rw [←List.getElem_eq_getD (h:=hi') 0]
  omega

theorem node_edge_not_start (n : Nat) (s : NodeS3) (hw : s.v.wf)
    (e : Msg) (h : e∈edgesOf3 n s) : e.getD 2 0≠SYM_START := by
  have hb : e.getD 2 0<17 := by
    unfold edgesOf3 at h
    cases hv : s.v with
    | leaf k v m =>
      rw [hv] at h hw
      dsimp only at h
      simp only [List.mem_append] at h
      rcases h with (h|h)|h
      · exact keyEdges3_symbol n k hw.1 e h
      · cases v <;> simp_all [SYM_END]
      · simp only [List.mem_singleton] at h;subst e;simp [SYM_END]
    | ext k c m =>
      rw [hv] at h hw
      dsimp only at h
      simp only [List.mem_append] at h
      rcases h with h|h
      · exact keyEdges3_symbol n k.dropLast (fun x hx=>hw.1 x ((List.dropLast_sublist k).subset hx)) e h
      · cases c <;> cases hh : k.getLast? <;> simp [hh] at h
        all_goals subst e; have hx:=hw.1 _ (List.mem_of_getLast? hh);simpa using Nat.lt_trans hx (by decide : 16<17)
    | branch v cs m =>
      rw [hv] at h hw
      dsimp only at h
      simp only [List.mem_append] at h
      rcases h with h|h
      · obtain ⟨⟨c,j⟩,hm,he⟩:=List.mem_filterMap.mp h
        have hj:=List.mem_range.mp (List.of_mem_zip hm).2
        have hl:=hw.1
        cases c <;> simp only [Option.some.injEq,reduceCtorEq] at he
        subst e;simp only [List.getD_cons_succ,List.getD_cons_zero];omega
      · cases v with
        | none=>simp at h
        | some v=>cases v <;> simp_all [SYM_END]
  simp only [SYM_START]
  omega

theorem forest_heads_tau : ∀(pairs : List (PTrie×PTrie))(tau n : Nat),
    (forestWalkHeads tau n pairs).map HeadE.tau=List.range' tau pairs.length
  | [],_,_=>rfl
  | (pre,post)::ps,tau,n=>by simp [forestWalkHeads,forest_heads_tau ps,List.range'_succ]

theorem head_keys_distinct (hs : List HeadE) (h : (hs.map HeadE.tau).Nodup) :
    (headEdgeKeys hs).Nodup := by
  unfold headEdgeKeys List.Nodup
  rw [List.pairwise_map]
  change List.Pairwise (·≠·) (hs.map HeadE.tau) at h
  rw [List.pairwise_map] at h
  apply h.imp_of_mem
  intro a b ha hb hab he
  have hh:=congrArg (fun e : Msg=>e.getD 1 0) he
  simp only [headEdgeKey,List.getD_cons_succ,List.getD_cons_zero] at hh
  exact hab hh

theorem forest_head_keys_distinct (pairs : List (PTrie×PTrie)) (tau n : Nat) :
    (headEdgeKeys (forestWalkHeads tau n pairs)).Nodup := by
  apply head_keys_distinct
  rw [forest_heads_tau]
  exact List.nodup_range'

theorem head_node_keys_distinct (hs : List HeadE) (ss : List NodeS3)
    (hh : (hs.map HeadE.tau).Nodup) (hw : ∀s∈ss,s.v.wf) :
    (headEdgeKeys hs++nodeEdgeKeys ss).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨head_keys_distinct hs hh,nodeEdgeKeys_distinct ss,?_⟩
  intro a ha b hb he
  obtain ⟨hd,_,rfl⟩:=List.mem_map.mp ha
  obtain ⟨⟨s,n⟩,hm,hb⟩:=List.mem_flatMap.mp hb
  have hn:=node_edge_not_start n s (hw s (List.of_mem_zip hm).1) b hb
  apply hn
  rw [←he]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

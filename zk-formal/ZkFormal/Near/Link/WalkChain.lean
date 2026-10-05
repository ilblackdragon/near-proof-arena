import ZkFormal.Near.Link.WalkEdge
import ZkFormal.Near.Link.Trie

/-!
# ZkFormal.Near.Link.WalkChain — `edge_provided`
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem flatMap_map_eq {α β γ : Type} (s : α → List β) (G : β → γ) :
    ∀ (l : List α), l.flatMap (fun a => (s a).map G) = (l.flatMap s).map G
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.flatMap_cons, List.map_append, flatMap_map_eq s G l]

theorem walkSends_edge (ws : List WalkV) : walkSends ws B_EDGE =
    (ws.flatMap (·.steps)).map fun st => st.1 ++ [st.2 + 1] := by
  simp only [walkSends, if_pos rfl]
  rw [← flatMap_map_eq]; rfl

theorem walkRecvs_edge (ws : List WalkV) : walkRecvs ws B_EDGE =
    (ws.flatMap (·.steps)).map fun st => st.1 ++ [st.2] := by
  simp only [walkRecvs, if_pos rfl]
  rw [← flatMap_map_eq]; rfl

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem klen_lt {n : Nat} (hn : n < vs.length) : vs[n].v.klen < 512 := by
  have hb := (node_bytes h hn).1
  generalize hv : vs[n].v = v at hb
  cases v with
  | leaf k s m =>
    have := hpN_len_lt (k := k) (b := true) hb (by simp [NodeV.ser, u32r])
    have := key_le_hexPrefix k true
    simp only [NodeV.klen]; omega
  | ext k kid m =>
    have := hpN_len_lt (k := k) (b := false) hb (by simp [NodeV.ser, u32r])
    have := key_le_hexPrefix k false
    simp only [NodeV.klen]; omega
  | branch => simp [NodeV.klen]

theorem provider_canon {n : Nat} (hn : n < vs.length) : ∀ e ∈ edgesOf n vs[n], e.length = 5 ∧ Canon e := by
  have hlt := vs_length_lt h.node
  have hs := List.getElem_mem hn
  exact edges_canon n vs[n] (by omega) (h.node.canon _ hs) (h.node.small _ hs).2.1
    (by have := klen_lt h hn; unfold P; omega) (h.node.wf _ hs)

/-- **Every edge a walk uses is provided by a node.** -/
theorem edge_provided {w : WalkV} (hw : w ∈ ws) {st : Msg × Nat} (hst : st ∈ w.steps) :
    ∃ n, ∃ hn : n < vs.length, st.1 ∈ edgesOf n vs[n] := by
  apply Classical.byContradiction; intro hno
  have hno' : ∀ n (hn : n < vs.length), st.1 ∉ edgesOf n vs[n] := fun n hn he => hno ⟨n, hn, he⟩
  obtain ⟨-, hstep, -⟩ := h.walk.steps w hw
  obtain ⟨hl5, -⟩ := hstep st hst
  have hcan : Canon st.1 := h.walk.canon w hw st hst
  have hT := walk_steps_lt h
  have hsum := perm_sum (pick st.1.toFp) (perm h (b := B_EDGE) (by decide) (by decide))
  rw [List.map_map, List.map_map, nearSends_edge, nearRecvs_edge, List.map_append, List.map_append,
    List.sum_append, List.sum_append] at hsum
  -- node parts vanish
  have hnode : ∀ (f : NodeS × Nat → List Msg), (∀ p ∈ vs.zip (List.range vs.length), ∀ m ∈ f p,
      ∃ e' x, m = e' ++ [x] ∧ e'.length = 5 ∧ Canon e' ∧ e' ≠ st.1) →
      (((vs.zip (List.range vs.length)).flatMap f).map (pick st.1.toFp ∘ Msg.toFp)).sum = 0 := by
    intro f hf
    apply sum_zero
    intro m hm
    obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨e', x, rfl, h5, hc, hne⟩ := hf p hp m hm
    simp only [Function.comp]
    rw [pick_eq hcan hc hl5 h5, if_neg hne]
  have hz1 : ((nodeSends vs B_EDGE).map (pick st.1.toFp ∘ Msg.toFp)).sum = 0 := by
    simp only [nodeSends, show B_EDGE ≠ B_BYTES from by decide, show B_EDGE ≠ B_PARENT from by decide,
      if_false, if_true]
    apply hnode
    rintro ⟨s, n⟩ hp m hm
    obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hm
    obtain ⟨h5, hc⟩ := provider_canon h hn e' he'
    exact ⟨e', 0, rfl, h5, hc, fun he => hno' _ hn (he ▸ he')⟩
  have hz2 : ((nodeRecvs vs (publicOf c) B_EDGE).map (pick st.1.toFp ∘ Msg.toFp)).sum = 0 := by
    simp only [nodeRecvs, show B_EDGE ≠ B_DIGEST from by decide, show B_EDGE ≠ B_PARENT from by decide,
      show B_EDGE ≠ B_VSLOT from by decide, if_false, if_true]
    apply hnode
    rintro ⟨s, n⟩ hp m hm
    obtain ⟨hn, rfl⟩ := mem_zip_range.mp hp
    obtain ⟨⟨e', u⟩, he', rfl⟩ := List.mem_map.mp hm
    have he'' := (List.of_mem_zip he').1
    obtain ⟨h5, hc⟩ := provider_canon h hn e' he''
    exact ⟨e', u, rfl, h5, hc, fun he => hno' _ hn (he ▸ he'')⟩
  rw [hz1, hz2, walkSends_edge, walkRecvs_edge, List.map_map, List.map_map] at hsum
  simp only [Nat.zero_add] at hsum
  -- walk parts
  have hT5 : ∀ s ∈ ws.flatMap (·.steps), s.1.length = 5 ∧ Canon s.1 ∧ s.2 < P := by
    intro s hs
    obtain ⟨w', hw', hs'⟩ := List.mem_flatMap.mp hs
    exact ⟨((h.walk.steps w' hw').2.1 s hs').1, h.walk.canon w' hw' s hs', ((h.walk.steps w' hw').2.1 s hs').2⟩
  have e1 : ((ws.flatMap (·.steps)).map ((pick st.1.toFp ∘ Msg.toFp) ∘ fun s => s.1 ++ [s.2 + 1])) =
      (ws.flatMap (·.steps)).map (fun s => if decide (s.1 = st.1) then (s.2 + 1) % P else 0) := by
    apply List.map_congr_left; intro s hs
    obtain ⟨h5, hc, -⟩ := hT5 s hs
    simp only [Function.comp, pick_eq hcan hc hl5 h5, decide_eq_true_eq]
  have e2 : ((ws.flatMap (·.steps)).map ((pick st.1.toFp ∘ Msg.toFp) ∘ fun s => s.1 ++ [s.2])) =
      (ws.flatMap (·.steps)).map (fun s => if decide (s.1 = st.1) then s.2 else 0) := by
    apply List.map_congr_left; intro s hs
    obtain ⟨h5, hc, hu⟩ := hT5 s hs
    simp only [Function.comp, pick_eq hcan hc hl5 h5, decide_eq_true_eq, Nat.mod_eq_of_lt hu]
  rw [e1, e2] at hsum
  have hmod := sum_mod_succ (fun s : Msg × Nat => decide (s.1 = st.1)) (·.2) (ws.flatMap (·.steps))
  rw [hsum] at hmod
  have hc1 := count_pos (fun s : Msg × Nat => decide (s.1 = st.1))
    (List.mem_flatMap.mpr ⟨w, hw, hst⟩) (by simp)
  have hc2 := count_le (fun s : Msg × Nat => decide (s.1 = st.1)) (ws.flatMap (·.steps))
  generalize ((ws.flatMap (·.steps)).map fun s => if decide (s.1 = st.1) then s.2 else 0).sum = A at hmod
  generalize ((ws.flatMap (·.steps)).map fun s => if decide (s.1 = st.1) then 1 else 0).sum = C
    at hmod hc1 hc2
  have hAP := Nat.mod_lt A (show 0 < P by unfold P; omega)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show C < P by omega)] at hmod
  generalize A % P = a at hmod hAP
  rcases Nat.lt_or_ge (a + C) P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hmod; omega
  · have h2 : a + C - P < P := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2] at hmod; omega

end Hyp

end Link

end ZkFormal.Near

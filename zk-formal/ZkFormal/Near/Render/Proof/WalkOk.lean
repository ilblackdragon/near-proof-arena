import ZkFormal.Near.Render.Proof.AcctFacts

/-!
# ZkFormal.Near.Render.Proof.WalkOk — the generator's walks succeed

Under `Good`, `walkOf I rc` succeeds for every receipt, consuming
`keySyms rc` and ending at the receipt's slot: the generator's walk is the
spec walk (`WalkTo`) with the `EPS` steps collapsed through `resF`
(`norm`: an extension whose key is consumed stands for its child's target).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

theorem nodup_len_le : ∀ (N : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < N) → l.length ≤ N
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x (by simp)) (by omega)
  | N + 1, l, hl, h => by
    have ih := nodup_len_le N (l.erase N) (hl.erase N) (fun x hx => by
      rw [hl.mem_erase_iff] at hx; have := h x hx.2; omega)
    rw [List.length_erase] at ih
    split at ih <;> omega

section res
variable {ns : List NodeRec} (hs : TreeShape ns)
include hs

/-- An unstable `resF` reveals a chain of `f + 1` nodes of increasing depth. -/
theorem res_chain (d : Nat → Nat) (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) : ∀ f n, n < ns.length →
    resF ns.toArray f n ≠ resF ns.toArray (f + 1) n →
    ∃ l : List Nat, l.length = f + 1 ∧ (∀ x ∈ l, x < ns.length) ∧ (∀ x ∈ l, d n ≤ d x) ∧
      l.Pairwise (fun a b => d a < d b)
  | 0, n, hn, _ => ⟨[n], rfl, by simp [hn], by simp, by simp⟩
  | f + 1, n, hn, hne => by
    simp only [resF] at hne
    split at hne
    · rename_i k c m heq
      have hget : ns[n]? = some (.ext [] (.node c) m) := by
        rw [List.getElem?_eq_getElem hn]; simp [Array.getD_eq_getD_getElem?, hn] at heq; rw [heq]
      have hch : ChildOf ns n c := ⟨_, hget, by simp [NodeRec.kids]⟩
      have hc := (hs.child_range n c hch).2
      obtain ⟨l, h1, h2, h3, h4⟩ := res_chain d hd f c hc hne
      have hdc := hd n c hch
      refine ⟨n :: l, by simp [h1], ?_, ?_, ?_⟩
      · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · exact hn
        · exact h2 x hx
      · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · exact Nat.le_refl _
        · have := h3 x hx; omega
      · refine List.pairwise_cons.2 ⟨fun x hx => ?_, h4⟩
        have := h3 x hx; omega
    · exact absurd rfl hne

theorem res_stable {n : Nat} : resF ns.toArray ns.length n = resF ns.toArray (ns.length + 1) n := by
  by_cases hn : n < ns.length
  · obtain ⟨d, _, hd⟩ := hs.depth
    apply Classical.byContradiction; intro hne
    obtain ⟨l, h1, h2, _, h4⟩ := res_chain hs d hd _ n hn hne
    have hnd : l.Nodup := h4.imp fun h h' => by rw [h'] at h; omega
    have := nodup_len_le _ l hnd h2
    omega
  · have hg : ns.toArray.getD n (.branch none [] 0) = .branch none [] 0 := by
      simp [Array.getD_eq_getD_getElem?, hn]
    cases h : ns.length with
    | zero => simp only [resF, hg, Nat.zero_add]
    | succ N => simp only [resF, hg]

/-- The walk target. -/
abbrev R (ns : List NodeRec) (n : Nat) : Nat := resF ns.toArray (ns.length + 1) n

theorem R_eext {n c m : Nat} (h : ns[n]? = some (.ext [] (.node c) m)) : R ns n = R ns c := by
  have hn : n < ns.length := by
    rcases Nat.lt_or_ge n ns.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hg : ns.toArray.getD n (.branch none [] 0) = .ext [] (.node c) m := by
    simp [Array.getD_eq_getD_getElem?, hn]; rw [List.getElem?_eq_getElem hn] at h; simpa using h
  simp only [R, resF, hg]
  exact res_stable hs

end res

theorem R_other {ns : List NodeRec} {n : Nat} (h : ∀ c m, ns[n]? ≠ some (.ext [] (.node c) m)) : R ns n = n := by
  simp only [R, resF]
  split
  · rename_i k c m heq
    exfalso
    by_cases hn : n < ns.length
    · apply h c m; rw [List.getElem?_eq_getElem hn]; simp [Array.getD_eq_getD_getElem?, hn] at heq; rw [heq]
    · simp [Array.getD_eq_getD_getElem?, hn] at heq
  · rfl

/-! ## Simulation -/

/-- Generator state of a spec state. -/
def norm (ns : List NodeRec) (s : Nat × Nat) : Nat × Nat :=
  match ns[s.1]? with
  | some (.ext k (.node c) _) => if s.2 = k.length then (R ns c, 0) else s
  | _ => s

/-- An extension whose key is consumed but whose child is not revealed. -/
def Dead (ns : List NodeRec) (s : Nat × Nat) : Prop :=
  ∃ k kid m, ns[s.1]? = some (.ext k kid m) ∧ s.2 = k.length ∧ ∀ c, kid ≠ .node c

section sim
variable {c : Claim} {e : Ext}

theorem info_res (x : Nat) : (mkInfo c e).res.getD x x = R e.ns x := by
  by_cases hx : x < e.ns.length
  · simp [mkInfo, Array.getD_eq_getD_getElem?, hx, R]
  · have : resF e.ns.toArray (e.ns.length + 1) x = x := by
      simp only [resF]
      have hg : e.ns.toArray.getD x (.branch none [] 0) = .branch none [] 0 := by
        simp [Array.getD_eq_getD_getElem?, hx]
      simp only [hg]
    simp [mkInfo, Array.getD_eq_getD_getElem?, hx, R, this]

theorem info_res' (x : Nat) : (mkInfo c e).res[x]?.getD x = R e.ns x := by
  rw [← Array.getD_eq_getD_getElem?]; exact info_res x

theorem info_get (x : Nat) : (mkInfo c e).ns[x]? = e.ns[x]? := by simp [mkInfo]

variable (hs : TreeShape e.ns) (hwf : ∀ nr ∈ e.ns, nr.wf)
include hs

theorem norm_zero (n : Nat) : norm e.ns (n, 0) = (R e.ns n, 0) := by
  unfold norm
  split
  · rename_i k c' m h
    split
    · rename_i hk
      have : k = [] := List.eq_nil_of_length_eq_zero hk.symm
      subst this; rw [R_eext hs h]
    · rename_i hk
      rw [R_other]; intro c'' m' h'; rw [h] at h'; simp at h'; exact hk (by rw [h'.1]; rfl)
  · rename_i h
    rw [R_other]; intro c'' m' h'; exact h _ _ _ h'

include hwf

theorem step_sim {s s' : Nat × Nat} {x : Nat} (h : Step e.ns s x s') (hx : x ≠ SYM_EPS)
    (hnd : ¬ Dead e.ns s') : norm e.ns s = s ∧ stepOf (mkInfo c e) s.1 s.2 x = .ok (norm e.ns s') := by
  cases h with
  | @key n i x nr h1 h2 h3 =>
    have hx16 : x < 16 := by
      have hw := hwf nr (List.mem_of_getElem? h1)
      have hk : nr.key.all (· < 16) = true := by
        cases nr <;> simp_all [NodeRec.wf, NodeRec.key, nibblesOk]
      exact of_decide_eq_true (List.all_eq_true.1 hk x (List.mem_of_getElem? h3))
    cases nr with
    | leaf k v mem =>
      simp only [NodeRec.key] at h3
      simp [norm, stepOf, info_get, h1, hx16, h3]
    | ext k kid mem =>
      simp only [NodeRec.key] at h3
      have hi : i < k.length := by
        rcases Nat.lt_or_ge i k.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at h3; cases h3
      refine ⟨?_, ?_⟩
      · cases kid <;> simp [norm, h1, Nat.ne_of_lt hi]
      · simp only [stepOf, info_get, h1, hx16, h3, and_self, if_true]
        by_cases hl : i + 1 = k.length
        · simp only [hl, if_true]
          cases kid with
          | node c' => simp [norm, h1, hl, info_res']
          | none => exact absurd ⟨k, _, mem, h1, (show i + 1 = k.length from hl), fun _ h => by cases h⟩ hnd
          | hash hh => exact absurd ⟨k, _, mem, h1, (show i + 1 = k.length from hl), fun _ h => by cases h⟩ hnd
        · simp only [hl, if_false]
          cases kid <;> simp [norm, h1, hl]
    | branch v kids mem => simp at h2
  | eps h1 => exact absurd rfl hx
  | @child n j c' mem v kids h1 h2 =>
    have hj : x < 16 := by
      have hw := hwf _ (List.mem_of_getElem? h1)
      simp only [NodeRec.wf] at hw
      rcases Nat.lt_or_ge x 16 with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at h2; cases h2
    refine ⟨by simp [norm, h1], ?_⟩
    rw [norm_zero hs]
    simp [stepOf, info_get, h1, hj, h2, info_res']
  | @endLeaf n mem k h1 =>
    refine ⟨by simp [norm, h1], ?_⟩
    simp [stepOf, info_get, h1, norm, SYM_END]
  | @endBranch n mem kids h1 =>
    refine ⟨by simp [norm, h1], ?_⟩
    simp [stepOf, info_get, h1, norm, SYM_END]

end sim

theorem dead_stuck {ns : List NodeRec} {s u : Nat × Nat} {y : Nat} (hd : Dead ns s) (h : Step ns s y u) : False := by
  obtain ⟨k, kid, m, h1, h2, h3⟩ := hd
  cases h with
  | key g1 g2 g3 =>
    rw [h1] at g1; cases g1
    simp only [NodeRec.key] at g3
    simp only at h2; rw [h2, List.getElem?_eq_none (Nat.le_refl _)] at g3; cases g3
  | eps g1 => rw [h1] at g1; cases g1; exact h3 _ rfl
  | child g1 => rw [h1] at g1; cases g1
  | endLeaf g1 => rw [h1] at g1; cases g1
  | endBranch g1 => rw [h1] at g1; cases g1

theorem not_dead {ns : List NodeRec} {s t kk : Nat × Nat} {key : List Nat} (hw : Walk ns s key t)
    (he : Step ns t SYM_END kk) : ¬ Dead ns s := by
  intro hd
  cases hw with
  | nil => exact dead_stuck hd he
  | eps h _ => exact dead_stuck hd h
  | sym _ h _ => exact dead_stuck hd h

theorem end_target {ns : List NodeRec} (hwf : ∀ nr ∈ ns, nr.wf) {t : Nat × Nat} {k : Nat}
    (he : Step ns t SYM_END (k, 0)) : ¬ Dead ns (k, 0) ∧ norm ns (k, 0) = (k, 0) := by
  cases he with
  | child g1 g2 =>
    have hw := hwf _ (List.mem_of_getElem? g1)
    simp only [NodeRec.wf] at hw
    rw [List.getElem?_eq_none (by simp [SYM_END]; omega)] at g2; cases g2
  | endLeaf g1 =>
    refine ⟨(fun ⟨k', kid, m, h1, _, _⟩ => by rw [g1] at h1; cases h1), ?_⟩
    simp [norm, g1]
  | endBranch g1 =>
    refine ⟨(fun ⟨k', kid, m, h1, _, _⟩ => by rw [g1] at h1; cases h1), ?_⟩
    simp [norm, g1]

theorem key_lt16 {ns : List NodeRec} (hwf : ∀ nr ∈ ns, nr.wf) {n i x : Nat} {nr : NodeRec}
    (g1 : ns[n]? = some nr) (g3 : nr.key[i]? = some x) : x < 16 := by
  have hw := hwf nr (List.mem_of_getElem? g1)
  have hk : nr.key.all (· < 16) = true := by
    cases nr <;> simp_all [NodeRec.wf, NodeRec.key, nibblesOk]
  exact of_decide_eq_true (List.all_eq_true.1 hk x (List.mem_of_getElem? g3))

section sim2
variable {c : Claim} {e : Ext} (hs : TreeShape e.ns) (hwf : ∀ nr ∈ e.ns, nr.wf)
include hs hwf

/-- **Simulation**: the generator follows the spec walk. -/
theorem sim {s t : Nat × Nat} {key : List Nat} {k : Nat} (hw : Walk e.ns s key t)
    (he : Step e.ns t SYM_END (k, 0)) (hkey : ∀ x ∈ key, x < 16) : ∀ tt, ∃ rest,
    walkFrom (mkInfo c e) (norm e.ns s) (key ++ [SYM_END]) tt = .ok rest ∧
      (rest.getLast?.map fun st => st.edge.getD 3 0) = some k := by
  induction hw with
  | nil =>
    intro tt
    obtain ⟨hnd, hn⟩ := end_target hwf he
    obtain ⟨h1, h2⟩ := step_sim (c := c) hs hwf he (by decide) hnd
    rw [hn] at h2
    simp only [List.nil_append, walkFrom, h1, h2]
    exact ⟨_, rfl, rfl⟩
  | @eps s0 s' t0 key0 hstep _ ih =>
    intro tt
    have : norm e.ns s0 = norm e.ns s' := by
      cases hstep with
      | eps g1 => rw [norm_zero hs]; simp [norm, g1]
      | key g1 g2 g3 => exact absurd (key_lt16 hwf g1 g3) (by simp [SYM_EPS])
      | child g1 g2 =>
        have hw := hwf _ (List.mem_of_getElem? g1)
        simp only [NodeRec.wf] at hw
        rw [List.getElem?_eq_none (by simp [SYM_EPS]; omega)] at g2; cases g2
    rw [this]; exact ih he hkey tt
  | @sym s0 s' t0 x key0 hx hstep hw' ih =>
    intro tt
    obtain ⟨h1, h2⟩ := step_sim (c := c) hs hwf hstep (by simp [SYM_EPS]; omega) (not_dead hw' he)
    obtain ⟨rest, hr1, hr2⟩ := ih he (fun y hy => hkey y (by simp [hy])) (tt + 1)
    have hne : rest ≠ [] := by rintro rfl; simp at hr2
    refine ⟨⟨some tt, x, [s0.1, s0.2, x, (norm e.ns s').1, (norm e.ns s').2], decide (x = SYM_END)⟩ :: rest,
      ?_, ?_⟩
    · simp only [List.cons_append, walkFrom, h1, h2, bind, Except.bind, hr1]; rfl
    · rw [List.getLast?_cons, ← hr2]
      cases h : rest.getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h; exact absurd h hne
      | some st => simp

end sim2

theorem nibbles_lt : ∀ (b : Bytes), ∀ x ∈ nibbles b, x < 16
  | [], x, h => by simp [nibbles] at h
  | y :: b, x, h => by
    simp only [nibbles, List.mem_cons] at h
    have := y.toNat_lt
    rcases h with rfl | rfl | h
    · omega
    · omega
    · exact nibbles_lt b x h

/-- **The walk of every receipt succeeds** and ends at its slot. -/
theorem walkOf_ok {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < e.rs.length) :
    ∃ rest, walkOf (mkInfo c e) (e.rc r) =
      .ok (⟨none, SYM_START, [0, 0, SYM_START, R e.ns 0, 0], false⟩ :: rest) ∧
      walkFrom (mkInfo c e) (R e.ns 0, 0) (keySyms (e.rc r)) 0 = .ok rest ∧
      (rest.getLast?.map fun st => st.edge.getD 3 0) = some (e.slot r) := by
  obtain ⟨s, hw, he⟩ := hg.walks r hr
  obtain ⟨rest, h1, h2⟩ := sim hg.shape hg.nodes_wf hw he (fun x hx => nibbles_lt _ x hx) 0
  rw [norm_zero hg.shape] at h1
  refine ⟨rest, ?_, h1, h2⟩
  simp only [walkOf, info_res, keySyms, h1]
  rfl

end ZkFormal.Near.Render

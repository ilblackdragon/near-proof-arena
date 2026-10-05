import ZkFormal.Near.Render.Proof.BusFinal
import ZkFormal.Near.Render.Proof.WalkTraffic

/-!
# ZkFormal.Near.Render.Proof.BusEdge — `EdgeBusStmt`

`node` offers each edge `e` once (send `(e, 0)`, receive `(e, uses e)`), the
walk steps use edges with chained counters (receive `(e, u)`, send
`(e, u + 1)`, `u` = earlier uses of `e`).  Balance holds as soon as the offered
edges are distinct and every step's edge is offered (`chain_perm`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusEdge

/-! ## The counting permutation -/

/-- Earlier occurrences of the element at position `j`. -/
def before (W : List (List Nat)) (j : Nat) : Nat := (W.take j).count (W.getD j [])

def sendsW (W : List (List Nat)) : List (List Nat) := (List.range W.length).map fun j => W.getD j [] ++ [before W j + 1]
def recvsW (W : List (List Nat)) : List (List Nat) := (List.range W.length).map fun j => W.getD j [] ++ [before W j]

theorem snoc_map (W : List (List Nat)) (x : List Nat) (f : List (List Nat) → Nat → List Nat)
    (hf : ∀ j, j < W.length → f (W ++ [x]) j = f W j) :
    (List.range (W ++ [x]).length).map (f (W ++ [x])) =
      (List.range W.length).map (f W) ++ [f (W ++ [x]) W.length] := by
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  apply List.map_congr_left; intro j hj; exact hf j (List.mem_range.1 hj)

theorem getD_snoc_lt {W : List (List Nat)} {x : List Nat} {j : Nat} (h : j < W.length) :
    (W ++ [x]).getD j [] = W.getD j [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem before_snoc_lt {W : List (List Nat)} {x : List Nat} {j : Nat} (h : j < W.length) :
    before (W ++ [x]) j = before W j := by
  simp only [before, getD_snoc_lt h, List.take_append_of_le_length (Nat.le_of_lt h)]

theorem before_snoc (W : List (List Nat)) (x : List Nat) : before (W ++ [x]) W.length = W.count x := by
  simp [before, List.getD_eq_getElem?_getD]

theorem sendsW_snoc (W : List (List Nat)) (x : List Nat) : sendsW (W ++ [x]) = sendsW W ++ [x ++ [W.count x + 1]] := by
  unfold sendsW
  rw [snoc_map W x (fun W j => W.getD j [] ++ [before W j + 1])
    (fun j hj => by simp only [getD_snoc_lt hj, before_snoc_lt hj]), before_snoc]
  simp [List.getD_eq_getElem?_getD]

theorem recvsW_snoc (W : List (List Nat)) (x : List Nat) : recvsW (W ++ [x]) = recvsW W ++ [x ++ [W.count x]] := by
  unfold recvsW
  rw [snoc_map W x (fun W j => W.getD j [] ++ [before W j])
    (fun j hj => by simp only [getD_snoc_lt hj, before_snoc_lt hj]), before_snoc]
  simp [List.getD_eq_getElem?_getD]

/-- **Chained counters balance.** -/
theorem chain_perm (E : List (List Nat)) (hE : E.Nodup) : ∀ W : List (List Nat), (∀ x ∈ W, x ∈ E) →
    (E.map (· ++ [0]) ++ sendsW W).Perm (E.map (fun e => e ++ [W.count e]) ++ recvsW W) := by
  intro W0
  suffices h : ∀ L : List (List Nat), let W := L.reverse; (∀ x ∈ W, x ∈ E) →
      (E.map (· ++ [0]) ++ sendsW W).Perm (E.map (fun e => e ++ [W.count e]) ++ recvsW W) by
    simpa using h W0.reverse
  intro L
  induction L with
  | nil => intro W _; simp [W, sendsW, recvsW]
  | cons x L ih =>
    intro W hW
    simp only [W, List.reverse_cons] at hW ⊢
    generalize L.reverse = W at ih hW ⊢
    have ih' := ih (fun y hy => hW y (by simp [hy]))
    rw [sendsW_snoc, recvsW_snoc, ← List.append_assoc]
    refine (ih'.append_right _).trans ?_
    obtain ⟨A, B, hAB⟩ := List.append_of_mem (hW x (by simp))
    subst hAB
    have hnd := hE
    rw [List.nodup_append] at hnd
    have hxA : x ∉ A := fun h => hnd.2.2 x h x (by simp) rfl
    have hxB : x ∉ B := (List.nodup_cons.1 hnd.2.1).1
    have hA : A.map (fun e => e ++ [(W ++ [x]).count e]) = A.map (fun e => e ++ [W.count e]) := by
      apply List.map_congr_left; intro e he
      have : x ≠ e := fun h => hxA (h ▸ he)
      simp [List.count_append, this]
    have hB : B.map (fun e => e ++ [(W ++ [x]).count e]) = B.map (fun e => e ++ [W.count e]) := by
      apply List.map_congr_left; intro e he
      have : x ≠ e := fun h => hxB (h ▸ he)
      simp [List.count_append, this]
    have hx : (W ++ [x]).count x = W.count x + 1 := by simp [List.count_append]
    simp only [List.map_append, List.map_cons, hA, hB, hx, List.append_assoc, List.cons_append]
    refine List.perm_iff_count.2 (fun a => ?_)
    simp only [List.count_append, List.count_cons]
    omega

/-! ## Use counts -/

theorem foldl_ins (e : Edge) : ∀ (l : List WStep) (m : Std.HashMap Edge Nat),
    (l.foldl (fun m s => m.insert s.edge (m.getD s.edge 0 + 1)) m).getD e 0 =
      m.getD e 0 + (l.map (·.edge)).count e
  | [], m => by simp
  | s :: l, m => by
    rw [List.foldl_cons, foldl_ins e l, Std.HashMap.getD_insert, List.map_cons, List.count_cons]
    by_cases h : s.edge = e
    · subst h; simp; omega
    · have : (s.edge == e) = false := by simpa using h
      simp [this]

theorem foldl_ins2 (e : Edge) : ∀ (ws : List (List WStep)) (m : Std.HashMap Edge Nat),
    (ws.foldl (fun m w => w.foldl (fun m s => m.insert s.edge (m.getD s.edge 0 + 1)) m) m).getD e 0 =
      m.getD e 0 + (ws.flatMap fun w => w.map (·.edge)).count e
  | [], m => by simp
  | w :: ws, m => by
    rw [List.foldl_cons, foldl_ins2 e ws, foldl_ins e w, List.flatMap_cons, List.count_append]; omega

/-- The edges of the walk steps, table order. -/
def wEdges (ws : List (List WStep)) : List Edge := ws.flatMap fun w => w.map (·.edge)

theorem edgeUses_getD (ws : List (List WStep)) (e : Edge) : (edgeUses ws).getD e 0 = (wEdges ws).count e := by
  simp [edgeUses, foldl_ins2, wEdges]

theorem stepsFrom_edges : ∀ (ws : List (List WStep)) (r : Nat),
    (stepsFrom ws r).map (·.2.edge) = wEdges ws
  | [], _ => rfl
  | w :: ws, r => by simp [stepsFrom, wEdges, stepsFrom_edges ws (r + 1)]

theorem useAtL_eq (ws : List (List WStep)) (q : Nat) (hq : q < (walkSteps ws).length) :
    useAtL (walkSteps ws) q = before (wEdges ws) q := by
  have hW : wEdges ws = (walkSteps ws).map (·.2.edge) := (stepsFrom_edges ws 0).symm
  have hget : (wEdges ws).getD q [] = ((walkSteps ws).getD q default).2.edge := by
    rw [hW]; simp [List.getD_eq_getElem?_getD, hq]
  simp only [useAtL, before, hget]
  rw [hW, ← List.map_take, List.count, List.countP_map, List.countP_eq_length_filter]
  rfl

/-- The walk side as `sendsW`/`recvsW` of the edge list. -/
theorem walk_side (ws : List (List WStep)) (g : Nat → Nat) :
    (walkViewsOf ws).flatMap (fun w => w.steps.map fun x => x.1 ++ [g x.2]) =
      (List.range (wEdges ws).length).map fun q => (wEdges ws).getD q [] ++ [g (before (wEdges ws) q)] := by
  have hlen : (wEdges ws).length = (ws.map List.length).sum := by
    rw [← stepsFrom_edges ws 0, List.length_map, stepsFrom_length]
  rw [hlen, ← flatMap_single (f := fun q => [(wEdges ws).getD q [] ++ [g (before (wEdges ws) q)]])
    (fun _ _ => rfl), range_chunks_var]
  simp only [walkViewsOf, List.flatMap_map, List.map_map]
  apply flatMap_congr'; intro r hr
  have hr' := List.mem_range.1 hr
  rw [← flatMap_single (fun _ _ => rfl)]
  apply flatMap_congr'; intro j hj
  have hj' := List.mem_range.1 hj
  have hq : walkOff ws r + j < (walkSteps ws).length := by
    rw [walkSteps, stepsFrom_length]; have := walkOff_add_le ws r hr'; omega
  have hst := stepsFrom_getD ws 0 r j hr' hj'
  have hus : (usesL (walkSteps ws)).getD (walkOff ws r + j) 0 = before (wEdges ws) (walkOff ws r + j) := by
    simp [usesL, List.getD_eq_getElem?_getD, hq, useAtL_eq ws _ hq]
  have he : (wEdges ws).getD (walkOff ws r + j) [] = ((ws.getD r []).getD j default).edge := by
    have hq' : walkOff ws r + j < (stepsFrom ws 0).length := hq
    rw [← stepsFrom_edges ws 0, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hq']
    simp only [Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq'] at hst
    simp only [Option.getD_some] at hst
    rw [hst]
  simp only [Function.comp_apply]
  rw [hus, he]

/-! ## The node side -/

/-- The offered edges, node order. -/
def nEdges (I : Info) (u : Std.HashMap Edge Nat) : List Edge :=
  (List.range I.ns.size).flatMap fun n => edgesOf n (nodeViewOf I u n)

theorem zip_map_self {α : Type} (f : List Nat → α) (g : List Nat → α → List Nat) :
    ∀ l : List (List Nat), (l.zip (l.map f)).map (fun x => g x.1 x.2) = l.map fun e => g e (f e)
  | [] => rfl
  | a :: l => by simp [zip_map_self f g l]

theorem node_sends (I : Info) (u : Std.HashMap Edge Nat) :
    ((nodeViewsOf I u).zip (List.range (nodeViewsOf I u).length)).flatMap
      (fun x => (edgesOf x.2 x.1).map (· ++ [0])) = (nEdges I u).map (· ++ [0]) := by
  simp only [nodeViewsOf, List.length_map, List.length_range, zip_range_map, List.flatMap_map, nEdges,
    List.map_flatMap]

theorem node_recvs (I : Info) (u : Std.HashMap Edge Nat) :
    ((nodeViewsOf I u).zip (List.range (nodeViewsOf I u).length)).flatMap
      (fun x => ((edgesOf x.2 x.1).zip x.1.uses).map fun y => y.1 ++ [y.2]) =
      (nEdges I u).map (fun e => e ++ [u.getD e 0]) := by
  simp only [nodeViewsOf, List.length_map, List.length_range, zip_range_map, List.flatMap_map, nEdges,
    List.map_flatMap]
  apply flatMap_congr'; intro n _
  exact zip_map_self (fun e => u.getD e 0) (fun a b => a ++ [b]) _

theorem cnt_append (l₁ l₂ : List (List Nat)) (m : List Fp) : cnt l₁ m + cnt l₂ m = cnt (l₁ ++ l₂) m := by
  simp [cnt, List.count_append]

/-! ## Offered edges are distinct -/

def KeysOk : NodeV → Prop
  | .leaf k _ _ => ∀ x ∈ k, x < 16
  | .ext k _ _ => ∀ x ∈ k, x < 16
  | .branch _ kids _ => kids.length ≤ 16

theorem keyEdges_facts (n : Nat) (k : List Nat) (hk : ∀ x ∈ k, x < 16) :
    (keyEdges n k).Pairwise (· ≠ ·) ∧
      ∀ x ∈ keyEdges n k, x.getD 2 0 < 16 ∧ x.getD 1 0 < k.length ∧ x.head? = some n := by
  refine ⟨?_, ?_⟩
  · simp only [keyEdges, List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h e => by simp at e; omega
  · intro x hx
    simp only [keyEdges, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨?_, by simpa using hi, rfl⟩
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact hk _ (by simp [List.getD_eq_getElem?_getD, hi])

theorem zip_range_pairwise {α : Type} : ∀ (l : List α) (k : Nat),
    (l.zip (List.range' k l.length)).Pairwise (fun a b => a.2 < b.2)
  | [], _ => by simp
  | a :: l, k => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.pairwise_cons]
    refine ⟨fun b hb => ?_, zip_range_pairwise l (k + 1)⟩
    have := (List.mem_range'.1 (List.of_mem_zip hb).2); omega

/-- Edges besides `START`. -/
def body (n : Nat) (s : NodeS) : List Edge :=
  match s.v with
  | .leaf k v _ =>
    keyEdges n k ++ (match v with | .touched _ _ => [[n, k.length, SYM_END, n, 0]] | _ => [])
  | .ext k kid _ =>
    keyEdges n (k.dropLast) ++
      (match kid, k.getLast? with
       | .node _ _ cr _ _, some x => [[n, k.length - 1, x, cr, 0]]
       | _, _ => [])
  | .branch v kids _ =>
    ((kids.zip (List.range kids.length)).filterMap fun
      | (.node _ _ cr _ _, j) => some [n, 0, j, cr, 0]
      | _ => none) ++
    (match v with | some (.touched _ _) => [[n, 0, SYM_END, n, 0]] | _ => [])

theorem edgesOf_eq (n : Nat) (s : NodeS) :
    edgesOf n s = (if n = 0 then [[0, 0, SYM_START, s.res, 0]] else []) ++ body n s := rfl

theorem body_facts (n : Nat) (s : NodeS) (hv : KeysOk s.v) :
    (body n s).Pairwise (· ≠ ·) ∧ ∀ x ∈ body n s, x.getD 2 0 ≤ 16 ∧ x.head? = some n := by
  unfold body
  split
  · rename_i k v _ hsv
    rw [hsv] at hv
    obtain ⟨p1, p2⟩ := keyEdges_facts n k hv
    refine ⟨List.pairwise_append.2 ⟨p1, ?_, ?_⟩, ?_⟩
    · split <;> simp
    · intro a ha b hb
      split at hb
      · simp at hb; subst hb; intro h; have := (p2 a ha).2.1; rw [h] at this; simp at this
      · simp at hb
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · have := p2 x hx; exact ⟨by omega, this.2.2⟩
      · split at hx
        · simp at hx; subst hx; simp [SYM_END]
        · simp at hx
  · rename_i k kid _ hsv
    rw [hsv] at hv
    obtain ⟨p1, p2⟩ := keyEdges_facts n k.dropLast (fun x hx => hv x ((List.dropLast_sublist k).subset hx))
    refine ⟨List.pairwise_append.2 ⟨p1, ?_, ?_⟩, ?_⟩
    · split <;> simp
    · intro a ha b hb
      split at hb
      · simp at hb; subst hb; intro h; have := (p2 a ha).2.1; rw [h] at this; simp at this
      · simp at hb
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · have := p2 x hx; exact ⟨by omega, this.2.2⟩
      · cases kid with
        | node c0 l0 cr p0 q0 =>
          cases hl : k.getLast? with
          | none => simp [hl] at hx
          | some x' =>
            simp [hl] at hx; subst hx
            have := hv x' (List.mem_of_getLast? hl)
            simp; omega
        | _ => simp at hx
  · rename_i v kids _ hsv
    rw [hsv] at hv
    have hz := zip_range_pairwise kids 0
    rw [← List.range_eq_range'] at hz
    have hlt : ∀ x ∈ (kids.zip (List.range kids.length)).filterMap (fun
        | (NKid.node _ _ cr _ _, j) => some [n, 0, j, cr, 0]
        | _ => none), x.getD 2 0 < 16 ∧ x.head? = some n := by
      intro x hx
      rw [List.mem_filterMap] at hx
      obtain ⟨⟨kd, j⟩, hm, hf⟩ := hx
      have hj := List.mem_range.1 (List.of_mem_zip hm).2
      have hv' : kids.length ≤ 16 := hv
      cases kd <;> simp at hf
      subst hf; simp; omega
    refine ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · refine (List.Pairwise.filterMap (S := fun a b => a.getD 2 0 < b.getD 2 0) _ ?_ hz).imp
        (fun h e => by rw [e] at h; omega)
      intro a a' haa b hb b' hb'
      split at hb
      · split at hb'
        · simp at hb hb'; subst hb hb'; simpa using haa
        · cases hb'
      · cases hb
    · split <;> simp
    · intro a ha b hb
      split at hb
      · simp at hb; subst hb; intro h; have := (hlt a ha).1; rw [h] at this; simp [SYM_END] at this
      · simp at hb
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · have := hlt x hx; exact ⟨by omega, this.2⟩
      · split at hx
        · simp at hx; subst hx; simp [SYM_END]
        · simp at hx

theorem edgesOf_facts (n : Nat) (s : NodeS) (hv : KeysOk s.v) :
    (edgesOf n s).Nodup ∧ ∀ x ∈ edgesOf n s, x.head? = some n := by
  obtain ⟨b1, b2⟩ := body_facts n s hv
  rw [edgesOf_eq]
  refine ⟨List.pairwise_append.2 ⟨by split <;> simp, b1, ?_⟩, ?_⟩
  · intro a ha b hb
    split at ha
    · simp at ha; subst ha; intro h; have := (b2 b hb).1; rw [← h] at this; simp [SYM_START] at this
    · simp at ha
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · split at hx
      · rename_i h0; simp at hx; subst hx h0; rfl
      · simp at hx
    · exact (b2 x hx).2

theorem nodeVOf_keys {I : Info} {n : Nat} {nr : NodeRec} (hw : nr.wf) : KeysOk (nodeVOf I n nr) := by
  cases nr with
  | leaf k v mem =>
    simp only [NodeRec.wf] at hw
    intro x hx; exact of_decide_eq_true (List.all_eq_true.1 hw.1 x hx)
  | ext k kid mem =>
    simp only [NodeRec.wf] at hw
    intro x hx; exact of_decide_eq_true (List.all_eq_true.1 hw.1 x hx)
  | branch v kids mem =>
    simp only [NodeRec.wf] at hw
    simp [KeysOk, nodeVOf, hw.1]

theorem nEdges_nodup {c : Claim} {e : Ext} (hg : Good c e) (u : Std.HashMap Edge Nat) :
    (nEdges (mkInfo c e) u).Nodup := by
  have hfacts : ∀ n, n < (mkInfo c e).ns.size → (edgesOf n (nodeViewOf (mkInfo c e) u n)).Nodup ∧
      ∀ x ∈ edgesOf n (nodeViewOf (mkInfo c e) u n), x.head? = some n := by
    intro n hn
    apply edgesOf_facts
    have hn' : n < e.ns.length := by simpa [mkInfo] using hn
    have hat : (mkInfo c e).nodeAt n = e.ns[n] := by
      simp [Info.nodeAt, mkInfo, Array.getD_eq_getD_getElem?, hn']
    simp only [nodeViewOf, hat]
    exact nodeVOf_keys (hg.nodes_wf _ (List.getElem_mem hn'))
  unfold nEdges List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun n hn => (hfacts n (List.mem_range.1 hn)).1, ?_⟩
  refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab x hx y hy hxy => ?_
  have h1 := (hfacts a (List.mem_range.1 ha)).2 x hx
  have h2 := (hfacts b (List.mem_range.1 hb)).2 y hy
  rw [hxy, h2] at h1; simp at h1; omega

theorem keyEdges_mem {n i x : Nat} {k : List Nat} (h : k[i]? = some x) : [n, i, x, n, i + 1] ∈ keyEdges n k := by
  have hi : i < k.length := by
    rcases Nat.lt_or_ge i k.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  simp only [keyEdges, List.mem_map, List.mem_range]
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, h]⟩

theorem stepOf_edge (I : Info) (u : Std.HashMap Edge Nat) {N i sym : Nat} {st' : Nat × Nat}
    (h : stepOf I N i sym = .ok st') :
    N < I.ns.size ∧ [N, i, sym, st'.1, st'.2] ∈ edgesOf N (nodeViewOf I u N) := by
  unfold stepOf at h
  cases hN : I.ns[N]? with
  | none => simp [hN] at h
  | some nr =>
    have hlt : N < I.ns.size := by
      rcases Nat.lt_or_ge N I.ns.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hN; cases hN
    have hat : I.nodeAt N = nr := by simp [Info.nodeAt, Array.getD_eq_getD_getElem?, hN]
    refine ⟨hlt, ?_⟩
    simp only [hN] at h
    simp only [nodeViewOf, edgesOf, hat]
    apply List.mem_append_right
    cases nr with
    | leaf k v mem =>
      simp only at h
      split at h
      · split at h
        · rename_i hk; cases h
          simp only [nodeVOf]; exact List.mem_append_left _ (keyEdges_mem hk)
        · cases h
      · split at h
        · rename_i hc; obtain ⟨h1, h2, h3⟩ := hc; cases h; subst h1 h2 h3
          simp [nodeVOf, nslotOf]
        · cases h
    | ext k kid mem =>
      simp only at h
      split at h
      · rename_i hc; obtain ⟨_, hk⟩ := hc
        have hi : i < k.length := by
          rcases Nat.lt_or_ge i k.length with h' | h'
          · exact h'
          · rw [List.getElem?_eq_none h'] at hk; cases hk
        split at h
        · rename_i hl
          split at h
          · rename_i c' _; cases h
            have hx : k.getLast? = some sym := by
              rw [List.getLast?_eq_getElem?, show k.length - 1 = i by omega, hk]
            simp only [nodeVOf, nkidOf, hx]
            simp [show k.length - 1 = i by omega]
          · cases h
        · rename_i hl; cases h
          simp only [nodeVOf]
          apply List.mem_append_left
          apply keyEdges_mem
          rw [List.getElem?_dropLast]; simp [hk]; omega
      · cases h
    | branch v kids mem =>
      simp only at h
      split at h
      · cases h
      · rename_i hi0
        have hi : i = 0 := by simpa using hi0
        subst hi
        split at h
        · split at h
          · rename_i c' hkid; cases h
            simp only [nodeVOf]
            apply List.mem_append_left
            rw [List.mem_filterMap]
            have hj : sym < kids.length := by
              rcases Nat.lt_or_ge sym kids.length with h' | h'
              · exact h'
              · rw [List.getElem?_eq_none h'] at hkid; cases hkid
            refine ⟨(nkidOf I (.node c'), sym), ?_, rfl⟩
            rw [List.mem_iff_getElem?]
            refine ⟨sym, ?_⟩
            have hk' : kids[sym] = .node c' := by simpa [List.getElem?_eq_getElem hj] using hkid
            simp [hk', hj]
          · cases h
        · split at h
          · rename_i hc; obtain ⟨h1, h2⟩ := hc; cases h; subst h1 h2
            simp [nodeVOf, nslotOf]
          · cases h

theorem mem_nEdges {I : Info} {u : Std.HashMap Edge Nat} {N : Nat} {x : Edge} (hN : N < I.ns.size)
    (h : x ∈ edgesOf N (nodeViewOf I u N)) : x ∈ nEdges I u :=
  List.mem_flatMap.2 ⟨N, List.mem_range.2 hN, h⟩

theorem walkFrom_mem (I : Info) (u : Std.HashMap Edge Nat) : ∀ (syms : List Nat) (st : Nat × Nat) (t : Nat)
    (rest : List WStep), walkFrom I st syms t = .ok rest →
    (∀ s ∈ rest, s.edge ∈ nEdges I u) ∧ (syms ≠ [] → st.1 < I.ns.size)
  | [], _, _, rest, h => by simp only [walkFrom] at h; cases h; simp
  | sym :: syms, st, t, rest, h => by
    simp only [walkFrom, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i st' hst
      split at h
      · cases h
      · rename_i rest' hrest
        cases h
        obtain ⟨h1, h2⟩ := stepOf_edge I u hst
        refine ⟨fun s hs => ?_, fun _ => h1⟩
        rcases List.mem_cons.1 hs with rfl | hs
        · exact mem_nEdges h1 h2
        · exact (walkFrom_mem I u syms st' (t + 1) rest' hrest).1 s hs

theorem wEdges_sub_of (I : Info) (u : Std.HashMap Edge Nat) : ∀ x ∈ wEdges (walksOf I), x ∈ nEdges I u := by
  intro x hx
  simp only [wEdges, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨w, hw, s, hs, rfl⟩ := hx
  simp only [walksOf, List.mem_map] at hw
  obtain ⟨rc, _, hrc⟩ := hw
  split at hrc
  · rename_i w' hok
    subst hrc
    simp only [walkOf, bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i rest hrest
      cases hok
      obtain ⟨h1, h2⟩ := walkFrom_mem I u _ _ _ _ hrest
      rcases List.mem_cons.1 hs with rfl | hs
      · have h0 := h2 (by simp [keySyms])
        refine mem_nEdges (N := 0) (by omega) ?_
        simp [nodeViewOf, edgesOf]
      · exact h1 s hs
  · subst hrc; cases hs

theorem wEdges_sub {c : Claim} {e : Ext} : ∀ x ∈ wEdges (walksOf (mkInfo c e)),
    x ∈ nEdges (mkInfo c e) (edgeUses (walksOf (mkInfo c e))) := wEdges_sub_of _ _

end BusEdge

open BusEdge in
/-- **`EdgeBusStmt`.** -/
theorem edgeBus : EdgeBusStmt := by
  intro c e hg _ m
  rw [hcount_eq, hcount_eq]
  have hw : (bundle c.1 e).walks = walksOf (mkInfo c.1 e) := rfl
  simp only [sel, ite_true, Bool.false_eq_true, ite_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkRecvs, walkSends, rcptTraffic, rcptSends, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_FINAL, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, bundle_info, hw]
  rw [node_sends, node_recvs, walk_side _ (· + 1), walk_side _ (fun x => x), cnt_append, cnt_append]
  have hp := chain_perm _ (nEdges_nodup hg _) _ wEdges_sub
  simp only [edgeUses_getD]
  exact (hp.map Msg.toFp).count_eq m

end ZkFormal.Near.Render

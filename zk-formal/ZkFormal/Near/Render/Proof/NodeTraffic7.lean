import ZkFormal.Near.Render.Proof.NodeTraffic6
import ZkFormal.Near.Render.Proof.BusEdge

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic7 — node traffic: EDGE, the edges of a node

The gated edges of a node's fields are the edges its view provides
(`edgesOf`), up to order (`node_edges`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeTr
open NodeCells NodeGen NodeInfo

theorem pairs_flat {β : Type} (g : Nat → List β) (o : Nat) :
    ∀ M, (List.range M).flatMap (fun m => g (2 * m + o) ++ g (2 * m + o + 1)) =
      (List.range (2 * M)).flatMap fun i => g (i + o)
  | 0 => rfl
  | M + 1 => by
    rw [List.range_succ, List.flatMap_append, pairs_flat g o M, show 2 * (M + 1) = 2 * M + 1 + 1 by omega,
      List.range_succ, List.range_succ, List.flatMap_append, List.flatMap_append]
    simp [Nat.add_assoc, Nat.add_comm o 1]

theorem keys_flat {β : Type} (g : Nat → List β) (s : Nat) :
    (if s % 2 = 1 then g 0 else []) ++ (List.range (s / 2)).flatMap (fun m => g (2 * m + s % 2) ++ g (2 * m + s % 2 + 1)) =
      (List.range s).flatMap g := by
  rw [pairs_flat]
  by_cases h : s % 2 = 1
  · rw [if_pos h, h]
    obtain ⟨M, rfl⟩ : ∃ M, s = 2 * M + 1 := ⟨s / 2, by omega⟩
    rw [show (2 * M + 1) / 2 = M by omega, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  · have h0 : s % 2 = 0 := by omega
    rw [if_neg h, h0, List.nil_append]
    obtain ⟨M, rfl⟩ : ∃ M, s = 2 * M := ⟨s / 2, by omega⟩
    rw [show 2 * M / 2 = M by omega]; rfl

theorem keys_flat' {β : Type} (g : Nat → List β) (s : Nat) (X : List β) :
    (if s % 2 = 1 then g 0 else []) ++ ((List.range (s / 2)).flatMap (fun m => g (2 * m + s % 2) ++ g (2 * m + s % 2 + 1))
      ++ X) = (List.range s).flatMap g ++ X := by
  rw [← List.append_assoc, keys_flat]

theorem keys_flat'' {β : Type} (g : Nat → List β) (s : Nat) :
    (if s % 2 = 1 then g 0 else []) ++ (List.range (s / 2)).flatMap (fun m => g (2 * m + s % 2) ++ g (2 * m + s % 2 + 1))
      = (List.range s).flatMap g := keys_flat g s

theorem field_flat0 {β : Type} (L : Nat) (hL : 1 ≤ L) (g : Nat → List β) (hg : ∀ i, i ≠ 0 → g i = []) :
    (List.range L).flatMap g = g 0 := flatMap_first L hL g hg

theorem branchWins_flatj {β : Type} (I : Info) (g : F → List β)
    (hg : ∀ k w l j w' l', g (.ch (kidWin I k w l j)) = g (.ch (kidWin I k w' l' j)))
    (kids : List Kid) :
    (branchWins I kids).flatMap g =
      ((kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none)).flatMap
        (fun x => g (.ch (kidWin I x.1 0 false (some x.2)))) := by
  unfold branchWins
  generalize (kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none) = P
  have h1 : ∀ (Q : List (Kid × Nat)) (L : List Nat), Q.length ≤ L.length →
      ((Q.zip L).map fun x => F.ch (kidWin I x.1.1 x.2 (x.2 + 1 = P.length) (some x.1.2))).flatMap g =
        Q.flatMap fun x => g (.ch (kidWin I x.1 0 false (some x.2))) := by
    intro Q
    induction Q with
    | nil => intro L _; simp
    | cons q Q ih =>
      intro L hL
      cases L with
      | nil => simp at hL
      | cons l L =>
        simp only [List.zip_cons_cons, List.map_cons, List.flatMap_cons]
        rw [ih L (by simpa using hL), hg]
  exact h1 P _ (by simp)

section
variable (I : Info) (n : Nat)

/-- Key nibble edges of a key node = the view's key edges. -/
theorem nib_leaf {k : List Nat} {v : VSlot} {m : Nat} (hnr : I.nodeAt n = .leaf k v m) :
    (List.range k.length).flatMap (nibE I n) = keyEdges n k := by
  exact flatMap_single (fun i _ => by simp [nibE, hnr, isExtR, NodeRec.key])

theorem nib_ext {k : List Nat} {kid : Kid} {m : Nat} (hnr : I.nodeAt n = .ext k kid m) :
    (List.range k.length).flatMap (nibE I n) = keyEdges n k.dropLast ++
      (match nkidOf I kid, k.getLast? with
       | .node _ _ cr _ _, some x => [[n, k.length - 1, x, cr, 0]]
       | _, _ => []) := by
  rcases Nat.eq_zero_or_pos k.length with h0 | h0
  · have : k = [] := List.eq_nil_of_length_eq_zero h0
    subst this; cases kid <;> simp [keyEdges, nkidOf]
  · obtain ⟨M, hM⟩ : ∃ M, k.length = M + 1 := ⟨k.length - 1, by omega⟩
    rw [hM, List.range_succ, List.flatMap_append]
    congr 1
    · simp only [keyEdges, List.length_dropLast, hM, Nat.add_sub_cancel]
      rw [← flatMap_single (fun _ _ => rfl)]
      apply flatMap_congr'; intro i hi
      have hi' := List.mem_range.1 hi
      simp only [nibE, hnr, isExtR, NodeRec.key, hM, show ¬ i + 1 = M + 1 by omega, and_false, if_false]
      have : i < k.length - 1 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_dropLast, this, List.getElem?_eq_getElem (show i < k.length by omega)]
    · have hl : k.getLast? = some (k.getD M 0) := by
        rw [List.getLast?_eq_getElem?, hM]; simp [List.getD_eq_getElem?_getD, show M < k.length by omega]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, nibE, hnr, isExtR, NodeRec.key, hM, and_self,
        if_true, hl]
      cases kid <;> simp [xrvOf, nkidOf, xresOf]

end

/-- Children edges of a branch. -/
theorem kids_edges (I : Info) (n : Nat) (kids : List Kid) (hle : isLE (I.nodeAt n) = false) :
    (branchWins I kids).flatMap (fun f => (List.range (f.len 0)).flatMap (geF I n f)) =
      ((kids.map (nkidOf I)).zip (List.range (kids.map (nkidOf I)).length)).filterMap fun
        | (.node _ _ cr _ _, j) => some [n, 0, j, cr, 0]
        | _ => none := by
  have hg : ∀ f ∈ branchWins I kids, (List.range (f.len 0)).flatMap (geF I n f) = geF I n f 0 := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf
    exact field_flat0 _ (by simp [F.len]) _ (fun i hi => by rw [geF_ch]; simp [hi])
  rw [flatMap_congr' hg, branchWins_flatj I (fun f => geF I n f 0)
    (fun k w l j w' l' => by cases k <;> simp [geF_ch, kidWin])]
  clear hg
  simp only [List.length_map]
  generalize List.range kids.length = L
  induction kids generalizing L with
  | nil => simp
  | cons k kids ih =>
    cases L with
    | nil => simp
    | cons j L =>
      simp only [ne_eq, decide_not] at ih
      simp only [List.zip_cons_cons, List.map_cons, List.filter_cons, List.filterMap_cons]
      cases k with
      | none => simpa [nkidOf] using ih L
      | hash h => simpa [geF_ch, kidWin, nkidOf] using ih L
      | node c => simpa [geF_ch, kidWin, nkidOf, hle] using ih L

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hs : Small e)
include hg hs

theorem node_edges (u : Std.HashMap Edge Nat) {n : Nat} (hn : n < e.ns.length) :
    ((nodeRecs (mkInfo c.1 e) n).flatMap (ge (mkInfo c.1 e))).Perm (edgesOf n (nodeViewOf (mkInfo c.1 e) u n)) := by
  rw [ge_rows hg hs hn, BusEdge.edgesOf_eq]
  have hw : ((mkInfo c.1 e).nodeAt n).wf := by rw [info_nodeAt hn]; exact hg.nodes_wf _ (List.getElem_mem hn)
  have hk : ∀ x ∈ ((mkInfo c.1 e).nodeAt n).key, x < 16 := by
    intro x hx
    cases h : (mkInfo c.1 e).nodeAt n with
    | leaf k v m =>
      rw [h] at hw hx; exact of_decide_eq_true (List.all_eq_true.1 hw.1 x hx)
    | ext k kid m =>
      rw [h] at hw hx; exact of_decide_eq_true (List.all_eq_true.1 hw.1 x hx)
    | branch v kids m => rw [h] at hx; simp [NodeRec.key] at hx
  have hres : (nodeViewOf (mkInfo c.1 e) u n).res = (mkInfo c.1 e).res.getD n n := rfl
  have hv : (nodeViewOf (mkInfo c.1 e) u n).v = nodeVOf (mkInfo c.1 e) n ((mkInfo c.1 e).nodeAt n) := rfl
  have htag : (List.range 1).flatMap (geF (mkInfo c.1 e) n .tag) =
      if n = 0 then [[0, 0, SYM_START, (mkInfo c.1 e).res.getD n n, 0]] else [] := by
    simp [geF_tag]
  have hplain : ∀ f L, (f = .hpl ∨ f = .vlen ∨ f = .bm ∨ f = .mem) →
      (List.range L).flatMap (geF (mkInfo c.1 e) n f) = [] :=
    fun f L h => flatMap_nil' (fun i _ => geF_plain _ _ f i h)
  simp only [BusEdge.body, hres, hv]
  cases hnr : (mkInfo c.1 e).nodeAt n with
  | leaf k v m =>
    have hle : isLE ((mkInfo c.1 e).nodeAt n) = true := by rw [hnr]; rfl
    have h1 : geF (mkInfo c.1 e) n .hpf 0 = if k.length % 2 = 1 then nibE (mkInfo c.1 e) n 0 else [] := by
      simpa [hnr, NodeRec.key] using geF_hpf _ n hle hk
    have h2 : ∀ m', m' < k.length / 2 → geF (mkInfo c.1 e) n .key m' = nibE (mkInfo c.1 e) n (2 * m' + k.length % 2) ++
        nibE (mkInfo c.1 e) n (2 * m' + k.length % 2 + 1) := by
      intro m' hm'; simpa [hnr, NodeRec.key] using geF_key _ n hle hk m' (by simpa [hnr, NodeRec.key] using hm')
    have hkeys : (List.range (F.len (hplenOf (.leaf k v m)) .key)).flatMap (geF (mkInfo c.1 e) n .key) =
        (List.range (k.length / 2)).flatMap fun m' =>
          nibE (mkInfo c.1 e) n (2 * m' + k.length % 2) ++ nibE (mkInfo c.1 e) n (2 * m' + k.length % 2 + 1) := by
      simp only [F.len, hplenOf, isLE, if_true, NodeRec.key, Nat.add_sub_cancel_left]
      exact flatMap_congr' fun m' hm => h2 m' (List.mem_range.1 hm)
    have hvh : (List.range (F.len (hplenOf (.leaf k v m)) (.vh (valWin (mkInfo c.1 e) n v)))).flatMap
        (geF (mkInfo c.1 e) n (.vh (valWin (mkInfo c.1 e) n v))) =
        match nslotOf (mkInfo c.1 e) n v with | .touched _ _ => [[n, k.length, SYM_END, n, 0]] | _ => [] := by
      rw [field_flat0 _ (by simp [F.len]) _ (fun i hi => by rw [geF_vh]; simp [hi]), geF_vh, hnr]
      cases v <;> simp [valWin, nslotOf, typeOf, NodeRec.key]
    simp only [nodeVOf, fieldsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, htag, hkeys, hvh,
      hplain .hpl _ (by simp), hplain .vlen _ (by simp), hplain .mem _ (by simp), List.nil_append]
    simp only [F.len, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, h1]
    rw [keys_flat', nib_leaf _ n hnr, geF_tag]; exact List.Perm.refl _
  | ext k kid m =>
    have hle : isLE ((mkInfo c.1 e).nodeAt n) = true := by rw [hnr]; rfl
    have h1 : geF (mkInfo c.1 e) n .hpf 0 = if k.length % 2 = 1 then nibE (mkInfo c.1 e) n 0 else [] := by
      simpa [hnr, NodeRec.key] using geF_hpf _ n hle hk
    have h2 : ∀ m', m' < k.length / 2 → geF (mkInfo c.1 e) n .key m' = nibE (mkInfo c.1 e) n (2 * m' + k.length % 2) ++
        nibE (mkInfo c.1 e) n (2 * m' + k.length % 2 + 1) := by
      intro m' hm'; simpa [hnr, NodeRec.key] using geF_key _ n hle hk m' (by simpa [hnr, NodeRec.key] using hm')
    have hkeys : (List.range (F.len (hplenOf (.ext k kid m)) .key)).flatMap (geF (mkInfo c.1 e) n .key) =
        (List.range (k.length / 2)).flatMap fun m' =>
          nibE (mkInfo c.1 e) n (2 * m' + k.length % 2) ++ nibE (mkInfo c.1 e) n (2 * m' + k.length % 2 + 1) := by
      simp only [F.len, hplenOf, isLE, if_true, NodeRec.key, Nat.add_sub_cancel_left]
      exact flatMap_congr' fun m' hm => h2 m' (List.mem_range.1 hm)
    have hch : (List.range (F.len (hplenOf (.ext k kid m)) (.ch (kidWin (mkInfo c.1 e) kid 0 true none)))).flatMap
        (geF (mkInfo c.1 e) n (.ch (kidWin (mkInfo c.1 e) kid 0 true none))) = [] :=
      flatMap_nil' fun i _ => by rw [geF_ch, hle]; simp
    simp only [nodeVOf, fieldsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, htag, hkeys, hch,
      hplain .hpl _ (by simp), hplain .mem _ (by simp), List.nil_append]
    simp only [F.len, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, h1]
    rw [keys_flat'', nib_ext _ n hnr, geF_tag]; exact List.Perm.refl _
  | branch v kids m =>
    have hle : isLE ((mkInfo c.1 e).nodeAt n) = false := by rw [hnr]; rfl
    have hkd := kids_edges (mkInfo c.1 e) n kids hle
    simp only [hplenOf, isLE, Bool.false_eq_true, if_false] at hkd ⊢
    cases v with
    | none =>
      simp only [nodeVOf, fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        List.append_nil, hkd, hplain .bm _ (by simp), hplain .mem _ (by simp), List.nil_append, Option.map_none]
      simp only [F.len, htag]
      exact List.Perm.refl _
    | some sv =>
      have hvh : (List.range 32).flatMap (geF (mkInfo c.1 e) n (.vh (valWin (mkInfo c.1 e) n sv))) =
          match some (nslotOf (mkInfo c.1 e) n sv) with | some (.touched _ _) => [[n, 0, SYM_END, n, 0]] | _ => [] := by
        rw [field_flat0 _ (by decide) _ (fun i hi => by rw [geF_vh]; simp [hi]), geF_vh, hnr]
        cases sv <;> simp [valWin, nslotOf, typeOf]
      simp only [nodeVOf, fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        List.append_nil, hkd, hplain .bm _ (by simp), hplain .mem _ (by simp), hplain .vlen _ (by simp),
        List.nil_append, Option.map_some]
      simp only [F.len, htag, hvh]
      exact List.Perm.append_left _ List.perm_append_comm

end

end NodeTr

end ZkFormal.Near.Render

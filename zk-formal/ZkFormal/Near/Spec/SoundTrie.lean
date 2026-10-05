import ZkFormal.Near.Spec.SoundShape

/-!
# ZkFormal.Near.Spec.SoundTrie — the record trie: congruence, `wf`, size

* `treeOf_succ` — one unfolding step (`nodeTree`);
* `treeOf_congr` — the trie of node `n` only depends on the touched values of
  the nodes of its subtree `sub f n`;
* `treeOf_wf` — under `TreeShape` and node well-formedness, fuel
  `ns.length - d n` suffices and the trie is `PTrie.wf`;
* `revealed_eq` — `revealedBytes` is the sum of `nodeSize` over `sub f n`,
  hence `revealedBytes (trieOf ns vals) ≤ revealedOf ns`.
-/

namespace ZkFormal.Near

open NearSpec

set_option linter.unusedSectionVars false

namespace Sound

variable {ns : List NodeRec}

/-- One node of `treeOf`, children built by `g`. -/
def nodeTree (vals : Nat → Bytes) (n : Nat) (g : Nat → PTrie) : NodeRec → PTrie
  | .leaf k v mem => .leaf k (slotOf vals n v) mem
  | .ext k kid mem => .ext k (kidTree g kid) mem
  | .branch v kids mem => .branch (v.map (slotOf vals n)) (kidsOf g kids) mem

theorem treeOf_succ {vals : Nat → Bytes} {f n : Nat} {nr : NodeRec} (h : ns[n]? = some nr) :
    treeOf ns vals (f + 1) n = nodeTree vals n (treeOf ns vals f) nr := by
  simp only [treeOf, h]; cases nr <;> rfl

theorem treeOf_none {vals : Nat → Bytes} {f n : Nat} (h : ns[n]? = none) :
    treeOf ns vals f n = .hash [] := by
  cases f <;> simp [treeOf, h]

/-! ## Congruence -/

theorem kidsOf_congr {g g' : Nat → PTrie} :
    ∀ kids : List Kid, (∀ c, Kid.node c ∈ kids → g c = g' c) → kidsOf g kids = kidsOf g' kids
  | [], _ => rfl
  | kid :: r, h => by
    have ih := kidsOf_congr r (fun c hc => h c (List.mem_cons_of_mem _ hc))
    cases kid with
    | none => simp [kidsOf, ih]
    | hash _ => simp [kidsOf, ih]
    | node c => simp [kidsOf, ih, h c (by simp)]

theorem kidTree_congr {g g' : Nat → PTrie} {kid : Kid} (h : ∀ c, kid = .node c → g c = g' c) :
    kidTree g kid = kidTree g' kid := by
  cases kid <;> simp [kidTree, h]

theorem mem_sub_succ {f n c j : Nat} {nr : NodeRec} (hn : ns[n]? = some nr)
    (hc : Kid.node c ∈ nr.kids) (hj : j ∈ sub ns f c) : j ∈ sub ns (f + 1) n := by
  rw [sub_succ hn]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, hc, hj⟩)

theorem self_mem_sub {f n : Nat} {nr : NodeRec} (hn : ns[n]? = some nr) :
    n ∈ sub ns (f + 1) n := by
  rw [sub_succ hn]; exact List.mem_cons_self

/-- Agreement of two value maps on the touched nodes of a set. -/
def AgreeOn (ns : List NodeRec) (vals vals' : Nat → Bytes) (l : List Nat) : Prop :=
  ∀ j ∈ l, ∀ nr, ns[j]? = some nr → nr.touched = true → vals j = vals' j

theorem slotOf_congr {vals vals' : Nat → Bytes} {n : Nat} {s : VSlot}
    (h : s = .touched → vals n = vals' n) : slotOf vals n s = slotOf vals' n s := by
  cases s <;> simp [slotOf, h]

theorem treeOf_congr {vals vals' : Nat → Bytes} :
    ∀ f n, AgreeOn ns vals vals' (sub ns f n) → treeOf ns vals f n = treeOf ns vals' f n
  | 0, _, _ => rfl
  | f + 1, n, h => by
    cases hn : ns[n]? with
    | none => rw [treeOf_none hn, treeOf_none hn]
    | some nr =>
      rw [treeOf_succ hn, treeOf_succ hn]
      have hk : ∀ c, Kid.node c ∈ nr.kids → treeOf ns vals f c = treeOf ns vals' f c :=
        fun c hc => treeOf_congr f c (fun j hj => h j (mem_sub_succ hn hc hj))
      have hself : ∀ s, NodeRec.touched nr = true → vals n = vals' n →
          slotOf vals n s = slotOf vals' n s := by
        intro s _ he; exact slotOf_congr (fun _ => he)
      have hv : nr.touched = true → vals n = vals' n := fun ht => h n (self_mem_sub hn) nr hn ht
      cases nr with
      | leaf k v mem =>
        simp only [nodeTree]
        rw [slotOf_congr (fun hv' => hv (by subst hv'; rfl))]
      | ext k kid mem =>
        simp only [nodeTree]
        rw [kidTree_congr (fun c hc => hk c (by subst hc; simp [NodeRec.kids]))]
      | branch v kids mem =>
        simp only [nodeTree]
        rw [kidsOf_congr kids (fun c hc => hk c hc)]
        cases v with
        | none => rfl
        | some s =>
          simp only [Option.map_some]
          rw [slotOf_congr (fun hs => hv (by subst hs; rfl))]

/-! ## Well-formedness -/

theorem packNibbles_length : ∀ l : List Nat, (packNibbles l).length ≤ l.length
  | a :: b :: rest => by
    have := packNibbles_length rest
    simp [packNibbles]; omega
  | [] => by simp [packNibbles]
  | [_] => by simp [packNibbles]

theorem hexPrefix_length (k : List Nat) (b : Bool) : (hexPrefix k b).length ≤ k.length + 1 := by
  rcases k with _ | ⟨a, rest⟩
  · simp [hexPrefix, packNibbles]
  · have := packNibbles_length rest
    have := packNibbles_length (a :: rest)
    by_cases h : (rest.length + 1) % 2 = 1
    · simp [hexPrefix, h]; omega
    · simp [hexPrefix, h]; omega

theorem nodeWf_key {nr : NodeRec} (hwf : nr.wf) {i x : Nat} (h : nr.key[i]? = some x) :
    x < 16 := by
  have hm := List.mem_of_getElem? h
  cases nr with
  | leaf k _ _ =>
    have := hwf.1; simp [nibblesOk, List.all_eq_true] at this; exact this x hm
  | ext k _ _ =>
    have := hwf.1; simp [nibblesOk, List.all_eq_true] at this; exact this x hm
  | branch _ _ _ => simp [NodeRec.key] at hm

theorem kidsOf_wf (g : Nat → PTrie) :
    ∀ kids : List Kid, (∀ kid ∈ kids, kid ≠ .none → (kidTree g kid).wf = true) →
      Kids.wf (kidsOf g kids) kids.length = true
  | [], _ => by simp [kidsOf, Kids.wf]
  | kid :: r, h => by
    have ih := kidsOf_wf g r (fun k hk => h k (List.mem_cons_of_mem _ hk))
    cases kid with
    | none => simp [kidsOf, Kids.wf, ih]
    | hash hh =>
      have := h (.hash hh) (by simp) (by simp); simp [kidTree] at this
      simp [kidsOf, Kids.wf, ih, this]
    | node c =>
      have := h (.node c) (by simp) (by simp); simp [kidTree] at this
      simp [kidsOf, Kids.wf, ih, this]

section Wf
variable (hs : TreeShape ns) (d : Nat → Nat) (hd0 : d 0 = 0)
  (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) (hwf : ∀ nr ∈ ns, nr.wf)
include hs hd0 hd hwf

theorem fuel_pos {n F : Nat} (hr : Reach ns 0 n) (hF : d n + F = ns.length) : 0 < F := by
  have := Reach.depth_lt d hd hs hr hs.nonempty; omega

theorem reach_some {n : Nat} (hr : Reach ns 0 n) : ∃ nr, ns[n]? = some nr ∧ nr.wf := by
  have hn := Reach.lt hs hr hs.nonempty
  refine ⟨ns[n], by simp [hn], hwf _ (List.getElem_mem hn)⟩

theorem treeOf_wf {vals : Nat → Bytes}
    (hlen : ∀ k nr, ns[k]? = some nr → nr.touched = true → (vals k).length = 72) :
    ∀ F n, Reach ns 0 n → d n + F = ns.length → (treeOf ns vals F n).wf = true
  | 0, n, hr, hF => absurd (fuel_pos hs d hd0 hd hwf hr hF) (by omega)
  | f + 1, n, hr, hF => by
    obtain ⟨nr, hn, hnw⟩ := reach_some hs d hd0 hd hwf hr
    rw [treeOf_succ hn]
    have hkid : ∀ c, Kid.node c ∈ nr.kids → (treeOf ns vals f c).wf = true := by
      intro c hc
      have hch : ChildOf ns n c := ⟨nr, hn, hc⟩
      exact treeOf_wf hlen f c (.tail hr hch) (by have := hd _ _ hch; omega)
    have hslot : ∀ s : VSlot, s.wf → (s = .touched → nr.touched = true) →
        slotOk (slotOf vals n s) = true := by
      intro s hsw ht
      cases s with
      | ref len h => simp [slotOf, slotOk]; exact ⟨hsw.1, hsw.2⟩
      | touched => simp [slotOf, slotOk, hlen n nr hn (ht rfl)]
    cases nr with
    | leaf k v mem =>
      obtain ⟨h1, h2, h3, h4⟩ := hnw
      have := hexPrefix_length k true
      have := hslot v h3 (fun hv => by subst hv; rfl)
      simp only [nodeTree, PTrie.wf, h1, this, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h4, by omega⟩
    | ext k kid mem =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hnw
      have := hexPrefix_length k false
      have hk : (kidTree (treeOf ns vals f) kid).wf = true := by
        cases kid with
        | none => exact absurd rfl h3
        | hash hh => simp [kidTree, PTrie.wf]; exact h4
        | node c => exact hkid c (by simp [NodeRec.kids])
      simp only [nodeTree, PTrie.wf, h1, hk, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h5, by omega⟩
    | branch v kids mem =>
      obtain ⟨h1, h2, h3, h4⟩ := hnw
      have hk := kidsOf_wf (treeOf ns vals f) kids (fun kid hk hne => by
        cases kid with
        | none => exact absurd rfl hne
        | hash hh => have := h3 _ hk; simp [kidTree, PTrie.wf]; exact this
        | node c => exact hkid c hk)
      rw [h1] at hk
      have hv : (match v.map (slotOf vals n) with | some s => slotOk s | none => true) = true := by
        cases v with
        | none => rfl
        | some s => exact hslot s (h2 s rfl) (fun hs' => by subst hs'; rfl)
      simp only [nodeTree, PTrie.wf, hk, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hv, trivial⟩, h4⟩

end Wf

/-! ## Revealed size -/

/-- `nodeSize` of node `m` (`0` out of range). -/
def szOf (ns : List NodeRec) (m : Nat) : Nat := (ns[m]?.map nodeSize).getD 0

theorem zeros_length (n : Nat) : (zeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeros, ih]

theorem kids_revealed (g : Nat → PTrie) :
    ∀ kids : List Kid,
      Kids.revealedBytes (kidsOf g kids) = (kids.map fun kid => (kidTree g kid).revealedBytes).sum
  | [] => by simp [kidsOf, Kids.revealedBytes]
  | kid :: r => by
    have ih := kids_revealed g r
    cases kid <;> simp [kidsOf, Kids.revealedBytes, kidTree, PTrie.revealedBytes, ih]

theorem kids_bytes_length (g : Nat → PTrie) :
    ∀ kids : List Kid, (∀ kid ∈ kids, kid.wf) →
      (concatAll (kids.map (kidBytes fun _ => zeros 32))).length = 32 * Kids.count (kidsOf g kids)
  | [], _ => by simp [concatAll, kidsOf, Kids.count]
  | kid :: r, h => by
    have ih := kids_bytes_length g r (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have hk := h kid (by simp)
    cases kid with
    | none => simp [concatAll, kidsOf, Kids.count, kidBytes, ih]
    | hash hh =>
      simp [Kid.wf] at hk
      simp [concatAll, kidsOf, Kids.count, kidBytes, ih, hk]; omega
    | node c => simp [concatAll, kidsOf, Kids.count, kidBytes, ih, zeros_length]; omega

theorem sum_flatMap_kidSub (s : Nat → List Nat) (g : Nat → Nat) :
    ∀ kids : List Kid, ((kids.flatMap (kidSub s)).map g).sum =
      (kids.map fun kid => ((kidSub s kid).map g).sum).sum
  | [] => rfl
  | kid :: r => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap_kidSub s g r]; simp

theorem vref_length {s : VSlot} (h : s.wf) : (vrefBytes (zeros 32) s).length = 36 := by
  cases s with
  | ref len hh => simp [vrefBytes, VSlot.wf] at h ⊢; simp [u32, leN_length, h.2]
  | touched => simp [vrefBytes, u32, leN_length, zeros_length]

theorem revealed_eq {vals : Nat → Bytes} (hwf : ∀ nr ∈ ns, nr.wf)
    (hlen : ∀ k nr, ns[k]? = some nr → nr.touched = true → (vals k).length = 72) :
    ∀ f n, (treeOf ns vals f n).revealedBytes = ((sub ns f n).map (szOf ns)).sum
  | 0, _ => by simp [treeOf, sub, PTrie.revealedBytes]
  | f + 1, n => by
    cases hn : ns[n]? with
    | none => simp [treeOf, sub, hn, PTrie.revealedBytes]
    | some nr =>
      rw [treeOf_succ hn, sub_succ hn, List.map_cons, List.sum_cons, sum_flatMap_kidSub]
      have hnw := hwf nr (List.mem_of_getElem? hn)
      have hsz : szOf ns n = nodeSize nr := by simp [szOf, hn]
      rw [hsz]
      have hkid : ∀ kid, ((kidSub (sub ns f) kid).map (szOf ns)).sum =
          (kidTree (treeOf ns vals f) kid).revealedBytes := by
        intro kid
        cases kid with
        | none => simp [kidSub, kidTree, PTrie.revealedBytes]
        | hash _ => simp [kidSub, kidTree, PTrie.revealedBytes]
        | node c => simp [kidSub, kidTree, revealed_eq hwf hlen f c]
      simp only [hkid]
      cases nr with
      | leaf k v mem =>
        obtain ⟨_, _, h3, _⟩ := hnw
        have hv := vref_length h3
        cases v with
        | ref len hh =>
          simp [nodeTree, PTrie.revealedBytes, slotOf, nodeSize, ser, NodeRec.touched, NodeRec.kids] at hv ⊢
          simp [u32, u64, leN_length, hv]; omega
        | touched =>
          have := hlen n _ hn rfl
          simp [nodeTree, PTrie.revealedBytes, slotOf, nodeSize, ser, NodeRec.touched, NodeRec.kids,
            this] at hv ⊢
          simp [u32, u64, leN_length, hv]; omega
      | ext k kid mem =>
        obtain ⟨_, _, h3, h4, _⟩ := hnw
        have hkb : (kidBytes (fun _ => zeros 32) kid).length = 32 := by
          cases kid with
          | none => exact absurd rfl h3
          | hash hh => simpa [kidBytes, Kid.wf] using h4
          | node c => simp [kidBytes, zeros_length]
        simp [nodeTree, PTrie.revealedBytes, nodeSize, ser, NodeRec.touched, NodeRec.kids]
        simp [u32, u64, leN_length, hkb]; omega
      | branch v kids mem =>
        obtain ⟨h1, h2, h3, _⟩ := hnw
        have hkb := kids_bytes_length (treeOf ns vals f) kids h3
        have hkr := kids_revealed (treeOf ns vals f) kids
        cases v with
        | none =>
          simp [nodeTree, PTrie.revealedBytes, nodeSize, ser, NodeRec.touched, NodeRec.kids]
          simp [u16, u64, leN_length, hkb, hkr]; omega
        | some s =>
          have hv := vref_length (h2 s rfl)
          cases s with
          | ref len hh =>
            simp [nodeTree, PTrie.revealedBytes, slotOf, nodeSize, ser, NodeRec.touched,
              NodeRec.kids] at hv ⊢
            simp [u16, u64, leN_length, hkb, hkr, hv]; omega
          | touched =>
            have := hlen n _ hn rfl
            simp [nodeTree, PTrie.revealedBytes, slotOf, nodeSize, ser, NodeRec.touched,
              NodeRec.kids, this] at hv ⊢
            simp [u16, u64, leN_length, hkb, hkr, hv]; omega

theorem revealed_le (hs : TreeShape ns) (d : Nat → Nat)
    (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) {vals : Nat → Bytes} (hwf : ∀ nr ∈ ns, nr.wf)
    (hlen : ∀ k nr, ns[k]? = some nr → nr.touched = true → (vals k).length = 72) :
    (trieOf ns vals).revealedBytes ≤ revealedOf ns := by
  unfold trieOf
  rw [revealed_eq hwf hlen, revealedOf, ← sum_range_getElem? nodeSize ns]
  exact sum_le_range _ _ _ (nodup_sub hs d hd _ _)
    (fun x hx => Reach.lt hs (mem_sub hx) hs.nonempty)

end Sound

end ZkFormal.Near

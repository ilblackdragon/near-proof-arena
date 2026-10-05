import ZkFormal.Near.Spec.CompleteTrie

/-!
# ZkFormal.Near.Spec.CompleteWalk — `get`/`set` on a trie vs. its records

* `get_vl` — `p.get key` reads the value of node `slotIdx p key`;
* `set_same` — `p.set key nv` keeps the records, the node count, the child
  slot and every `slotIdx`, and updates `vl` at `slotIdx p key`;
* `walk_recs` — a successful `get` is a walk of the records ending in the
  touched slot `slotIdx p key`;
* `recs_touched` — a touched record carries a revealed value.
-/

namespace ZkFormal.Near.Prune

open NearSpec NearSpec.TransferV1

theorem cnt_pos_of_get {p : PTrie} {key : List Nat} {x : Bytes} (h : p.get key = some x) :
    0 < cnt p := by
  cases p with
  | hash _ => simp [PTrie.get] at h
  | _ => simp only [cnt]; omega

theorem kidOf_of_pos {p : PTrie} (id : Nat) (h : 0 < cnt p) : kidOf p id = .node id := by
  cases p with
  | hash _ => simp [cnt] at h
  | _ => rfl

/-! ## `get` -/

mutual
theorem get_vl : ∀ (p : PTrie) (key : List Nat) (x : Bytes), p.get key = some x →
    (vl p)[slotIdx p key]? = some (some x)
  | .hash _, _, _, h => by simp [PTrie.get] at h
  | .leaf k s mem, key, x, h => by
    simp only [PTrie.get] at h
    split at h
    · simp [vl, slotIdx, h]
    · cases h
  | .ext k c mem, key, x, h => by
    simp only [PTrie.get] at h
    split at h
    · simp only [vl, slotIdx, Nat.add_comm 1, List.getElem?_cons_succ]
      exact get_vl c _ x h
    · cases h
  | .branch v cs mem, [], x, h => by
    simp only [PTrie.get] at h
    simp [vl, slotIdx, h]
  | .branch v cs mem, n :: rest, x, h => by
    simp only [PTrie.get] at h
    simp only [vl, slotIdx, Nat.add_comm 1, List.getElem?_cons_succ]
    exact getKids_vl cs n rest x h
theorem getKids_vl : ∀ (cs : Kids) (n : Nat) (key : List Nat) (x : Bytes), Kids.get cs n key = some x →
    (vlKids cs)[slotIdxKids cs n key]? = some (some x)
  | .nil, _, _, _, h => by simp [Kids.get] at h
  | .none _, 0, _, _, h => by simp [Kids.get] at h
  | .some c r, 0, key, x, h => by
    simp only [Kids.get] at h
    have h1 := get_vl c key x h
    simp only [vlKids, slotIdxKids]
    rw [List.getElem?_append_left (lt_of_getElem? h1)]; exact h1
  | .none r, i + 1, key, x, h => by
    simp only [Kids.get] at h
    simp only [vlKids, slotIdxKids]; exact getKids_vl r i key x h
  | .some c r, i + 1, key, x, h => by
    simp only [Kids.get] at h
    simp only [vlKids, slotIdxKids]
    rw [List.getElem?_append_right (by rw [vl_length]; omega), vl_length,
      show cnt c + slotIdxKids r i key - cnt c = slotIdxKids r i key by omega]
    exact getKids_vl r i key x h
end

/-! ## `set` keeps the shape -/

/-- `p'` has the same records, node count, child slot and slots as `p`. -/
structure Same (p p' : PTrie) : Prop where
  cnt : cnt p' = cnt p
  recs : ∀ b, recs p' b = recs p b
  kidOf : ∀ id, kidOf p' id = kidOf p id
  slot : ∀ key, slotIdx p' key = slotIdx p key

structure SameKids (cs cs' : Kids) : Prop where
  cnt : cntKids cs' = cntKids cs
  recs : ∀ b, recsKids cs' b = recsKids cs b
  kids : ∀ b, kidsList cs' b = kidsList cs b
  slot : ∀ n key, slotIdxKids cs' n key = slotIdxKids cs n key

theorem Same.refl (p : PTrie) : Same p p := ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem Same.trans {p q r : PTrie} (h₁ : Same p q) (h₂ : Same q r) : Same p r :=
  ⟨h₂.cnt.trans h₁.cnt, fun b => (h₂.recs b).trans (h₁.recs b),
   fun id => (h₂.kidOf id).trans (h₁.kidOf id), fun k => (h₂.slot k).trans (h₁.slot k)⟩

mutual
theorem set_same : ∀ (p : PTrie) (key : List Nat) (nv : Bytes) (p' : PTrie), p.set key nv = some p' →
    Same p p' ∧ slotIdx p key < cnt p ∧ vl p' = (vl p).set (slotIdx p key) (some nv)
  | .hash _, _, _, _, h => by simp [PTrie.set] at h
  | .leaf k s mem, key, nv, p', h => by
    simp only [PTrie.set] at h
    split at h
    · cases s with
      | ref _ _ => simp [Slot.get] at h
      | val b =>
        simp only [Slot.get, Option.map_some, Option.some.injEq] at h; subst h
        exact ⟨⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, by simp [slotIdx, cnt],
          by simp [vl, slotIdx, Slot.get]⟩
    · cases h
  | .ext k c mem, key, nv, p', h => by
    simp only [PTrie.set] at h
    split at h
    · cases hs : c.set (key.drop k.length) nv with
      | none => simp [hs] at h
      | some c' =>
        simp only [hs, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨hS, hlt, hv⟩ := set_same c _ nv c' hs
        refine ⟨⟨?_, ?_, fun _ => rfl, ?_⟩, ?_, ?_⟩
        · simp only [cnt, hS.cnt]
        · intro b; simp only [recs, hS.recs, hS.kidOf]
        · intro key'; simp only [slotIdx, hS.slot]
        · simp only [slotIdx, cnt]; omega
        · simp only [vl, slotIdx, hv, Nat.add_comm 1, List.set_cons_succ]
    · cases h
  | .branch v cs mem, [], nv, p', h => by
    simp only [PTrie.set] at h
    match v, h with
    | some (.val b), h =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨⟨rfl, fun _ => rfl, fun _ => rfl, fun key => by cases key <;> rfl⟩,
        by simp only [slotIdx, cnt]; omega, by simp [vl, slotIdx, Slot.get]⟩
  | .branch v cs mem, n :: rest, nv, p', h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest nv with
    | none => simp [hs] at h
    | some cs' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨hS, hlt, hv⟩ := setKids_same cs n rest nv cs' hs
      refine ⟨⟨?_, ?_, fun _ => rfl, ?_⟩, ?_, ?_⟩
      · simp only [cnt, hS.cnt]
      · intro b; simp only [recs, hS.recs, hS.kids]
      · intro key'
        cases key' with
        | nil => rfl
        | cons m r => simp only [slotIdx, hS.slot]
      · simp only [slotIdx, cnt]; omega
      · simp only [vl, slotIdx, hv, Nat.add_comm 1, List.set_cons_succ]
theorem setKids_same : ∀ (cs : Kids) (n : Nat) (key : List Nat) (nv : Bytes) (cs' : Kids),
    Kids.set cs n key nv = some cs' →
    SameKids cs cs' ∧ slotIdxKids cs n key < cntKids cs ∧
      vlKids cs' = (vlKids cs).set (slotIdxKids cs n key) (some nv)
  | .nil, _, _, _, _, h => by simp [Kids.set] at h
  | .none _, 0, _, _, _, h => by simp [Kids.set] at h
  | .some c r, 0, key, nv, cs', h => by
    simp only [Kids.set] at h
    cases hs : c.set key nv with
    | none => simp [hs] at h
    | some c' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨hS, hlt, hv⟩ := set_same c key nv c' hs
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [cntKids, hS.cnt]
      · intro b; simp only [recsKids, hS.recs, hS.cnt]
      · intro b; simp only [kidsList, hS.kidOf, hS.cnt]
      · intro m key'
        cases m with
        | zero => simp only [slotIdxKids, hS.slot]
        | succ m => simp only [slotIdxKids, hS.cnt]
      · simp only [slotIdxKids, cntKids]; omega
      · simp only [vlKids, slotIdxKids, hv]
        rw [List.set_append]; simp only [vl_length, hlt, ↓reduceIte]
  | .none r, i + 1, key, nv, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key nv with
    | none => simp [hs] at h
    | some r' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨hS, hlt, hv⟩ := setKids_same r i key nv r' hs
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [cntKids, hS.cnt]
      · intro b; simp only [recsKids, hS.recs]
      · intro b; simp only [kidsList, hS.kids]
      · intro m key'
        cases m with
        | zero => rfl
        | succ m => simp only [slotIdxKids, hS.slot]
      · simp only [slotIdxKids, cntKids]; omega
      · simp only [vlKids, slotIdxKids, hv]
  | .some c r, i + 1, key, nv, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key nv with
    | none => simp [hs] at h
    | some r' =>
      simp only [hs, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨hS, hlt, hv⟩ := setKids_same r i key nv r' hs
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [cntKids, hS.cnt]
      · intro b; simp only [recsKids, hS.recs]
      · intro b; simp only [kidsList, hS.kids]
      · intro m key'
        cases m with
        | zero => rfl
        | succ m => simp only [slotIdxKids, hS.slot]
      · simp only [slotIdxKids, cntKids]; omega
      · simp only [vlKids, slotIdxKids, hv]
        have hn : ¬ cnt c + slotIdxKids r i key < cnt c := by omega
        rw [List.set_append]; simp only [vl_length, hn, ↓reduceIte,
          show cnt c + slotIdxKids r i key - cnt c = slotIdxKids r i key by omega]
end

/-! ## Walks -/

theorem walk_append {ns : List NodeRec} {s t u : Nat × Nat} {k₁ k₂ : List Nat}
    (h₁ : Walk ns s k₁ t) (h₂ : Walk ns t k₂ u) : Walk ns s (k₁ ++ k₂) u := by
  induction h₁ with
  | nil => exact h₂
  | eps hs _ ih => exact .eps hs (ih h₂)
  | sym hx hs _ ih => exact .sym hx hs (ih h₂)

theorem walk_key {ns : List NodeRec} {n : Nat} {nr : NodeRec}
    (hlx : (nr matches .leaf ..) ∨ (nr matches .ext ..)) (hn : ns[n]? = some nr) :
    ∀ (l : List Nat) (i : Nat), i + l.length = nr.key.length → nr.key.drop i = l →
      (∀ y ∈ l, y < 16) → Walk ns (n, i) l (n, nr.key.length)
  | [], i, hl, _, _ => by simp only [List.length_nil, Nat.add_zero] at hl; subst hl; exact .nil
  | x :: l, i, hl, hd, hy => by
    have hx : nr.key[i]? = some x := by
      have := congrArg (·[0]?) hd
      simpa [List.getElem?_drop] using this
    have hd' : nr.key.drop (i + 1) = l := by
      rw [← List.tail_drop, hd]; rfl
    exact .sym (hy x (by simp)) (.key hn hlx hx)
      (walk_key hlx hn l (i + 1) (by simp at hl; omega) hd' (fun y hy' => hy y (by simp [hy'])))

theorem isPrefix_eq {k key : List Nat} (h : isPrefix k key = true) : key = k ++ key.drop k.length := by
  induction k generalizing key with
  | nil => simp
  | cons a k ih =>
    cases key with
    | nil => simp [isPrefix] at h
    | cons b key =>
      simp only [isPrefix, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
      rw [← ih h]

mutual
theorem walk_recs : ∀ (p : PTrie) (b : Nat) (A B : List NodeRec) (key : List Nat) (x : Bytes),
    A.length = b → (∀ y ∈ key, y < 16) → p.get key = some x →
    ∃ s, Walk (A ++ recs p b ++ B) (b, 0) key s ∧
      Step (A ++ recs p b ++ B) s SYM_END (b + slotIdx p key, 0)
  | .hash _, _, _, _, _, _, _, _, h => by simp [PTrie.get] at h
  | .leaf k s mem, b, A, B, key, x, hA, hy, h => by
    simp only [PTrie.get] at h
    split at h
    · rename_i hk
      have hk : k = key := by simpa using hk
      subst hk
      cases s with
      | ref _ _ => simp [Slot.get] at h
      | val v =>
        have hm := getElem?_mid A [] B (NodeRec.leaf k .touched mem)
        rw [hA] at hm
        refine ⟨(b, k.length), ?_, ?_⟩
        · have := walk_key (nr := .leaf k .touched mem) (.inl rfl) hm k 0 (by simp [NodeRec.key])
            (by simp [NodeRec.key]) hy
          simpa [recs, vslot, NodeRec.key] using this
        · simpa [slotIdx] using Step.endLeaf (ns := A ++ recs (.leaf k (.val v) mem) b ++ B)
            (by simpa [recs, vslot] using hm)
    · cases h
  | .ext k c mem, b, A, B, key, x, hA, hy, h => by
    simp only [PTrie.get] at h
    split at h
    · rename_i hp
      have hc := cnt_pos_of_get h
      have hm := getElem?_mid A (recs c (b + 1)) B (NodeRec.ext k (.node (b + 1)) mem)
      rw [hA] at hm
      have e : A ++ (NodeRec.ext k (.node (b + 1)) mem :: recs c (b + 1)) ++ B =
          (A ++ [NodeRec.ext k (.node (b + 1)) mem]) ++ recs c (b + 1) ++ B := by simp
      have hkey := isPrefix_eq hp
      obtain ⟨s, hw, hs⟩ := walk_recs c (b + 1) (A ++ [NodeRec.ext k (.node (b + 1)) mem]) B _ x
        (by simp [hA]) (fun y hy' => hy y (by rw [hkey]; simp [List.mem_append, hy'])) h
      rw [← e] at hw hs
      have hrec : recs (.ext k c mem) b = NodeRec.ext k (.node (b + 1)) mem :: recs c (b + 1) := by
        simp only [recs, kidOf_of_pos _ hc]
      refine ⟨s, ?_, ?_⟩
      · rw [hrec, hkey]
        refine walk_append (t := (b, k.length)) ?_ (.eps (.eps hm) hw)
        exact walk_key (nr := .ext k (.node (b + 1)) mem) (.inr rfl) hm k 0 (by simp [NodeRec.key])
          (by simp [NodeRec.key]) (fun y hy' => hy y (by rw [hkey]; simp [hy']))
      · rw [hrec]; simp only [slotIdx]
        rwa [show b + (1 + slotIdx c (key.drop k.length)) = b + 1 + slotIdx c (key.drop k.length) by omega]
    · cases h
  | .branch v cs mem, b, A, B, [], x, hA, _, h => by
    simp only [PTrie.get] at h
    match v, h with
    | some (.val w), _ =>
      have hm := getElem?_mid A (recsKids cs (b + 1)) B
        (NodeRec.branch (some .touched) (kidsList cs (b + 1)) mem)
      rw [hA] at hm
      have hm' : (A ++ recs (.branch (some (.val w)) cs mem) b ++ B)[b]? =
          some (NodeRec.branch (some .touched) (kidsList cs (b + 1)) mem) := by
        simpa [recs, vslot] using hm
      exact ⟨(b, 0), .nil, by simpa [slotIdx] using Step.endBranch hm'⟩
  | .branch v cs mem, b, A, B, n :: rest, x, hA, hy, h => by
    simp only [PTrie.get] at h
    have hm := getElem?_mid A (recsKids cs (b + 1)) B
      (NodeRec.branch (v.map vslot) (kidsList cs (b + 1)) mem)
    rw [hA] at hm
    have e : A ++ (NodeRec.branch (v.map vslot) (kidsList cs (b + 1)) mem :: recsKids cs (b + 1)) ++ B =
        (A ++ [NodeRec.branch (v.map vslot) (kidsList cs (b + 1)) mem]) ++ recsKids cs (b + 1) ++ B := by
      simp
    obtain ⟨cid, s, hk, hw, hs⟩ := walkKids_recs cs (b + 1)
      (A ++ [NodeRec.branch (v.map vslot) (kidsList cs (b + 1)) mem]) B n rest x (by simp [hA])
      (fun y hy' => hy y (by simp [hy'])) h
    rw [← e] at hw hs
    refine ⟨s, ?_, ?_⟩
    · exact .sym (hy n (by simp)) (.child hm hk) hw
    · simp only [slotIdx]
      rwa [show b + (1 + slotIdxKids cs n rest) = b + 1 + slotIdxKids cs n rest by omega]
theorem walkKids_recs : ∀ (cs : Kids) (b : Nat) (A B : List NodeRec) (n : Nat) (key : List Nat)
    (x : Bytes), A.length = b → (∀ y ∈ key, y < 16) → Kids.get cs n key = some x →
    ∃ cid s, (kidsList cs b)[n]? = some (Kid.node cid) ∧
      Walk (A ++ recsKids cs b ++ B) (cid, 0) key s ∧
      Step (A ++ recsKids cs b ++ B) s SYM_END (b + slotIdxKids cs n key, 0)
  | .nil, _, _, _, _, _, _, _, _, h => by simp [Kids.get] at h
  | .none _, _, _, _, 0, _, _, _, _, h => by simp [Kids.get] at h
  | .some c r, b, A, B, 0, key, x, hA, hy, h => by
    simp only [Kids.get] at h
    have hc := cnt_pos_of_get h
    have e : A ++ recsKids (.some c r) b ++ B = A ++ recs c b ++ (recsKids r (b + cnt c) ++ B) := by
      simp [recsKids]
    obtain ⟨s, hw, hs⟩ := walk_recs c b A (recsKids r (b + cnt c) ++ B) key x hA hy h
    rw [← e] at hw hs
    exact ⟨b, s, by simp [kidsList, kidOf_of_pos _ hc], hw, by simpa [slotIdxKids] using hs⟩
  | .none r, b, A, B, i + 1, key, x, hA, hy, h => by
    simp only [Kids.get] at h
    obtain ⟨cid, s, hk, hw, hs⟩ := walkKids_recs r b A B i key x hA hy h
    exact ⟨cid, s, by simpa [kidsList] using hk, by simpa [recsKids] using hw,
      by simpa [recsKids, slotIdxKids] using hs⟩
  | .some c r, b, A, B, i + 1, key, x, hA, hy, h => by
    simp only [Kids.get] at h
    have e : A ++ recsKids (.some c r) b ++ B = (A ++ recs c b) ++ recsKids r (b + cnt c) ++ B := by
      simp [recsKids]
    obtain ⟨cid, s, hk, hw, hs⟩ := walkKids_recs r (b + cnt c) (A ++ recs c b) B i key x
      (by simp [hA, recs_length]) hy h
    rw [← e] at hw hs
    refine ⟨cid, s, by simpa [kidsList] using hk, hw, ?_⟩
    simp only [slotIdxKids]
    rwa [show b + (cnt c + slotIdxKids r i key) = b + cnt c + slotIdxKids r i key by omega]
end

theorem walkTo_recs (p : PTrie) (key : List Nat) (x : Bytes) (hy : ∀ y ∈ key, y < 16)
    (h : p.get key = some x) : WalkTo (recs p 0) key (slotIdx p key) := by
  obtain ⟨s, hw, hs⟩ := walk_recs p 0 [] [] key x rfl hy h
  exact ⟨s, by simpa using hw, by simpa using hs⟩

/-! ## Touched records -/

mutual
theorem recs_touched : ∀ (p : PTrie) (b i : Nat) (nr : NodeRec), (recs p b)[i]? = some nr →
    nr.touched = true → ∃ v, (vl p)[i]? = some (some v)
  | .hash _, _, _, _, h, _ => by simp [recs] at h
  | .leaf k s mem, b, i, nr, h, ht => by
    match i, h with
    | 0, h =>
      simp only [recs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      cases s with
      | val v => exact ⟨v, by simp [vl, Slot.get]⟩
      | ref _ _ => simp [vslot, NodeRec.touched] at ht
  | .ext k c mem, b, i, nr, h, ht => by
    match i, h with
    | 0, h =>
      simp only [recs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp [NodeRec.touched] at ht
    | i + 1, h =>
      simp only [recs, List.getElem?_cons_succ] at h
      simpa [vl] using recs_touched c (b + 1) i nr h ht
  | .branch bv cs mem, b, i, nr, h, ht => by
    match i, h with
    | 0, h =>
      simp only [recs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      match bv, ht with
      | some (.val v), _ => exact ⟨v, by simp [vl, Slot.get]⟩
      | some (.ref _ _), ht => simp [vslot, NodeRec.touched] at ht
      | none, ht => simp [NodeRec.touched] at ht
    | i + 1, h =>
      simp only [recs, List.getElem?_cons_succ] at h
      simpa [vl] using recsKids_touched cs (b + 1) i nr h ht
theorem recsKids_touched : ∀ (cs : Kids) (b i : Nat) (nr : NodeRec), (recsKids cs b)[i]? = some nr →
    nr.touched = true → ∃ v, (vlKids cs)[i]? = some (some v)
  | .nil, _, _, _, h, _ => by simp [recsKids] at h
  | .none r, b, i, nr, h, ht => by
    simp only [recsKids] at h; simpa [vlKids] using recsKids_touched r b i nr h ht
  | .some c r, b, i, nr, h, ht => by
    simp only [recsKids] at h
    simp only [vlKids]
    rcases Nat.lt_or_ge i (recs c b).length with hi | hi
    · rw [List.getElem?_append_left hi] at h
      rw [recs_length, ← vl_length] at hi
      rw [List.getElem?_append_left hi]; exact recs_touched c b i nr h ht
    · rw [List.getElem?_append_right hi] at h
      rw [recs_length, ← vl_length] at hi
      rw [List.getElem?_append_right hi, vl_length, ← recs_length c b]
      exact recsKids_touched r _ _ nr h ht
end

end ZkFormal.Near.Prune

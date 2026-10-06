import ZkFormal.NearV3.Spec.Rank
import ZkFormal.NearV3.Spec.Occs

/-!
# ZkFormal.NearV3.Spec.TreeRecs — tree-shaped records of a relation-built trie (no A6)

Completeness direction of the store obligation under the lead's decision (V3-D0-DESIGN §11):
records are **tree-shaped** (one record per revealed node *occurrence*, v1 style), and the
AIR proves only **weak** uniqueness (equal digest ⇒ equal bytes).

For any witness store `ws` and the relation's trie `T = partialTrie ws root keys`:

* `recsT τ 0 0 T` — one `NodeRec3` per revealed node occurrence of `T`, pre-order (so
  every child id is larger than its parent's: id order is a rank); `valsT τ T` — one value
  record per revealed value occurrence; `depsT 0 T` — the depth of every record;
* `treeRecs_spec` — these records are a `RootedDag` whose unfolding **is** `T`
  (`fullTree … 0 = T`); every entry of their store is what `storeGet (mkStore ws)` returns
  for its own digest (`EntriesFound`), hence the store is `HashFunctional` and *weakly
  unique* in any digest order; the root digest is `root`; every read key is revealed
  within fuel; child depth = parent depth + 1 and every depth is `< trieFuel = 400`.

No acyclicity or role-clash hypothesis is needed: an occurrence tree is finite, and
`Found` makes the digest ↦ bytes map functional on the entries.

**Size (finding).** The record store's byte count is the *unfolded* size of `T`
(`storeBytes_eq`: `Σ |nodeEnc o|` over occurrences plus `Σ |v|` over value
occurrences), which may exceed `Σ |ws|` when identical subtrees occur at several
positions.  Any AIR has to hash every changed occurrence on a write path to compute the
post-state root, so a cap on the unfolded size is needed for `FitsV3Stmt` with any record
layout (see `docs/zk-formal/STATUS-V3-TRIE.md` §"Unfolded-size cap").
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-! ## Sizes and heights -/

/-- Number of revealed node occurrences. -/
abbrev tsize (t : PTrie) : Nat := (occs t).length
abbrev ksize (cs : Kids) : Nat := (kOccs cs).length

/-- Revealed values of a child list. -/
def kvals (cs : Kids) : List Bytes := (kOccs cs).flatMap ownVals

mutual
def theight : PTrie → Nat
  | .hash _ => 0
  | .leaf .. => 1
  | .ext _ c _ => 1 + theight c
  | .branch _ cs _ => 1 + kheight cs
def kheight : Kids → Nat
  | .nil => 0
  | .none r => kheight r
  | .some c r => max (theight c) (kheight r)
end

theorem valsOf_leaf (k : List Nat) (s : Slot) (m : Nat) : valsOf (.leaf k s m) = slotVal s := by
  simp [tsize, ksize, valsOf, occs, ownVals]
theorem valsOf_ext (k : List Nat) (c : PTrie) (m : Nat) : valsOf (.ext k c m) = valsOf c := by
  simp [tsize, ksize, valsOf, occs, ownVals]
theorem valsOf_branch (v : Option Slot) (cs : Kids) (m : Nat) :
    valsOf (.branch v cs m) = optSlotVal v ++ kvals cs := by
  simp [tsize, ksize, valsOf, occs, ownVals, kvals]
theorem kvals_some (c : PTrie) (r : Kids) : kvals (.some c r) = valsOf c ++ kvals r := by
  simp [tsize, ksize, kvals, kOccs, valsOf, List.flatMap_append]
theorem kvals_none (r : Kids) : kvals (.none r) = kvals r := by simp [tsize, ksize, kvals, kOccs]
theorem kvals_nil : kvals .nil = [] := by simp [tsize, ksize, kvals, kOccs]

/-! ## The records -/

/-- Value slot of a record whose own value (if revealed) is value record `v`. -/
def vslT (v : Nat) : Slot → VSlot3
  | .val _ => .val v
  | .ref l h => .ref l h

/-- Child slot: a revealed child is record `n`. -/
def kidT (n : Nat) (c : PTrie) : Kid3 := if isNode c then .node n else .hash c.hashOf

/-- Child slots of a branch whose first revealed child is record `n`. -/
def kidsT : Nat → Kids → List Kid3
  | _, .nil => []
  | n, .none r => .none :: kidsT n r
  | n, .some c r => kidT n c :: kidsT (n + tsize c) r

/-- The record of a node occurrence with id `n` whose first value id is `v`. -/
def recT (n v : Nat) : PTrie → Rec3
  | .hash _ => .branch none [] 0
  | .leaf k s m => .leaf k (vslT v s) m
  | .ext k c m => .ext k (kidT (n + 1) c) m
  | .branch sv cs m => .branch (sv.map (vslT v)) (kidsT (n + 1) cs) m

mutual
/-- Pre-order records of `t` (ids from `n`, value ids from `v`). -/
def recsT (τ : Nat) : Nat → Nat → PTrie → List NodeRec3
  | _, _, .hash _ => []
  | n, v, .leaf k s m => [⟨τ, recT n v (.leaf k s m)⟩]
  | n, v, .ext k c m => ⟨τ, recT n v (.ext k c m)⟩ :: recsT τ (n + 1) v c
  | n, v, .branch sv cs m => ⟨τ, recT n v (.branch sv cs m)⟩ ::
      krecsT τ (n + 1) (v + (optSlotVal sv).length) cs
def krecsT (τ : Nat) : Nat → Nat → Kids → List NodeRec3
  | _, _, .nil => []
  | n, v, .none r => krecsT τ n v r
  | n, v, .some c r => recsT τ n v c ++ krecsT τ (n + tsize c) (v + (valsOf c).length) r
end

mutual
/-- Depths of the records of `t` (root depth `d`). -/
def depsT : Nat → PTrie → List Nat
  | _, .hash _ => []
  | d, .leaf .. => [d]
  | d, .ext _ c _ => d :: depsT (d + 1) c
  | d, .branch _ cs _ => d :: kdepsT (d + 1) cs
def kdepsT : Nat → Kids → List Nat
  | _, .nil => []
  | d, .none r => kdepsT d r
  | d, .some c r => depsT d c ++ kdepsT d r
end

/-- Value records of `t`. -/
def valsT (τ : Nat) (t : PTrie) : List ValRec3 := (valsOf t).map fun b => ⟨τ, b⟩

mutual
theorem recsT_length (τ : Nat) : ∀ (n v : Nat) (t : PTrie), (recsT τ n v t).length = tsize t
  | _, _, .hash _ => by simp [tsize, ksize, recsT, occs]
  | _, _, .leaf .. => by simp [tsize, ksize, recsT, occs]
  | n, v, .ext k c m => by simp [tsize, ksize, recsT, occs, recsT_length τ (n + 1) v c]
  | n, v, .branch sv cs m => by
    simp [tsize, ksize, recsT, occs, krecsT_length τ (n + 1) (v + (optSlotVal sv).length) cs]
theorem krecsT_length (τ : Nat) : ∀ (n v : Nat) (cs : Kids), (krecsT τ n v cs).length = ksize cs
  | _, _, .nil => by simp [tsize, ksize, krecsT, kOccs]
  | n, v, .none r => by simp [tsize, ksize, krecsT, kOccs, krecsT_length τ n v r]
  | n, v, .some c r => by
    simp [tsize, ksize, krecsT, kOccs, recsT_length τ n v c, krecsT_length τ (n + tsize c) _ r]
end

mutual
theorem depsT_length : ∀ (d : Nat) (t : PTrie), (depsT d t).length = tsize t
  | _, .hash _ => by simp [tsize, ksize, depsT, occs]
  | _, .leaf .. => by simp [tsize, ksize, depsT, occs]
  | d, .ext k c m => by simp [tsize, ksize, depsT, occs, depsT_length (d + 1) c]
  | d, .branch sv cs m => by simp [tsize, ksize, depsT, occs, kdepsT_length (d + 1) cs]
theorem kdepsT_length : ∀ (d : Nat) (cs : Kids), (kdepsT d cs).length = ksize cs
  | _, .nil => by simp [tsize, ksize, kdepsT, kOccs]
  | d, .none r => by simp [tsize, ksize, kdepsT, kOccs, kdepsT_length d r]
  | d, .some c r => by simp [tsize, ksize, kdepsT, kOccs, depsT_length d c, kdepsT_length d r]
end

/-! ## Segments -/

theorem drop_of_append {α : Type} {L a b : List α} {n : Nat} (h : L.drop n = a ++ b) :
    L.drop (n + a.length) = b := by
  rw [← List.drop_drop, h, List.drop_left]

theorem get_of_drop {α : Type} {L r : List α} {n : Nat} {a : α} (h : L.drop n = a :: r) :
    L[n]? = some a := by
  have := congrArg (·[0]?) h; simpa using this

theorem drop_succ_of {α : Type} {L r : List α} {n : Nat} {a : α} (h : L.drop n = a :: r) :
    L.drop (n + 1) = r := by
  have := drop_of_append (a := [a]) (b := r) (h.trans rfl); simpa using this

section Seg

variable (L : List NodeRec3) (VL : List ValRec3) (D : List Nat) (τ : Nat)

/-- `t`'s records, values and depths sit at offsets `n`, `v` of the global lists. -/
structure Seg (n v d : Nat) (t : PTrie) : Prop where
  ns : ∃ r, L.drop n = recsT τ n v t ++ r
  vs : ∃ r, VL.drop v = (valsOf t).map (fun b => (⟨τ, b⟩ : ValRec3)) ++ r
  ds : ∃ r, D.drop n = depsT d t ++ r

structure KSeg (n v d : Nat) (cs : Kids) : Prop where
  ns : ∃ r, L.drop n = krecsT τ n v cs ++ r
  vs : ∃ r, VL.drop v = (kvals cs).map (fun b => (⟨τ, b⟩ : ValRec3)) ++ r
  ds : ∃ r, D.drop n = kdepsT d cs ++ r

variable {L VL D τ}

theorem Seg.ext_kid {n v d : Nat} {k : List Nat} {c : PTrie} {m : Nat}
    (h : Seg L VL D τ n v d (.ext k c m)) : Seg L VL D τ (n + 1) v (d + 1) c := by
  obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := h
  refine ⟨⟨r1, ?_⟩, ⟨r2, by rw [h2, valsOf_ext]⟩, ⟨r3, ?_⟩⟩
  · simp only [recsT, List.cons_append] at h1; exact drop_succ_of h1
  · simp only [depsT, List.cons_append] at h3; exact drop_succ_of h3

theorem Seg.br_kids {n v d : Nat} {sv : Option Slot} {cs : Kids} {m : Nat}
    (h : Seg L VL D τ n v d (.branch sv cs m)) :
    KSeg L VL D τ (n + 1) (v + (optSlotVal sv).length) (d + 1) cs := by
  obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := h
  refine ⟨⟨r1, ?_⟩, ⟨r2, ?_⟩, ⟨r3, ?_⟩⟩
  · simp only [recsT, List.cons_append] at h1; exact drop_succ_of h1
  · rw [valsOf_branch, List.map_append, List.append_assoc] at h2
    have := drop_of_append h2; simpa using this
  · simp only [depsT, List.cons_append] at h3; exact drop_succ_of h3

theorem KSeg.none_r {n v d : Nat} {r : Kids} (h : KSeg L VL D τ n v d (.none r)) :
    KSeg L VL D τ n v d r := by
  obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := h
  exact ⟨⟨r1, by simpa [krecsT] using h1⟩, ⟨r2, by simpa [kvals_none] using h2⟩,
    ⟨r3, by simpa [kdepsT] using h3⟩⟩

theorem KSeg.some_c {n v d : Nat} {c : PTrie} {r : Kids} (h : KSeg L VL D τ n v d (.some c r)) :
    Seg L VL D τ n v d c := by
  obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := h
  simp only [krecsT, List.append_assoc] at h1
  rw [kvals_some, List.map_append, List.append_assoc] at h2
  simp only [kdepsT, List.append_assoc] at h3
  exact ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩

theorem KSeg.some_r {n v d : Nat} {c : PTrie} {r : Kids} (h : KSeg L VL D τ n v d (.some c r)) :
    KSeg L VL D τ (n + tsize c) (v + (valsOf c).length) d r := by
  obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := h
  refine ⟨⟨r1, ?_⟩, ⟨r2, ?_⟩, ⟨r3, ?_⟩⟩
  · simp only [krecsT, List.append_assoc] at h1
    have := drop_of_append h1; rwa [recsT_length] at this
  · rw [kvals_some, List.map_append, List.append_assoc] at h2
    have := drop_of_append h2; simpa using this
  · simp only [kdepsT, List.append_assoc] at h3
    have := drop_of_append h3; rwa [depsT_length] at this

/-! ### At a segment root -/

theorem Seg.get {n v d : Nat} {t : PTrie} (h : Seg L VL D τ n v d t) (hn : isNode t = true) :
    L[n]? = some ⟨τ, recT n v t⟩ ∧ D[n]? = some d := by
  obtain ⟨⟨r1, h1⟩, -, ⟨r3, h3⟩⟩ := h
  cases t with
  | hash => simp [isNode] at hn
  | leaf => simp only [recsT, depsT, List.cons_append, List.nil_append] at h1 h3
            exact ⟨get_of_drop h1, get_of_drop h3⟩
  | ext => simp only [recsT, depsT, List.cons_append] at h1 h3
           exact ⟨get_of_drop h1, get_of_drop h3⟩
  | branch => simp only [recsT, depsT, List.cons_append] at h1 h3
              exact ⟨get_of_drop h1, get_of_drop h3⟩

theorem Seg.val {n v d : Nat} {t : PTrie} (h : Seg L VL D τ n v d t) {x : Bytes}
    (hx : (valsOf t).head? = some x) : VL[v]? = some ⟨τ, x⟩ := by
  obtain ⟨-, ⟨r2, h2⟩, -⟩ := h
  cases hv : valsOf t with
  | nil => rw [hv] at hx; simp at hx
  | cons y ys =>
    rw [hv] at hx h2; simp at hx; subst hx
    exact get_of_drop (by simpa using h2)

theorem slot3_vslT {n v d : Nat} {t : PTrie} (h : Seg L VL D τ n v d t) {s : Slot}
    (hs : ∀ x, s = .val x → (valsOf t).head? = some x) : slot3 VL (vslT v s) = s := by
  cases s with
  | ref => rfl
  | val x =>
    have := h.val (x := x) (hs x rfl)
    simp [vslT, slot3, valOf, this]

mutual
/-- The unfolding at a segment root is the occurrence. -/
theorem Seg.tree : ∀ {n v d : Nat} {t : PTrie}, Seg L VL D τ n v d t → isNode t = true →
    ∀ f, tsize t ≤ f → treeOf3 L VL f n = t
  | _, _, _, .hash _, _, hn, _, _ => by simp [isNode] at hn
  | n, v, d, .leaf k s m, h, _, f, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [tsize, ksize, occs] at hf; omega⟩
    simp only [treeOf3, (h.get rfl).1, nodeTree3, recT]
    rw [slot3_vslT h (fun x hx => by simp [valsOf_leaf, hx, slotVal])]
  | n, v, d, .ext k c m, h, _, f, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [tsize, ksize, occs] at hf; omega⟩
    simp only [treeOf3, (h.get rfl).1, nodeTree3, recT, kidT]
    cases hc : isNode c
    · cases c <;> simp_all [isNode, kidTree3, PTrie.hashOf]
    · simp only [ite_true, kidTree3]
      rw [h.ext_kid.tree hc f (by simp [tsize, ksize, occs] at hf; omega)]
  | n, v, d, .branch sv cs m, h, _, f, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [tsize, ksize, occs] at hf; omega⟩
    simp only [treeOf3, (h.get rfl).1, nodeTree3, recT]
    rw [h.br_kids.tree f (by simp [tsize, ksize, occs] at hf; omega)]
    congr 1
    cases sv with
    | none => rfl
    | some s => simp only [Option.map_some]; rw [slot3_vslT h (fun x hx => by simp [valsOf_branch, optSlotVal, hx, slotVal])]
theorem KSeg.tree : ∀ {n v d : Nat} {cs : Kids}, KSeg L VL D τ n v d cs →
    ∀ f, ksize cs ≤ f → kidsOf3 (treeOf3 L VL f) (kidsT n cs) = cs
  | _, _, _, .nil, _, _, _ => rfl
  | n, v, d, .none r, h, f, hf => by
    simp only [kidsT, kidsOf3]
    rw [h.none_r.tree f (by simpa [ksize, kOccs] using hf)]
  | n, v, d, .some c r, h, f, hf => by
    have hr := h.some_r.tree f (by simp only [ksize, kOccs, List.length_append] at hf; show (kOccs r).length ≤ f; omega)
    simp only [kidsT, kidT]
    cases hc : isNode c
    · cases c <;> simp_all [isNode, kidsOf3, PTrie.hashOf]
    · simp only [ite_true, kidsOf3, hr]
      rw [h.some_c.tree hc f (by simp only [ksize, kOccs, List.length_append] at hf; show (occs c).length ≤ f; omega)]
end

end Seg

section Seg2

variable {L : List NodeRec3} {VL : List ValRec3} {D : List Nat} {τ : Nat}

mutual
/-- Every index of a segment is the root of the segment of the corresponding occurrence. -/
theorem Seg.all : ∀ {n v d : Nat} {t : PTrie}, Seg L VL D τ n v d t →
    ∀ i < tsize t, ∃ o, (occs t)[i]? = some o ∧
      ∃ v' d', Seg L VL D τ (n + i) v' d' o ∧ d' + theight o ≤ d + theight t
  | _, _, _, .hash _, _, i, hi => by simp [tsize, occs] at hi
  | n, v, d, .leaf k s m, h, i, hi => by
    simp [tsize, occs] at hi; subst hi
    exact ⟨_, by simp [occs], v, d, h, Nat.le_refl _⟩
  | n, v, d, .ext k c m, h, i, hi => by
    cases i with
    | zero => exact ⟨_, by simp [occs], v, d, h, Nat.le_refl _⟩
    | succ j =>
      have hj : j < tsize c := by simp [tsize, occs] at hi; omega
      obtain ⟨o, ho, v', d', hs, hb⟩ := h.ext_kid.all j hj
      refine ⟨o, by simpa [occs] using ho, v', d', ?_, ?_⟩
      · have e : n + 1 + j = n + (j + 1) := by omega
        rw [← e]; exact hs
      · simp only [theight]; omega
  | n, v, d, .branch sv cs m, h, i, hi => by
    cases i with
    | zero => exact ⟨_, by simp [occs], v, d, h, Nat.le_refl _⟩
    | succ j =>
      have hj : j < ksize cs := by simp [tsize, ksize, occs] at hi ⊢; omega
      obtain ⟨o, ho, v', d', hs, hb⟩ := h.br_kids.all j hj
      refine ⟨o, by simpa [occs] using ho, v', d', ?_, ?_⟩
      · have e : n + 1 + j = n + (j + 1) := by omega
        rw [← e]; exact hs
      · simp only [theight]; omega
theorem KSeg.all : ∀ {n v d : Nat} {cs : Kids}, KSeg L VL D τ n v d cs →
    ∀ i < ksize cs, ∃ o, (kOccs cs)[i]? = some o ∧
      ∃ v' d', Seg L VL D τ (n + i) v' d' o ∧ d' + theight o ≤ d + kheight cs
  | _, _, _, .nil, _, i, hi => by simp [ksize, kOccs] at hi
  | n, v, d, .none r, h, i, hi => by
    obtain ⟨o, ho, v', d', hs, hb⟩ := h.none_r.all i (by simpa [ksize, kOccs] using hi)
    exact ⟨o, by simpa [kOccs] using ho, v', d', hs, by simpa [kheight] using hb⟩
  | n, v, d, .some c r, h, i, hi => by
    by_cases hc : i < tsize c
    · obtain ⟨o, ho, v', d', hs, hb⟩ := h.some_c.all i hc
      refine ⟨o, ?_, v', d', hs, ?_⟩
      · simp only [kOccs]; rw [List.getElem?_append_left hc]; exact ho
      · simp only [kheight]; have := Nat.le_max_left (theight c) (kheight r); omega
    · have hi' : i - tsize c < ksize r := by
        simp only [tsize, ksize, kOccs, List.length_append] at hi hc ⊢; omega
      obtain ⟨o, ho, v', d', hs, hb⟩ := h.some_r.all (i - tsize c) hi'
      refine ⟨o, ?_, v', d', ?_, ?_⟩
      · simp only [kOccs]; rw [List.getElem?_append_right (by simp only [tsize] at hc; omega)]; exact ho
      · have e : n + tsize c + (i - tsize c) = n + i := by omega
        rw [← e]; exact hs
      · simp only [kheight]; have := Nat.le_max_right (theight c) (kheight r); omega
end

/-- A revealed child slot of a branch record points at the segment of a child occurrence
at depth + 1, with a larger id. -/
theorem KSeg.kid_mem : ∀ {n v d : Nat} {cs : Kids}, KSeg L VL D τ n v d cs → ∀ c,
    Kid3.node c ∈ kidsT n cs → n ≤ c ∧ ∃ co v' , isNode co = true ∧ Seg L VL D τ c v' d co
  | _, _, _, .nil, _, c, hc => by simp [kidsT] at hc
  | n, v, d, .none r, h, c, hc => by
    simp only [kidsT, List.mem_cons, reduceCtorEq, false_or] at hc
    exact h.none_r.kid_mem c hc
  | n, v, d, .some co r, h, c, hc => by
    simp only [kidsT, List.mem_cons] at hc
    rcases hc with hc | hc
    · unfold kidT at hc
      split at hc
      · rename_i hn
        cases hc
        exact ⟨Nat.le_refl _, co, v, hn, h.some_c⟩
      · cases hc
    · obtain ⟨h1, h2⟩ := h.some_r.kid_mem c hc
      exact ⟨by omega, h2⟩

theorem kidsT_length : ∀ (n : Nat) (cs : Kids) (k : Nat), Kids.wf cs k = true → (kidsT n cs).length = k
  | _, .nil, k, h => by simp [Kids.wf] at h; simp [kidsT, h]
  | n, .none r, k, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [kidsT, kidsT_length n r _ h.2]; omega
  | n, .some c r, k, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp [kidsT, kidsT_length _ r _ h.2]; omega

theorem kidT_wf {n : Nat} {c : PTrie} (hc : c.wf = true) : (kidT n c).wf ∧ kidT n c ≠ .none := by
  unfold kidT
  split
  · exact ⟨trivial, by simp⟩
  · exact ⟨hashOf_len_of_wf c hc, by simp⟩

theorem kidsT_wf : ∀ (n : Nat) (cs : Kids) (k : Nat), Kids.wf cs k = true → ∀ x ∈ kidsT n cs, x.wf
  | _, .nil, _, _, x, hx => by simp [kidsT] at hx
  | n, .none r, k, h, x, hx => by
    simp only [kidsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · trivial
    · exact kidsT_wf n r _ (wf_kids_none h) x hx
  | n, .some c r, k, h, x, hx => by
    simp only [kidsT, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (kidT_wf (wf_kids_some h).1).1
    · exact kidsT_wf _ r _ (wf_kids_some h).2 x hx

/-- The record at a segment root is well formed. -/
theorem Seg.rec_wf {n v d : Nat} {t : PTrie} (h : Seg L VL D τ n v d t) (hw : t.wf = true)
    (hn : isNode t = true) : (recT n v t).wf VL := by
  have hval : ∀ s : Slot, slotOk s = true → (∀ x, s = .val x → (valsOf t).head? = some x) →
      (vslT v s).wf VL := by
    intro s hs hh
    cases s with
    | ref l hh' => simpa [vslT, VSlot3.wf, slotOk] using hs
    | val x =>
      have := h.val (hh x rfl)
      simp only [vslT, VSlot3.wf, valOf, this, Option.map_some, Option.getD_some]
      simpa [slotOk] using hs
  cases t with
  | hash => simp [isNode] at hn
  | leaf k sl m =>
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    exact ⟨h1, h4, hval sl h2 (fun x hx => by simp [valsOf_leaf, hx, slotVal]), h3⟩
  | ext k c m =>
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    have hk := kidT_wf (n := n + 1) h2
    exact ⟨h1, h4, hk.2, hk.1, h3⟩
  | branch bv cs m =>
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    refine ⟨kidsT_length _ cs 16 h2, ?_, kidsT_wf _ cs 16 h2, h3⟩
    intro sl hsl
    cases bv with
    | none => simp at hsl
    | some sl0 =>
      simp at hsl; subst hsl
      exact hval sl0 (by simpa using h1) (fun x hx => by simp [valsOf_branch, optSlotVal, hx, slotVal])

/-- Value ids referenced by a segment-root record exist, in instance `τ`. -/
theorem Seg.rec_vals {n v d : Nat} {t : PTrie} (h : Seg L VL D τ n v d t) :
    ∀ i ∈ (recT n v t).vids, ∃ vr : ValRec3, VL[i]? = some vr ∧ vr.tau = τ := by
  intro i hi
  cases t with
  | hash => simp [recT, Rec3.vids] at hi
  | ext => simp [recT, Rec3.vids] at hi
  | leaf k sl m =>
    cases sl with
    | ref => simp [recT, vslT, Rec3.vids] at hi
    | val x =>
      simp [recT, vslT, Rec3.vids] at hi; subst hi
      exact ⟨_, h.val (x := x) (by simp [valsOf_leaf, slotVal]), rfl⟩
  | branch bv cs m =>
    cases bv with
    | none => simp [recT, Rec3.vids] at hi
    | some sl =>
      cases sl with
      | ref => simp [recT, vslT, Rec3.vids] at hi
      | val x =>
        simp [recT, vslT, Rec3.vids] at hi; subst hi
        exact ⟨_, h.val (x := x) (by simp [valsOf_branch, optSlotVal, slotVal]), rfl⟩

theorem Seg.len {n v d : Nat} {t : PTrie} (h : Seg L VL D τ n v d t) : tsize t ≤ L.length - n := by
  obtain ⟨⟨r, hr⟩, -, -⟩ := h
  have := congrArg List.length hr
  simp only [List.length_drop, List.length_append, recsT_length] at this
  omega

end Seg2

/-! ## Heights and `fdepth` -/

theorem isPrefix_append : ∀ (k x : List Nat), isPrefix k (k ++ x) = true
  | [], _ => by simp [isPrefix]
  | a :: k, x => by simp [isPrefix, isPrefix_append k x]

mutual
/-- Some key visits as many revealed nodes as the height. -/
theorem exists_fdepth : ∀ t : PTrie, ∃ key, fdepth t key = theight t
  | .hash _ => ⟨[], by simp [fdepth, theight]⟩
  | .leaf .. => ⟨[], by simp [fdepth, theight]⟩
  | .ext k c m => by
    obtain ⟨kc, hk⟩ := exists_fdepth c
    refine ⟨k ++ kc, ?_⟩
    simp [fdepth, theight, isPrefix_append, hk]
  | .branch v cs m => by
    obtain ⟨n, r, hk⟩ := exists_kfdepth cs
    exact ⟨n :: r, by simp [fdepth, theight, hk]⟩
theorem exists_kfdepth : ∀ cs : Kids, ∃ n r, kfdepth cs n r = kheight cs
  | .nil => ⟨0, [], by simp [kfdepth, kheight]⟩
  | .none r => by
    obtain ⟨n, k, hk⟩ := exists_kfdepth r
    exact ⟨n + 1, k, by simp [kfdepth, kheight, hk]⟩
  | .some c r => by
    by_cases hle : kheight r ≤ theight c
    · obtain ⟨k, hk⟩ := exists_fdepth c
      exact ⟨0, k, by simp [kfdepth, kheight, hk]; omega⟩
    · obtain ⟨n, k, hk⟩ := exists_kfdepth r
      exact ⟨n + 1, k, by simp [kfdepth, kheight, hk]; omega⟩
end

theorem theight_le_of_fdepth {t : PTrie} {f : Nat} (h : ∀ k, fdepth t k ≤ f) : theight t ≤ f := by
  obtain ⟨k, hk⟩ := exists_fdepth t
  rw [← hk]; exact h k

/-! ## The records of a relation-built trie -/

/-- Every store entry of instance `τ` is what `s` returns for its own digest. -/
def EntriesFound (s : Store) (ns : List NodeRec3) (vs : List ValRec3) (τ : Nat) : Prop :=
  ∀ e ∈ storeOf ns vs τ, Found s e

theorem hashFunctional_of_found {s : Store} {l : List Bytes} (h : ∀ e ∈ l, Found s e) :
    HashFunctional l := fun a ha b hb he => found_inj (h a ha) (h b hb) he

/-- Unfolded revealed bytes of a partial trie: every node occurrence and value occurrence. -/
def unfoldedBytes (t : PTrie) : Nat :=
  ((occs t).map fun o => (nodeEnc o).length).sum + ((valsOf t).map List.length).sum

section Main

variable (τ : Nat) (T : PTrie)

theorem seg0 : Seg (recsT τ 0 0 T) (valsT τ T) (depsT 0 T) τ 0 0 0 T :=
  ⟨⟨[], by simp⟩, ⟨[], by simp [valsT]⟩, ⟨[], by simp⟩⟩

variable {τ T}

theorem rec_at {i : Nat} (hi : i < (recsT τ 0 0 T).length) :
    ∃ o, (occs T)[i]? = some o ∧ ∃ v' d', Seg (recsT τ 0 0 T) (valsT τ T) (depsT 0 T) τ i v' d' o ∧
      d' + theight o ≤ theight T := by
  rw [recsT_length] at hi
  obtain ⟨o, ho, v', d', hs, hb⟩ := (seg0 τ T).all i hi
  exact ⟨o, ho, v', d', by simpa using hs, by simpa using hb⟩

theorem all_tau {i : Nat} {nr : NodeRec3} (h : (recsT τ 0 0 T)[i]? = some nr) : nr.tau = τ := by
  obtain ⟨o, ho, v', d', hs, -⟩ := rec_at (List.getElem?_eq_some_iff.1 h).1
  rw [(hs.get (occs_isNode T o (List.mem_of_getElem? ho))).1] at h
  cases h; rfl

theorem inInst_iff {i : Nat} : InInst (recsT τ 0 0 T) τ i ↔ i < (recsT τ 0 0 T).length := by
  constructor
  · exact InInst.lt
  · intro hi
    obtain ⟨nr, hnr⟩ : ∃ nr, (recsT τ 0 0 T)[i]? = some nr := ⟨_, List.getElem?_eq_getElem hi⟩
    exact ⟨nr, hnr, all_tau hnr⟩

/-- The unfolding of record `i` is the `i`-th occurrence. -/
theorem fullTree_at {i : Nat} {o : PTrie} (ho : (occs T)[i]? = some o) :
    fullTree (recsT τ 0 0 T) (valsT τ T) i = o := by
  have hi : i < (recsT τ 0 0 T).length := by
    rw [recsT_length]; exact (List.getElem?_eq_some_iff.1 ho).1
  obtain ⟨o', ho', v', d', hs, -⟩ := rec_at hi
  rw [ho] at ho'; cases ho'
  exact hs.tree (occs_isNode T o (List.mem_of_getElem? ho)) _ (by have := hs.len; omega)

theorem rootedT (hw : T.wf = true) (hn : isNode T = true) :
    RootedDag (recsT τ 0 0 T) (valsT τ T) τ 0 where
  root_inst := inInst_iff.2 (by rw [recsT_length]; exact List.length_pos_of_mem (self_mem_occs hn))
  child := by
    intro n nr hnr _ c hc
    obtain ⟨o, ho, v', d', hs, -⟩ := rec_at (List.getElem?_eq_some_iff.1 hnr).1
    have hon := occs_isNode T o (List.mem_of_getElem? ho)
    rw [(hs.get hon).1] at hnr; cases hnr
    cases o with
    | hash => simp [isNode] at hon
    | leaf => simp [recT, Rec3.kids] at hc
    | ext k c0 m =>
      simp only [recT, Rec3.kids, List.mem_singleton, kidT] at hc
      split at hc
      · rename_i hc0; cases hc
        have := hs.ext_kid.get hc0
        exact ⟨by omega, inInst_iff.2 (List.getElem?_eq_some_iff.1 this.1).1⟩
      · cases hc
    | branch bv cs m =>
      simp only [recT, Rec3.kids] at hc
      obtain ⟨hle, co, v'', hco, hs'⟩ := hs.br_kids.kid_mem c hc
      exact ⟨by omega, inInst_iff.2 (List.getElem?_eq_some_iff.1 (hs'.get hco).1).1⟩
  vals := by
    intro n nr hnr _
    obtain ⟨o, ho, v', d', hs, -⟩ := rec_at (List.getElem?_eq_some_iff.1 hnr).1
    rw [(hs.get (occs_isNode T o (List.mem_of_getElem? ho))).1] at hnr; cases hnr
    exact hs.rec_vals
  wf := by
    intro n nr hnr _
    obtain ⟨o, ho, v', d', hs, -⟩ := rec_at (List.getElem?_eq_some_iff.1 hnr).1
    rw [(hs.get (occs_isNode T o (List.mem_of_getElem? ho))).1] at hnr; cases hnr
    exact hs.rec_wf (occs_wf T hw o (List.mem_of_getElem? ho)) (occs_isNode T o (List.mem_of_getElem? ho))

theorem filterMap_range' {α β : Type} (f : Nat → Option β) (g : α → β) :
    ∀ (s : Nat) (l : List α), (∀ i (h : i < l.length), f (s + i) = some (g l[i])) →
      (List.range' s l.length).filterMap f = l.map g
  | _, [], _ => rfl
  | s, a :: l, h => by
    simp only [List.length_cons, List.range'_succ, List.filterMap_cons, List.map_cons]
    have h0 := h 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, filterMap_range' f g (s + 1) l (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)]

theorem nodeEntries_T (_hn : isNode T = true) :
    nodeEntries (recsT τ 0 0 T) (valsT τ T) τ = (occs T).map nodeEnc := by
  unfold nodeEntries
  rw [List.range_eq_range', recsT_length]
  apply filterMap_range'
  intro i hi
  have hi' : i < (recsT τ 0 0 T).length := by rw [recsT_length]; exact hi
  obtain ⟨nr, hnr⟩ : ∃ nr, (recsT τ 0 0 T)[i]? = some nr := ⟨_, List.getElem?_eq_getElem hi'⟩
  simp only [Nat.zero_add, hnr, all_tau hnr, ite_true]
  rw [fullTree_at (List.getElem?_eq_getElem hi)]

theorem valEntries_T : valEntries (valsT τ T) τ = valsOf T := by
  simp [valEntries, valsT, List.filter_map, Function.comp_def]

theorem storeOf_T (hn : isNode T = true) :
    storeOf (recsT τ 0 0 T) (valsT τ T) τ = (occs T).map nodeEnc ++ valsOf T := by
  rw [storeOf, nodeEntries_T hn, valEntries_T]

end Main

/-- **Tree-shaped records of the relation's trie** (completeness, no A6). -/
theorem treeRecs_spec (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) (τ : Nat)
    (hroot : root.length = 32) (hne : keys ≠ [])
    (hread : ∀ k ∈ keys, (partialTrie ws root keys).find k ≠ none) :
    RootedDag (recsT τ 0 0 (partialTrie ws root keys)) (valsT τ (partialTrie ws root keys)) τ 0 ∧
    fullTree (recsT τ 0 0 (partialTrie ws root keys)) (valsT τ (partialTrie ws root keys)) 0 =
      partialTrie ws root keys ∧
    digest (recsT τ 0 0 (partialTrie ws root keys)) (valsT τ (partialTrie ws root keys)) 0 = root ∧
    EntriesFound (mkStore ws) (recsT τ 0 0 (partialTrie ws root keys))
      (valsT τ (partialTrie ws root keys)) τ ∧
    HashFunctional (storeOf (recsT τ 0 0 (partialTrie ws root keys)) (valsT τ (partialTrie ws root keys)) τ) ∧
    PathsRevealed (recsT τ 0 0 (partialTrie ws root keys)) (valsT τ (partialTrie ws root keys)) 0 keys ∧
    (∀ (n : Nat) (nr : NodeRec3), (recsT τ 0 0 (partialTrie ws root keys))[n]? = some nr →
      ∀ c, Kid3.node c ∈ nr.node.kids →
      (depsT 0 (partialTrie ws root keys))[c]? = (depsT 0 (partialTrie ws root keys))[n]?.map (· + 1)) ∧
    (∀ n < (recsT τ 0 0 (partialTrie ws root keys)).length,
      ∃ d, (depsT 0 (partialTrie ws root keys))[n]? = some d ∧ d < trieFuel) ∧
    (depsT 0 (partialTrie ws root keys))[0]? = some 0 ∧
    storeBytes (recsT τ 0 0 (partialTrie ws root keys)) (valsT τ (partialTrie ws root keys)) τ =
      unfoldedBytes (partialTrie ws root keys) := by
  obtain ⟨hh, hw, hst, hdep⟩ := built_spec ws trieFuel root keys hroot
  have hT : partialTrie ws root keys = buildFor (mkStore ws) trieFuel root keys := rfl
  rw [← hT] at hh hw hst hdep
  generalize partialTrie ws root keys = T at hh hw hst hdep hread ⊢
  have hnode : isNode T = true := by
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil keys hne
    have := hread k hk
    cases T with
    | hash h => exact absurd (find_hash_none h k) this
    | _ => rfl
  have h0 : (occs T)[0]? = some T := by cases T <;> simp_all [isNode, occs]
  have hfull := fullTree_at (τ := τ) h0
  have hheight := theight_le_of_fdepth hdep
  have hfound : EntriesFound (mkStore ws) (recsT τ 0 0 T) (valsT τ T) τ := by
    intro e he
    rw [storeOf_T hnode, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
      exact stored_found (occs_stored _ T hst o ho) (occs_isNode T o ho)
    · obtain ⟨o, ho, hv⟩ := List.mem_flatMap.1 he
      exact stored_ownVals (occs_stored _ T hst o ho) e hv
  refine ⟨rootedT hw hnode, hfull, ?_, hfound, hashFunctional_of_found hfound, ?_, ?_, ?_, ?_, ?_⟩
  · unfold digest; rw [hfull, hh]
  · intro k hk; rw [hfull]; exact ⟨hread k hk, hdep k⟩
  · intro n nr hnr c hc
    obtain ⟨o, ho, v', d', hs, -⟩ := rec_at (List.getElem?_eq_some_iff.1 hnr).1
    have hon := occs_isNode T o (List.mem_of_getElem? ho)
    rw [(hs.get hon).1] at hnr; cases hnr
    rw [(hs.get hon).2]
    cases o with
    | hash => simp [isNode] at hon
    | leaf => simp [recT, Rec3.kids] at hc
    | ext k c0 m =>
      simp only [recT, Rec3.kids, List.mem_singleton, kidT] at hc
      split at hc
      · rename_i hc0; cases hc
        rw [(hs.ext_kid.get hc0).2]; rfl
      · cases hc
    | branch bv cs m =>
      simp only [recT, Rec3.kids] at hc
      obtain ⟨-, co, v'', hco, hs'⟩ := hs.br_kids.kid_mem c hc
      rw [(hs'.get hco).2]; rfl
  · intro n hn
    obtain ⟨o, ho, v', d', hs, hb⟩ := rec_at hn
    have hon := occs_isNode T o (List.mem_of_getElem? ho)
    refine ⟨d', (hs.get hon).2, ?_⟩
    have : 1 ≤ theight o := by cases o <;> simp_all [isNode, theight]
    omega
  · exact ((seg0 τ T).get hnode).2
  · unfold storeBytes unfoldedBytes; rw [storeOf_T hnode, List.map_append, List.sum_append, List.map_map]; rfl


end ZkFormal.NearV3

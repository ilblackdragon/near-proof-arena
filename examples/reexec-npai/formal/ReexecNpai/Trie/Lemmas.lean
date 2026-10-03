import ReexecNpai.Trie.Arena

/-!
# Pure lemmas about the arena representation

* `hashOf_treeAt`: the node hash of `treeAt j` is the SHA-256 of `preImg`
  with the value hash and the children's hashes in the placeholders;
* `treeAt_local`: `treeAt j` only depends on the values of the entries of
  its subtree `[lo j, j]`;
* `res_spec`: `res` points to `j` itself, or skips extensions with empty key;
* `walk_get_set`: a walk to `f` means `get` returns `vals f` and `set` is the
  point update of `vals` at `f`;
* `get_walk`: conversely every successful `get` from the root is a walk.
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-- Point update of the value function. -/
def updVals (vals : Nat → Bytes) (f : Nat) (nv : Bytes) : Nat → Bytes := fun x => if x = f then nv else vals x

/-! ## Helper lemmas -/


theorem nodeWF_of {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    e.lo ≤ j ∧ (nKids e.nf = 0 → e.lo = j) ∧
    (∀ q, q < nKids e.nf →
      ∃ ec, A[childIdx K e.kid (nKids e.nf) q]? = some ec ∧ childIdx K e.kid (nKids e.nf) q < j ∧
        ec.lo = (if q = 0 then e.lo else childIdx K e.kid (nKids e.nf) (q - 1) + 1) ∧
        (q + 1 = nKids e.nf → childIdx K e.kid (nKids e.nf) q + 1 = j)) ∧
    e.res = (match e.nf with
             | .ext [] none _ => (A.getD (K.getD e.kid 0) e).res
             | .ext [] (some _) _ => RNONE
             | _ => j) := by
  have hl : j < A.length := by
    rcases Nat.lt_or_ge j A.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  obtain ⟨e', he', -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := hw.nodes j hl
  rw [hj] at he'; cases he'
  refine ⟨h1, h2, ?_, h4⟩
  intro q hq
  obtain ⟨ec, a, b, -, c, d⟩ := h3 q hq
  exact ⟨ec, a, b, c, d⟩

theorem treeAt_leaf {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {k ref mm} (hn : e.nf = .leaf k ref mm) :
    treeAt A K vals j = .leaf k (slotOfRef ref (vals j)) mm := by
  rw [treeAt, hj]; simp only [hn]

theorem treeAt_exth {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {k hh mm} (hn : e.nf = .ext k (some hh) mm) :
    treeAt A K vals j = .ext k (.hash hh) mm := by
  rw [treeAt, hj]; simp only [hn]

theorem treeAt_ext {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {k mm} (hn : e.nf = .ext k none mm) :
    treeAt A K vals j = .ext k (if K.getD e.kid 0 < j then treeAt A K vals (K.getD e.kid 0) else .hash []) mm := by
  rw [treeAt, hj]; simp only [hn]

theorem treeAt_branch {A : List Ent} {K : List Nat} {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    {v ks mm} (hn : e.nf = .branch v ks mm) :
    treeAt A K vals j = .branch (v.map fun r => slotOfRef r (vals j))
        (kidsOf (fun q => if childIdx K e.kid (nRev ks) q < j then
            treeAt A K vals (childIdx K e.kid (nRev ks) q) else .hash []) ks 0) mm := by
  rw [treeAt, hj]; simp only [hn]



@[simp] theorem nRev_nil : nRev [] = 0 := rfl
@[simp] theorem revBelow_zero (ks : List (Option (Option Bytes))) : revBelow ks 0 = 0 := by
  simp [revBelow]

theorem nRev_cons (x : Option (Option Bytes)) (r : List (Option (Option Bytes))) :
    nRev (x :: r) = nRev r + (if x = some none then 1 else 0) := by
  unfold nRev; rw [List.countP_cons]; cases x with
  | none => simp
  | some y => cases y <;> simp

macro "nrev_tac" : tactic => `(tactic| first | omega | (simp only [nRev_cons, reduceCtorEq, ite_true, ite_false, Option.some.injEq] at *; omega) | (simp [nRev_cons] at *; omega) | simp [nRev_cons] at *)

theorem kidsBitmap_kidsOf (f : Nat → PTrie) (ks : List (Option (Option Bytes))) (q i : Nat) :
    kidsBitmap (kidsOf f ks q) i = bitsPres ks i := by
  induction ks generalizing q i with
  | nil => rfl
  | cons x r ih =>
    rcases x with _ | _ | h <;> simp [kidsOf, kidsBitmap, bitsPres, ih]

theorem hashes_kidsOf (f : Nat → PTrie) (ks : List (Option (Option Bytes))) (q : Nat) :
    Kids.hashes (kidsOf f ks q) = slotBytes ks ((List.range (nRev ks)).map fun p => (f (q + p)).hashOf) := by
  induction ks generalizing q with
  | nil => rfl
  | cons x r ih =>
    rcases x with _ | _ | h
    · simp [kidsOf, Kids.hashes, slotBytes, ih, nRev_cons]
    · simp only [kidsOf, Kids.hashes, slotBytes, ih, nRev_cons]
      simp only [ite_true, List.range_succ_eq_map, List.map_cons, List.map_map, List.headD_cons,
        List.tail_cons, Nat.add_zero]
      congr 2
      apply List.map_congr_left; intro p _; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 p]
    · simp [kidsOf, Kids.hashes, slotBytes, ih, nRev_cons, PTrie.hashOf]

theorem kidsOf_congr (f g : Nat → PTrie) (ks : List (Option (Option Bytes))) (q : Nat)
    (h : ∀ p, q ≤ p → p < q + nRev ks → f p = g p) : kidsOf f ks q = kidsOf g ks q := by
  induction ks generalizing q with
  | nil => rfl
  | cons x r ih =>
    rcases x with _ | _ | hh
    · simp only [kidsOf]; rw [ih]; intro p h1 h2; apply h p h1; nrev_tac
    · simp only [kidsOf]; rw [ih, h q (Nat.le_refl _)]
      · rw [nRev_cons]; simp
      · intro p h1 h2; apply h p (by omega); nrev_tac
    · simp only [kidsOf]; rw [ih]; intro p h1 h2; apply h p h1; nrev_tac

theorem revBelow_succ (x : Option (Option Bytes)) (r : List (Option (Option Bytes))) (n : Nat) :
    revBelow (x :: r) (n + 1) = revBelow r n + (if x = some none then 1 else 0) := by
  unfold revBelow; rw [List.take_succ_cons, nRev_cons]

theorem revBelow_lt (ks : List (Option (Option Bytes))) (n : Nat) (h : ks[n]? = some (some none)) :
    revBelow ks n < nRev ks := by
  induction ks generalizing n with
  | nil => simp at h
  | cons x r ih =>
    cases n with
    | zero => simp at h; subst h; simp [revBelow, nRev_cons]
    | succ n => simp at h; have := ih n h; rw [revBelow_succ, nRev_cons]; split <;> omega

theorem get_kidsOf (f : Nat → PTrie) (ks : List (Option (Option Bytes))) (q n : Nat) (rest : List Nat) :
    Kids.get (kidsOf f ks q) n rest =
      if ks[n]? = some (some none) then (f (q + revBelow ks n)).get rest else none := by
  induction ks generalizing q n with
  | nil => simp [kidsOf, Kids.get]
  | cons x r ih =>
    cases n with
    | zero =>
      rcases x with _ | _ | hh <;> simp [kidsOf, Kids.get, revBelow, PTrie.get]
    | succ n =>
      rcases x with _ | _ | hh <;> simp [kidsOf, Kids.get, ih, revBelow_succ, Nat.add_assoc, Nat.add_comm 1]

theorem set_kidsOf (f g : Nat → PTrie) (ks : List (Option (Option Bytes))) (q n : Nat) (rest : List Nat) (nv : Bytes)
    (hn : ks[n]? = some (some none))
    (hs : (f (q + revBelow ks n)).set rest nv = some (g (q + revBelow ks n)))
    (ho : ∀ p, p ≠ q + revBelow ks n → q ≤ p → p < q + nRev ks → f p = g p) :
    Kids.set (kidsOf f ks q) n rest nv = some (kidsOf g ks q) := by
  induction ks generalizing q n with
  | nil => simp at hn
  | cons x r ih =>
    cases n with
    | zero =>
      simp at hn; subst hn
      simp only [revBelow_zero, Nat.add_zero] at hs ho
      simp only [kidsOf, Kids.set, hs, Option.map_some]
      rw [kidsOf_congr f g r (q+1)]
      intro p h1 h2; apply ho p (by omega) (by omega); nrev_tac
    | succ n =>
      simp at hn
      rw [revBelow_succ] at hs ho
      rcases x with _ | _ | hh
      · simp only [kidsOf, Kids.set]
        rw [ih q n hn (by simpa using hs)]; (try rfl)
        intro p h1 h2 h3; apply ho p (by simpa using h1) h2; nrev_tac
      · simp only [kidsOf, Kids.set]
        rw [ih (q+1) n hn (by simpa [Nat.add_assoc, Nat.add_comm 1] using hs)]
        · simp only [Option.map_some]; rw [ho q (by first | omega | simp | (simp; omega)) (Nat.le_refl _) (by rw [nRev_cons]; simp)]
        intro p h1 h2 h3; apply ho p (by simp; omega) (by omega); nrev_tac
      · simp only [kidsOf, Kids.set]
        rw [ih q n hn (by simpa using hs)]; (try rfl)
        intro p h1 h2 h3; apply ho p (by simpa using h1) h2; nrev_tac


theorem child_info {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {j : Nat} {e : Ent} (hj : A[j]? = some e) {q : Nat} (hq : q < nKids e.nf) :
    ∃ ec, A[childIdx K e.kid (nKids e.nf) q]? = some ec ∧ childIdx K e.kid (nKids e.nf) q < j ∧
      e.lo ≤ ec.lo ∧ ec.lo ≤ childIdx K e.kid (nKids e.nf) q := by
  induction q with
  | zero =>
    obtain ⟨-, -, hc, -⟩ := nodeWF_of hw hj
    obtain ⟨ec, h1, h2, h3, -⟩ := hc 0 hq
    exact ⟨ec, h1, h2, by simp [h3], (nodeWF_of hw h1).1⟩
  | succ q ih =>
    obtain ⟨ep, -, -, h3p, h4p⟩ := ih (by omega)
    obtain ⟨-, -, hc, -⟩ := nodeWF_of hw hj
    obtain ⟨ec, h1, h2, h3, -⟩ := hc (q+1) hq
    refine ⟨ec, h1, h2, ?_, (nodeWF_of hw h1).1⟩
    rw [h3]; simp; omega

theorem child_disj {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {j : Nat} {e : Ent} (hj : A[j]? = some e) {p p' : Nat} (hp : p < p') (hp' : p' < nKids e.nf)
    {ec : Ent} (hc : A[childIdx K e.kid (nKids e.nf) p']? = some ec) :
    childIdx K e.kid (nKids e.nf) p < ec.lo := by
  induction p' generalizing ec with
  | zero => omega
  | succ p' ih =>
    obtain ⟨-, -, hcs, -⟩ := nodeWF_of hw hj
    obtain ⟨ec', h1, -, h3, -⟩ := hcs (p'+1) hp'
    rw [hc] at h1; cases h1
    rw [h3]; simp
    rcases Nat.lt_or_ge p p' with h | h
    · obtain ⟨ep, h1p, -, -, -⟩ := hcs p' (by omega)
      have := ih h (by omega) h1p
      have := (nodeWF_of hw h1p).1
      omega
    · have : p = p' := by omega
      subst this; omega

theorem ext_child {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {j : Nat} {e : Ent} (hj : A[j]? = some e) {k mm} (hn : e.nf = .ext k none mm) :
    ∃ ec, A[K.getD e.kid 0]? = some ec ∧ K.getD e.kid 0 < j ∧
      ec.lo = e.lo ∧ ec.lo ≤ K.getD e.kid 0 := by
  obtain ⟨-, -, hc, -⟩ := nodeWF_of hw hj
  obtain ⟨ec, h1, h2, h3, -⟩ := hc 0 (by simp [hn, nKids])
  have hk : childIdx K e.kid (nKids e.nf) 0 = K.getD e.kid 0 := by simp only [hn, nKids]; rfl
  rw [hk] at h1 h2
  exact ⟨ec, h1, h2, by simpa using h3, (nodeWF_of hw h1).1⟩

theorem getD_of {A : List Ent} {c : Nat} {ec d : Ent} (h : A[c]? = some ec) : A.getD c d = ec := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

theorem isPrefix_append {k key : List Nat} (h : isPrefix k key = true) : k ++ key.drop k.length = key := by
  induction k generalizing key with
  | nil => rfl
  | cons a k ih =>
    cases key with
    | nil => simp [isPrefix] at h
    | cons b key =>
      simp only [isPrefix, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      simp [ih h]

/-- Hashes of the revealed children of entry `e` (ascending nibble order). -/
def childHashes (A : List Ent) (K : List Nat) (vals : Nat → Bytes) (e : Ent) : List Bytes :=
  (List.range (nKids e.nf)).map fun q => (treeAt A K vals (childIdx K e.kid (nKids e.nf) q)).hashOf

theorem hashOf_treeAt {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    (hv : hasVal e.nf = true → (vals j).length = vlenAt pb e) :
    (treeAt A K vals j).hashOf =
      sha256 (preImg e.nf (vlenAt pb e) (sha256 (vals j)) (childHashes A K vals e)) := by
  obtain ⟨-, -, hc, -⟩ := nodeWF_of hw hj
  unfold childHashes
  cases hn : e.nf with
  | leaf k ref mm =>
    rw [treeAt_leaf hj hn]
    cases ref with
    | none =>
      simp [hn, hasVal] at hv
      simp [PTrie.hashOf, preImg, slotOfRef, Slot.valueRef, hv]
    | some p =>
      obtain ⟨len, h⟩ := p
      simp [PTrie.hashOf, preImg, slotOfRef, Slot.valueRef]
  | ext k h mm =>
    cases h with
    | some hh => rw [treeAt_exth hj hn]; simp [PTrie.hashOf, preImg]
    | none =>
      rw [treeAt_ext hj hn]
      have := hc 0 (by simp [hn, nKids])
      simp only [hn, nKids, childIdx] at this
      obtain ⟨ec, -, hlt, -⟩ := this
      simp at hlt
      simp [PTrie.hashOf, preImg, nKids, childIdx, hlt]
  | branch v ks mm =>
    rw [treeAt_branch hj hn]
    rw [kidsOf_congr _ (fun q => treeAt A K vals (childIdx K e.kid (nRev ks) q)) ks 0 (by
      intro p _ hp
      obtain ⟨ec, -, hlt, -⟩ := hc p (by simpa [hn, nKids] using hp)
      simp only [hn, nKids] at hlt
      simp [hlt])]
    have hv' := hv
    simp only [hn, hasVal] at hv'
    rcases v with _ | _ | ⟨len, h⟩
    · simp [PTrie.hashOf, preImg, kidsBitmap_kidsOf, hashes_kidsOf, nKids]
    · simp [PTrie.hashOf, preImg, kidsBitmap_kidsOf, hashes_kidsOf, nKids, slotOfRef, Slot.valueRef, hv']
    · simp [PTrie.hashOf, preImg, kidsBitmap_kidsOf, hashes_kidsOf, nKids, slotOfRef, Slot.valueRef]

theorem treeAt_local {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals vals' : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e)
    (h : ∀ x, e.lo ≤ x → x ≤ j → vals x = vals' x) :
    treeAt A K vals j = treeAt A K vals' j := by
  induction j using Nat.strongRecOn generalizing e with
  | _ j ih =>
  obtain ⟨hlo, -, -, -⟩ := nodeWF_of hw hj
  cases hn : e.nf with
  | leaf k ref mm => rw [treeAt_leaf hj hn, treeAt_leaf hj hn, h j hlo (Nat.le_refl _)]
  | ext k h' mm =>
    cases h' with
    | some hh => rw [treeAt_exth hj hn, treeAt_exth hj hn]
    | none =>
      rw [treeAt_ext hj hn, treeAt_ext hj hn]
      obtain ⟨ec, h1, h2, h3, h4⟩ := ext_child hw hj hn
      simp only [h2, ↓reduceIte]
      rw [ih _ h2 h1 (fun x hx1 hx2 => h x (by omega) (by omega))]
  | branch v ks mm =>
    rw [treeAt_branch hj hn, treeAt_branch hj hn, h j hlo (Nat.le_refl _)]
    congr 1
    apply kidsOf_congr; intro p _ hp
    obtain ⟨ec, h1, h2, h3, h4⟩ := child_info hw hj (q := p) (by simpa [hn, nKids] using hp)
    simp only [hn, nKids] at h1 h2 h3 h4
    simp only [h2, ↓reduceIte]; exact ih _ h2 h1 (fun x hx1 hx2 => h x (by omega) (by omega))

/-- `res j` is `RNONE` or an entry `≤ j` that is not an extension with an empty
key; and `treeAt` agrees on `get` with its `res` (or `get` fails). -/
theorem res_spec {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e) :
    (e.res = RNONE ∧ ∀ key, (treeAt A K vals j).get key = none) ∨
    (∃ e', A[e.res]? = some e' ∧ e.res ≤ j ∧ (∀ mm, e'.nf ≠ .ext [] none mm) ∧
      (∀ h mm, e'.nf ≠ .ext [] (some h) mm) ∧
      ∀ key, (treeAt A K vals j).get key = (treeAt A K vals e.res).get key) := by
  induction j using Nat.strongRecOn generalizing e with
  | _ j ih =>
  obtain ⟨-, -, -, hres⟩ := nodeWF_of hw hj
  have self : e.res = j → (∀ mm, e.nf ≠ .ext [] none mm) → (∀ h mm, e.nf ≠ .ext [] (some h) mm) →
      ((e.res = RNONE ∧ ∀ key, (treeAt A K vals j).get key = none) ∨
      (∃ e', A[e.res]? = some e' ∧ e.res ≤ j ∧ (∀ mm, e'.nf ≠ .ext [] none mm) ∧
        (∀ h mm, e'.nf ≠ .ext [] (some h) mm) ∧
        ∀ key, (treeAt A K vals j).get key = (treeAt A K vals e.res).get key)) :=
    fun h1 h2 h3 => Or.inr ⟨e, by rw [h1]; exact hj, by omega, h2, h3, fun key => by rw [h1]⟩
  cases hn : e.nf with
  | leaf k ref mm =>
    rw [hn] at hres
    exact self hres (by intro mm h; rw [hn] at h; cases h) (by intro h mm h'; rw [hn] at h'; cases h')
  | branch v ks mm =>
    rw [hn] at hres
    exact self hres (by intro mm h; rw [hn] at h; cases h) (by intro h mm h'; rw [hn] at h'; cases h')
  | ext k h mm =>
    cases k with
    | cons a k' =>
      rw [hn] at hres
      exact self hres (by intro mm h; rw [hn] at h; cases h) (by intro h mm h'; rw [hn] at h'; cases h')
    | nil =>
      cases h with
      | some hh =>
        rw [hn] at hres
        refine Or.inl ⟨hres, fun key => ?_⟩
        rw [treeAt_exth hj hn]; simp [PTrie.get, isPrefix]
      | none =>
        rw [hn] at hres
        obtain ⟨ec, h1, h2, -, -⟩ := ext_child hw hj hn
        have hg : A.getD (K.getD e.kid 0) e = ec := by rw [List.getD_eq_getElem?_getD, h1]; rfl
        have hres : e.res = ec.res := by rw [← hg]; exact hres
        have hget : ∀ key, (treeAt A K vals j).get key = (treeAt A K vals (K.getD e.kid 0)).get key := by
          intro key; rw [treeAt_ext hj hn]
          simp only [PTrie.get, isPrefix, h2, ↓reduceIte, List.length_nil, List.drop_zero]
        rcases ih _ h2 h1 with ⟨hr, hn'⟩ | ⟨e', he', hle, hx1, hx2, hx3⟩
        · exact Or.inl ⟨by rw [hres, hr], fun key => by rw [hget, hn']⟩
        · rw [hres]
          exact Or.inr ⟨e', he', by omega, hx1, hx2, fun key => by rw [hget, hx3]⟩

/-! ## Walk inversion and the point update -/

theorem walk_lt {A : List Ent} {K : List Nat} {r : Nat} {key : List Nat} {f : Nat}
    (h : Walk A K r key f) : r < A.length := by
  have g : ∀ {e : Ent}, A[r]? = some e → r < A.length := by
    intro e he
    rcases Nat.lt_or_ge r A.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at he; cases he
  cases h with
  | leaf he _ => exact g he
  | brv he _ => exact g he
  | ext he _ _ => exact g he
  | br he _ _ _ => exact g he

theorem walk_inv {A : List Ent} {K : List Nat} {r : Nat} {key : List Nat} {f : Nat} {e : Ent}
    (h : Walk A K r key f) (he : A[r]? = some e) :
    (∃ mm, e.nf = .leaf key none mm ∧ f = r) ∨
    (∃ ks mm, e.nf = .branch (some none) ks mm ∧ key = [] ∧ f = r) ∨
    (∃ k mm rest, e.nf = .ext k none mm ∧ key = k ++ rest ∧
      Walk A K (A.getD (K.getD e.kid 0) default).res rest f) ∨
    (∃ v ks mm n rest, e.nf = .branch v ks mm ∧ ks[n]? = some (some none) ∧ key = n :: rest ∧
      Walk A K (A.getD (childIdx K e.kid (nRev ks) (revBelow ks n)) default).res rest f) := by
  cases h with
  | leaf he' hn => rw [he] at he'; cases he'; exact Or.inl ⟨_, hn, rfl⟩
  | brv he' hn => rw [he] at he'; cases he'; exact Or.inr (Or.inl ⟨_, _, hn, rfl, rfl⟩)
  | ext he' hn hw => rw [he] at he'; cases he'; exact Or.inr (Or.inr (Or.inl ⟨_, _, _, hn, rfl, hw⟩))
  | br he' hn hks hw => rw [he] at he'; cases he'; exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, hn, hks, rfl, hw⟩))

theorem treeAt_upd_off {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} {f : Nat} {nv : Bytes} {c : Nat} {ec : Ent} (hc : A[c]? = some ec)
    (hf : f < ec.lo ∨ c < f) : treeAt A K vals c = treeAt A K (updVals vals f nv) c := by
  apply treeAt_local hw hc
  intro x h1 h2
  have : x ≠ f := by omega
  simp [updVals, this]

theorem isPrefix_self (k rest : List Nat) : isPrefix k (k ++ rest) = true := by
  induction k with
  | nil => rfl
  | cons a k ih => simp [isPrefix, ih]

/-- `walk_get_set` with the bounds of the target entry, assuming the arena has
fewer than `RNONE` entries (so that `RNONE` is never an entry). -/
theorem walk_get_set_aux {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    (hA : A.length ≤ RNONE) (vals : Nat → Bytes) (nv : Bytes) (j : Nat) :
    ∀ {e : Ent} {key : List Nat} {f : Nat}, A[j]? = some e → Walk A K e.res key f →
    e.lo ≤ f ∧ f ≤ j ∧ (treeAt A K vals j).get key = some (vals f) ∧
    (treeAt A K vals j).set key nv = some (treeAt A K (updVals vals f nv) j) := by
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro e key f hj hwalk
  obtain ⟨hlo, -, -, hres⟩ := nodeWF_of hw hj
  cases hn : e.nf with
  | leaf k ref mm =>
    rw [hn] at hres
    have hres : e.res = j := hres
    rw [hres] at hwalk
    rcases walk_inv hwalk hj with ⟨mm', hn', rfl⟩ | ⟨_, _, hn', -⟩ | ⟨_, _, _, hn', -⟩ | ⟨_, _, _, _, _, hn', -⟩ <;>
      rw [hn] at hn' <;> cases hn'
    refine ⟨hlo, Nat.le_refl _, ?_, ?_⟩
    · rw [treeAt_leaf hj hn]; simp [PTrie.get, slotOfRef, Slot.get]
    · rw [treeAt_leaf hj hn, treeAt_leaf hj hn]; simp [PTrie.set, slotOfRef, Slot.get, updVals]
  | ext k h mm =>
    cases h with
    | some hh =>
      cases k with
      | nil =>
        rw [hn] at hres
        have hres : e.res = RNONE := hres
        rw [hres] at hwalk
        have := walk_lt hwalk; omega
      | cons a k' =>
        rw [hn] at hres
        have hres : e.res = j := hres
        rw [hres] at hwalk
        rcases walk_inv hwalk hj with ⟨_, hn', -⟩ | ⟨_, _, hn', -⟩ | ⟨_, _, _, hn', -⟩ | ⟨_, _, _, _, _, hn', -⟩ <;>
          rw [hn] at hn' <;> cases hn'
    | none =>
      obtain ⟨ec, h1, h2, h3, -⟩ := ext_child hw hj hn
      have hrest : ∃ rest, key = k ++ rest ∧ Walk A K ec.res rest f := by
        cases k with
        | nil =>
          rw [hn] at hres
          have hres : e.res = (A.getD (K.getD e.kid 0) e).res := hres
          rw [getD_of h1] at hres
          rw [hres] at hwalk
          exact ⟨key, rfl, hwalk⟩
        | cons a k' =>
          rw [hn] at hres
          have hres : e.res = j := hres
          rw [hres] at hwalk
          rcases walk_inv hwalk hj with ⟨_, hn', -⟩ | ⟨_, _, hn', -⟩ | ⟨_, _, rest, hn', hk, hw'⟩ |
              ⟨_, _, _, _, _, hn', -⟩ <;> rw [hn] at hn' <;> cases hn'
          rw [getD_of h1] at hw'
          exact ⟨rest, hk, hw'⟩
      obtain ⟨rest, rfl, hw'⟩ := hrest
      obtain ⟨b1, b2, hget, hset⟩ := ih _ h2 h1 hw'
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [treeAt_ext hj hn]
        simp only [PTrie.get, h2, ↓reduceIte, isPrefix_self, List.drop_left, hget]
      · rw [treeAt_ext hj hn, treeAt_ext hj hn]
        simp only [PTrie.set, h2, ↓reduceIte, isPrefix_self, List.drop_left, hset, Option.map_some]
  | branch v ks mm =>
    rw [hn] at hres
    have hres : e.res = j := hres
    rw [hres] at hwalk
    rcases walk_inv hwalk hj with ⟨_, hn', -⟩ | ⟨ks', mm', hn', rfl, rfl⟩ | ⟨_, _, _, hn', -⟩ |
        ⟨v', ks', mm', n, rest, hn', hks, rfl, hw'⟩ <;> rw [hn] at hn' <;> cases hn'
    · -- value of the branch itself
      refine ⟨hlo, Nat.le_refl _, ?_, ?_⟩
      · rw [treeAt_branch hj hn]; simp [PTrie.get, slotOfRef, Slot.get]
      · rw [treeAt_branch hj hn, treeAt_branch hj hn]
        simp only [PTrie.set, Option.map_some, slotOfRef, updVals, ↓reduceIte, Option.some.injEq,
          PTrie.branch.injEq, true_and, and_true]
        apply kidsOf_congr; intro p _ hp
        obtain ⟨ec, h1, h2, -, -⟩ := child_info hw hj (q := p) (by simpa [hn, nKids] using hp)
        simp only [hn, nKids] at h1 h2
        simp only [h2, ↓reduceIte]
        exact treeAt_upd_off hw h1 (Or.inr h2)
    · -- through the child `revBelow ks n`
      have hlt := revBelow_lt ks n hks
      obtain ⟨ec, h1, h2, h3, h4⟩ := child_info hw hj (q := revBelow ks n) (by simp only [hn, nKids]; exact hlt)
      simp only [hn, nKids] at h1 h2
      rw [getD_of h1] at hw'
      obtain ⟨b1, b2, hget, hset⟩ := ih _ h2 h1 hw'
      have hfj : f ≠ j := by omega
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [treeAt_branch hj hn]
        simp only [PTrie.get, get_kidsOf, hks, ↓reduceIte, Nat.zero_add, h2, hget]
      · rw [treeAt_branch hj hn, treeAt_branch hj hn]
        simp only [PTrie.set]
        rw [set_kidsOf _ (fun q => if childIdx K e.kid (nRev ks) q < j then
            treeAt A K (updVals vals f nv) (childIdx K e.kid (nRev ks) q) else .hash []) ks 0 n rest nv hks (by simp only [Nat.zero_add, h2, ↓reduceIte]; exact hset)]
        · simp only [Option.map_some, updVals, Ne.symm hfj, ↓reduceIte]
        · intro p hne _ hp
          simp only [Nat.zero_add] at hne hp
          obtain ⟨ec', h1', h2', -, -⟩ := child_info hw hj (q := p) (by simpa [hn, nKids] using hp)
          simp only [hn, nKids] at h1' h2'
          simp only [h2', ↓reduceIte]
          apply treeAt_upd_off hw h1'
          rcases Nat.lt_or_gt_of_ne hne with hpl | hpl
          · have := child_disj hw hj hpl (by simpa [hn, nKids] using hlt) (by simpa [hn, nKids] using h1)
            simp only [hn, nKids] at this
            omega
          · have := child_disj hw hj hpl (by simpa [hn, nKids] using hp) (by simpa [hn, nKids] using h1')
            simp only [hn, nKids] at this
            omega


/-- `walk_get_set` under the extra hypothesis `A.length ≤ RNONE`. -/
theorem walk_get_set' {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    (hA : A.length ≤ RNONE)
    {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e) {key : List Nat} {f : Nat}
    (hwalk : Walk A K e.res key f) (nv : Bytes) :
    (treeAt A K vals j).get key = some (vals f) ∧
    (treeAt A K vals j).set key nv = some (treeAt A K (updVals vals f nv) j) :=
  let ⟨_, _, h1, h2⟩ := walk_get_set_aux hw hA vals nv j hj hwalk
  ⟨h1, h2⟩

/-- (`ArenaWF.len_le` bounds the arena below `RNONE`, which rules out a walk
starting at the "no entry" marker.) -/
theorem walk_get_set {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e) {key : List Nat} {f : Nat}
    (hwalk : Walk A K e.res key f) (nv : Bytes) :
    (treeAt A K vals j).get key = some (vals f) ∧
    (treeAt A K vals j).set key nv = some (treeAt A K (updVals vals f nv) j) :=
  walk_get_set' hw (Nat.le_trans hw.len_le (by decide)) hj hwalk nv

theorem get_walk {pb : Bytes} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → Bytes} {j : Nat} {e : Ent} (hj : A[j]? = some e) {key : List Nat} {v : Bytes}
    (hg : (treeAt A K vals j).get key = some v) :
    ∃ f, Walk A K e.res key f ∧ v = vals f := by
  induction j using Nat.strongRecOn generalizing e key v with
  | _ j ih =>
  rcases res_spec hw (vals := vals) hj with ⟨-, hn0⟩ | ⟨e', he', hle, -, -, hget⟩
  · rw [hn0] at hg; cases hg
  rw [hget] at hg
  cases hn : e'.nf with
  | leaf k ref mm =>
    rw [treeAt_leaf he' hn] at hg
    simp only [PTrie.get] at hg
    split at hg
    · rename_i hk
      simp only [beq_iff_eq] at hk; subst hk
      cases ref with
      | none =>
        simp only [slotOfRef, Slot.get, Option.some.injEq] at hg
        exact ⟨e.res, Walk.leaf he' hn, hg.symm⟩
      | some p => obtain ⟨len, h⟩ := p; simp [slotOfRef, Slot.get] at hg
    · cases hg
  | ext k h mm =>
    cases h with
    | some hh => rw [treeAt_exth he' hn] at hg; simp [PTrie.get] at hg
    | none =>
      obtain ⟨ec, h1, h2, -, -⟩ := ext_child hw he' hn
      rw [treeAt_ext he' hn] at hg
      simp only [PTrie.get, h2, ↓reduceIte] at hg
      split at hg
      · rename_i hpre
        obtain ⟨f, hw', hv⟩ := ih _ (by omega) h1 hg
        refine ⟨f, ?_, hv⟩
        have := Walk.ext he' hn (by rw [getD_of h1]; exact hw')
        rw [isPrefix_append hpre] at this; exact this
      · cases hg
  | branch v' ks mm =>
    rw [treeAt_branch he' hn] at hg
    cases key with
    | nil =>
      simp only [PTrie.get] at hg
      rcases v' with _ | _ | ⟨len, h⟩
      · simp at hg
      · simp only [Option.map_some, Option.bind_some, slotOfRef, Slot.get, Option.some.injEq] at hg
        exact ⟨e.res, Walk.brv he' hn, hg.symm⟩
      · simp [slotOfRef, Slot.get] at hg
    | cons n rest =>
      simp only [PTrie.get, get_kidsOf] at hg
      split at hg
      · rename_i hks
        have hlt := revBelow_lt ks n hks
        obtain ⟨ec, h1, h2, -, -⟩ := child_info hw he' (q := revBelow ks n) (by simp only [hn, nKids]; exact hlt)
        simp only [hn, nKids] at h1 h2
        simp only [Nat.zero_add, h2, ↓reduceIte] at hg
        obtain ⟨f, hw', hv⟩ := ih _ (by omega) h1 hg
        exact ⟨f, Walk.br he' hn hks (by rw [getD_of h1]; exact hw'), hv⟩
      · cases hg

end ReexecNpai

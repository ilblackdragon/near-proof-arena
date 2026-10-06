import ZkFormal.NearV3.Link.Walk3Prov

/-!
# ZkFormal.NearV3.Link.Walk3Trie — one walk row, read on the record trie

`T n := fullTree (recsOf f vs) V n`.  The per-position invariant of a walk is

  `Pos X n I r` :  record `n` exists, `I ≤ |key n|` (`0` for a branch) and
                  `X = (T n).find ((key n).take I ++ r)`,

i.e. "the lookup `X` of the whole key equals the lookup, in the subtrie of record `n`,
of the remaining key `r` at key offset `I`".  For an extension with a dead child the
position `(n, |key|)` is reachable; there `X = none` and no row can continue.

* `res_find` — `T c` and `T (res c)` answer `find` alike (`res` skips empty-key
  extensions with a revealed child), and `res c` is a record;
* `pos_step` — a `DOWN`/`KEY` edge of record `n` with the next symbol moves `Pos`;
* `pos_val` — a `VAL` edge at the end of the key gives `X = some (some (valOf V (f vid)))`;
* `pos_absK` — a `KEY`/`LEND` edge with a different symbol gives `X = some none`;
* `pos_absB` — a branch's `BMAP` facts (empty slot, or no value at the end) give
  `X = some none`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace ZkFormal.NearV3.Walk3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3 ZkFormal.NearV3.Link3
open NearSpec

/-- Key of a record (`[]` for a branch). -/
def kkey3 : NodeV3 → List Nat
  | .leaf k _ _ => k
  | .ext k _ _ => k
  | .branch .. => []

theorem klen_kkey (v : NodeV3) : klen3 v = (kkey3 v).length := by cases v <;> rfl

/-- Structural hypotheses in `[]?` form (see `TrieHyp.of` for the user-facing shape). -/
structure TrieHyp (f : Nat → Nat) (vs : List NodeS3) (V : List ValRec3) : Prop where
  unf : ∀ (n : Nat) (s : NodeS3), vs[n]? = some s →
    fullTree (recsOf f vs) V n = nodeTree3 V (fullTree (recsOf f vs) V) (s.v.toRec3 f)
  res : ∀ (n : Nat) (s : NodeS3), vs[n]? = some s → s.resOk n
  par : ∀ (n : Nat) (s : NodeS3), vs[n]? = some s → ∀ (c l r : Nat) (pre po : List Nat), (c, l, r, pre, po) ∈ s.v.revealed →
    ∃ s' : NodeS3, vs[c]? = some s' ∧ s'.res = r

theorem TrieHyp.of {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3}
    (hunf : ∀ n (hn : n < vs.length),
      fullTree (recsOf f vs) V n = nodeTree3 V (fullTree (recsOf f vs) V) (vs[n].v.toRec3 f))
    (hres : ∀ n (hn : n < vs.length), vs[n].resOk n)
    (hpar : ∀ p (hp : p < vs.length) {c l r : Nat} {pre po : List Nat},
      (c, l, r, pre, po) ∈ vs[p].v.revealed → ∃ hc : c < vs.length, vs[c].res = r) :
    TrieHyp f vs V where
  unf n s h := by
    obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h; exact hunf n hn
  res n s h := by
    obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h; exact hres n hn
  par n s h c l r pre po hm := by
    obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h
    obtain ⟨hc, hr⟩ := hpar n hn hm
    exact ⟨vs[c], List.getElem?_eq_getElem hc, hr⟩

section
variable {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3}

/-- The invariant at position `(n, I)` with remaining key `r`. -/
def Pos (f : Nat → Nat) (vs : List NodeS3) (V : List ValRec3) (X : Option (Option Bytes))
    (n I : Nat) (r : List Nat) : Prop :=
  ∃ s, vs[n]? = some s ∧ I ≤ klen3 s.v ∧
    X = (fullTree (recsOf f vs) V n).find ((kkey3 s.v).take I ++ r)

theorem resOk_cases {n : Nat} {s : NodeS3} (h : s.resOk n) :
    s.res = n ∨ ∃ c l cr pre po m, s.v = .ext [] (.node c l cr pre po) m ∧ s.res = cr := by
  unfold NodeS3.resOk at h
  split at h
  · rename_i heq; exact Or.inr ⟨_, _, _, _, _, _, heq, h⟩
  · exact Or.inl h

theorem find_ext_nil (c : PTrie) (m : Nat) (r : List Nat) : (PTrie.ext [] c m).find r = c.find r := by
  simp [PTrie.find, isPrefix]

/-- `res` targets: same lookups, and the target is a record. -/
theorem res_find (H : TrieHyp f vs V) : ∀ (N c : Nat) (s : NodeS3), vs[c]? = some s →
    sizeOf (fullTree (recsOf f vs) V c) < N →
    ∃ s', vs[s.res]? = some s' ∧ ∀ r, (fullTree (recsOf f vs) V c).find r =
      (fullTree (recsOf f vs) V s.res).find r
  | 0, _, _, _, hN => absurd hN (Nat.not_lt_zero _)
  | N + 1, c, s, hs, hN => by
    rcases resOk_cases (H.res c s hs) with he | ⟨c', l, cr, pre, po, m, hv, he⟩
    · rw [he]; exact ⟨s, hs, fun _ => rfl⟩
    · obtain ⟨s', hs', hr'⟩ := H.par c s hs c' l cr pre po (by simp [hv, NodeV3.revealed])
      have hu := H.unf c s hs
      rw [hv] at hu
      simp only [NodeV3.toRec3, NKid.toKid3, nodeTree3, kidTree3] at hu
      have hsz : sizeOf (fullTree (recsOf f vs) V c') < N := by
        rw [hu] at hN; simp at hN; omega
      obtain ⟨s'', hs'', hf⟩ := res_find H N c' s' hs' hsz
      rw [hr'] at hs'' hf
      rw [he]
      refine ⟨s'', hs'', fun r => ?_⟩
      rw [hu, find_ext_nil, hf]

theorem res_find' (H : TrieHyp f vs V) {c : Nat} {s : NodeS3} (hs : vs[c]? = some s) :
    ∃ s', vs[s.res]? = some s' ∧ ∀ r, (fullTree (recsOf f vs) V c).find r =
      (fullTree (recsOf f vs) V s.res).find r :=
  res_find H _ c s hs (Nat.lt_succ_self _)

/-- Entering a `res` target from a kid with that target. -/
theorem pos_res (H : TrieHyp f vs V) {X : Option (Option Bytes)} {c cr : Nat} {s : NodeS3}
    (hs : vs[c]? = some s) (hcr : s.res = cr) {r : List Nat}
    (hX : X = (fullTree (recsOf f vs) V c).find r) : Pos f vs V X cr 0 r := by
  obtain ⟨s', hs', hf⟩ := res_find' H hs
  subst hcr
  exact ⟨s', hs', Nat.zero_le _, by rw [hX, hf]; simp⟩

theorem kids_find_node (g : Nat → PTrie) : ∀ (kl : List Kid3) (j c : Nat) (r : List Nat),
    kl[j]? = some (.node c) → Kids.find (kidsOf3 g kl) j r = (g c).find r
  | [], _, _, _, h => by simp at h
  | k :: kl, 0, c, r, h => by
    simp at h; subst h; simp [kidsOf3, Kids.find]
  | k :: kl, j + 1, c, r, h => by
    simp only [List.getElem?_cons_succ] at h
    have := kids_find_node g kl j c r h
    cases k <;> simpa [kidsOf3, Kids.find] using this

theorem kids_find_none (g : Nat → PTrie) : ∀ (kl : List Kid3) (j : Nat) (r : List Nat),
    kl[j]? = some .none → Kids.find (kidsOf3 g kl) j r = some none
  | [], _, _, h => by simp at h
  | k :: kl, 0, r, h => by
    simp at h; subst h; simp [kidsOf3, Kids.find]
  | k :: kl, j + 1, r, h => by
    simp only [List.getElem?_cons_succ] at h
    have := kids_find_none g kl j r h
    cases k <;> simpa [kidsOf3, Kids.find] using this

theorem isPrefix_app : ∀ (k x : List Nat), isPrefix k (k ++ x) = true
  | [], _ => rfl
  | a :: k, x => by simp [isPrefix, isPrefix_app k x]

theorem take_succ_getD {k : List Nat} {i : Nat} (hi : i < k.length) :
    k.take (i + 1) = k.take i ++ [k.getD i 0] := by
  rw [List.take_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp

theorem getElem?_take_app {k r : List Nat} {i : Nat} (hi : i < k.length) {σ : Nat} :
    (k.take i ++ σ :: r)[i]? = some σ := by
  have h : (k.take i).length = i := by simp; omega
  rw [List.getElem?_append_right (by omega), h]; simp

theorem getD_some {k : List Nat} {i : Nat} (hi : i < k.length) : k[i]? = some (k.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

theorem dropLast_getD {k : List Nat} {i : Nat} (hi : i < k.length - 1) : k.dropLast.getD i 0 = k.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_dropLast]; simp [hi]

theorem dropLast_x {k : List Nat} {x : Nat} (hl : k.getLast? = some x) :
    k.take (k.length - 1) ++ [x] = k ∧ 0 < k.length ∧ k.getD (k.length - 1) 0 = x := by
  have hne : k ≠ [] := by rintro rfl; simp at hl
  have hx : k.getLast hne = x := by rw [List.getLast?_eq_getLast hne] at hl; exact Option.some.inj hl
  have hk := List.dropLast_concat_getLast hne
  refine ⟨?_, List.length_pos_iff.mpr hne, ?_⟩
  · rw [← List.dropLast_eq_take, ← hx, hk]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by have := List.length_pos_iff.mpr hne; omega)]
    simp only [Option.getD_some]
    rw [← hx, List.getLast_eq_getElem]

theorem leaf_find (k : List Nat) (sl : Slot) (m : Nat) (key : List Nat) :
    (PTrie.leaf k sl m).find key = if k = key then sl.get.map some else some none := by
  simp [PTrie.find]

theorem ext_find (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) :
    (PTrie.ext k c m).find key = if isPrefix k key then c.find (key.drop k.length) else some none := by
  simp [PTrie.find]

/-- **Step** along a `DOWN`/`KEY` edge of record `n` reading symbol `σ`. -/
theorem pos_step (H : TrieHyp f vs V) {X : Option (Option Bytes)} {n I σ N' I' kd : Nat}
    {r : List Nat} (hp : Pos f vs V X n I (σ :: r)) {s : NodeS3} (hs : vs[n]? = some s)
    (he : [n, I, σ, N', I', kd] ∈ edgesOf3 n s) (hk : kd = EK_DOWN ∨ kd = EK_KEY) :
    Pos f vs V X N' I' r := by
  obtain ⟨s0, hs0, hI, hX⟩ := hp
  rw [hs] at hs0; cases hs0
  have hu := H.unf n s hs
  have hkd : kd ≠ EK_VAL ∧ kd ≠ EK_LEND := by
    rcases hk with rfl | rfl <;> decide
  unfold edgesOf3 at he
  cases hv : s.v with
  | leaf k sl m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, he⟩ := mem_keyEdges3.mp he
        simp only [List.cons.injEq, and_true] at he
        obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := he
        refine ⟨s, hs, by simp [klen3, hv]; omega, ?_⟩
        simp only [kkey3, hv]
        rw [hX, take_succ_getD hi]; simp
      · cases sl with
        | val _ i _ _ _ _ =>
          simp only [List.mem_singleton, List.cons.injEq] at he
          exact absurd he.2.2.2.2.2.1 hkd.1
        | ref => simp at he
    · simp only [List.mem_singleton, List.cons.injEq] at he
      exact absurd he.2.2.2.2.2.1 hkd.2
  | ext k kid m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, he⟩ := mem_keyEdges3.mp he
      simp only [List.length_dropLast] at hi
      rw [dropLast_getD hi] at he
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := he
      refine ⟨s, hs, by simp [klen3, hv]; omega, ?_⟩
      simp only [kkey3, hv]
      rw [hX, take_succ_getD (by omega)]; simp
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x =>
        obtain ⟨hkx, hkpos, -⟩ := dropLast_x hl
        cases kid with
        | node c l cr pre po =>
          simp only [hl, List.mem_singleton, List.cons.injEq, and_true] at he
          obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := he
          obtain ⟨s', hs', hr'⟩ := H.par n s hs c l N' pre po (by simp [hv, NodeV3.revealed])
          refine pos_res H hs' hr' ?_
          rw [hX, hu]
          have : k.take (k.length - 1) ++ σ :: r = k ++ r := by
            rw [← hkx]; simp
          rw [this]
          simp [NKid.toKid3, kidTree3, ext_find, isPrefix_app]
        | none =>
          simp only [hl, List.mem_singleton, List.cons.injEq, and_true] at he
          obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := he
          refine ⟨s, hs, by simp [klen3, hv], ?_⟩
          simp only [kkey3, hv]
          rw [hX, List.take_length, ← hkx]; simp
        | hash h =>
          simp only [hl, List.mem_singleton, List.cons.injEq, and_true] at he
          obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := he
          refine ⟨s, hs, by simp [klen3, hv], ?_⟩
          simp only [kkey3, hv]
          rw [hX, List.take_length, ← hkx]; simp
  | branch sv kids m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rcases List.mem_append.mp he with he | he
    · obtain ⟨⟨kd', j⟩, hpm, hm⟩ := List.mem_filterMap.mp he
      obtain ⟨hj, hkd'⟩ := mem_zip_range.mp hpm
      cases kd' with
      | node c l cr pre po =>
        simp only [Option.some.injEq, List.cons.injEq, and_true] at hm
        obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := hm
        obtain ⟨s', hs', hr'⟩ := H.par n s hs c l cr pre po (by
          simp only [hv, NodeV3.revealed, List.mem_filterMap]
          exact ⟨_, List.getElem_mem hj, by rw [hkd']⟩)
        refine pos_res H hs' hr' ?_
        rw [hX, hu]
        simp only [List.take_zero, List.nil_append, PTrie.find]
        apply kids_find_node
        simp [hj, hkd', NKid.toKid3]
      | none => simp at hm
      | hash => simp at hm
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      · simp at he
      · simp only [List.mem_singleton, List.cons.injEq] at he
        exact absurd he.2.2.2.2.2.1 hkd.1

/-- **Value terminal**: a `VAL` edge at the end of the key. -/
theorem pos_val (H : TrieHyp f vs V) {X : Option (Option Bytes)} {n I σ N' I' : Nat}
    (hp : Pos f vs V X n I []) {s : NodeS3} (hs : vs[n]? = some s)
    (he : [n, I, σ, N', I', EK_VAL] ∈ edgesOf3 n s) :
    X = some (some (valOf V (f N'))) := by
  obtain ⟨s0, hs0, hI, hX⟩ := hp
  rw [hs] at hs0; cases hs0
  have hu := H.unf n s hs
  unfold edgesOf3 at he
  cases hv : s.v with
  | leaf k sl m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, he⟩ := mem_keyEdges3.mp he
        simp only [List.cons.injEq] at he
        exact absurd he.2.2.2.2.2.1 (by decide)
      · cases sl with
        | val lenB i l pre po w =>
          simp only [List.mem_singleton, List.cons.injEq, and_true] at he
          obtain ⟨-, rfl, -, rfl, -⟩ := he
          rw [hX, hu, List.take_length, List.append_nil, leaf_find]
          simp [NSlot3.toV3, slot3, Slot.get]
        | ref => simp at he
    · simp only [List.mem_singleton, List.cons.injEq] at he
      exact absurd he.2.2.2.2.2.1 (by decide)
  | ext k kid m =>
    rw [hv] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, he⟩ := mem_keyEdges3.mp he
      simp only [List.cons.injEq] at he
      exact absurd he.2.2.2.2.2.1 (by decide)
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x =>
        cases kid <;>
        · simp only [hl, List.mem_singleton, List.cons.injEq] at he
          exact absurd he.2.2.2.2.2.1 (by decide)
  | branch sv kids m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rcases List.mem_append.mp he with he | he
    · obtain ⟨⟨kd', j⟩, hpm, hm⟩ := List.mem_filterMap.mp he
      cases kd' with
      | node c l cr pre po =>
        simp only [Option.some.injEq, List.cons.injEq] at hm
        exact absurd hm.2.2.2.2.2.1 (by decide)
      | none => simp at hm
      | hash => simp at hm
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      · simp at he
      · simp only [List.mem_singleton, List.cons.injEq, and_true] at he
        obtain ⟨-, -, -, rfl, -⟩ := he
        rw [hX, hu]
        simp [PTrie.find, NSlot3.toV3, slot3, Slot.get]

/-- The remaining key at an absent-by-key row: empty with `σ = END` (last row), or `σ :: r`. -/
def RestOk (σ : Nat) (rest : List Nat) : Prop := (rest = [] ∧ σ = SYM_END) ∨ ∃ r, rest = σ :: r

/-- **Absent by key**: a `KEY`/`LEND` edge whose nibble differs from the symbol. -/
theorem pos_absK (H : TrieHyp f vs V) {X : Option (Option Bytes)} {n I a σ N' I' kd : Nat}
    {rest : List Nat} (hp : Pos f vs V X n I rest) {s : NodeS3} (hs : vs[n]? = some s)
    (he : [n, I, a, N', I', kd] ∈ edgesOf3 n s) (hk : kd = EK_KEY ∨ kd = EK_LEND) (hne : a ≠ σ)
    (hr : RestOk σ rest) : X = some none := by
  obtain ⟨s0, hs0, hI, hX⟩ := hp
  rw [hs] at hs0; cases hs0
  have hu := H.unf n s hs
  have hkd : kd ≠ EK_VAL ∧ kd ≠ EK_DOWN := by
    rcases hk with rfl | rfl <;> decide
  -- key nibble `i < |k|` differs: `k.take i ++ rest ≠ k` and `k` is no prefix
  have hne_key : ∀ {k : List Nat} {i : Nat}, i < k.length → k.getD i 0 ≠ σ →
      k ≠ k.take i ++ rest ∧ isPrefix k (k.take i ++ rest) = false := by
    intro k i hi hd
    rcases hr with ⟨rfl, -⟩ | ⟨r, rfl⟩
    · have hl : (k.take i ++ []).length < k.length := by simp; omega
      exact ⟨fun h => by rw [← h] at hl; omega, not_prefix_of_len hl⟩
    · exact ⟨ne_of_nib (getD_some hi) (getElem?_take_app hi) hd,
        not_prefix_of_nib (getD_some hi) (getElem?_take_app hi) hd⟩
  unfold edgesOf3 at he
  cases hv : s.v with
  | leaf k sl m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rw [hX, hu, leaf_find]
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, he⟩ := mem_keyEdges3.mp he
        simp only [List.cons.injEq, and_true] at he
        obtain ⟨-, rfl, rfl, -⟩ := he
        rw [if_neg (hne_key hi hne).1]
      · cases sl with
        | val _ i _ _ _ _ =>
          simp only [List.mem_singleton, List.cons.injEq] at he
          exact absurd he.2.2.2.2.2.1 hkd.1
        | ref => simp at he
    · simp only [List.mem_singleton, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl, -⟩ := he
      rcases hr with ⟨-, rfl⟩ | ⟨r, rfl⟩
      · exact absurd rfl hne
      · rw [if_neg]; intro h
        have := congrArg List.length h; simp at this
  | ext k kid m =>
    rw [hv] at he hu
    simp only [kkey3, klen3, hv] at hX hI
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rw [hX, hu, ext_find]
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, he⟩ := mem_keyEdges3.mp he
      simp only [List.length_dropLast] at hi
      rw [dropLast_getD hi] at he
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl, -⟩ := he
      rw [(hne_key (by omega) hne).2]; rfl
    · cases hl : k.getLast? with
      | none => cases kid <;> simp [hl] at he
      | some x =>
        obtain ⟨-, hkpos, hgx⟩ := dropLast_x hl
        have key : I = k.length - 1 → a = x → isPrefix k (k.take I ++ rest) = false := by
          rintro rfl rfl; exact (hne_key (by omega) (by rw [hgx]; exact hne)).2
        cases kid <;>
        · simp only [hl, List.mem_singleton, List.cons.injEq, and_true] at he
          rw [key he.2.1 he.2.2.1]; rfl
  | branch sv kids m =>
    rw [hv] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨⟨kd', j⟩, hpm, hm⟩ := List.mem_filterMap.mp he
      cases kd' with
      | node c l cr pre po =>
        simp only [Option.some.injEq, List.cons.injEq] at hm
        exact absurd hm.2.2.2.2.2.1.symm hkd.2
      | none => simp at hm
      | hash => simp at hm
    · rcases sv with _ | ⟨_ | ⟨lenB, i, l, pre, po, w⟩⟩
      · simp at he
      · simp at he
      · simp only [List.mem_singleton, List.cons.injEq] at he
        exact absurd he.2.2.2.2.2.1 hkd.1

theorem kbit_zero {k : NKid} (h : Render.NodeGen3.kbit k = 0) : k = .none := by
  unfold Render.NodeGen3.kbit at h; split at h
  · omega
  · rename_i hk; exact Classical.not_not.mp hk

/-- **Absent at a branch**: the branch's `BMAP` facts. -/
theorem pos_absB (H : TrieHyp f vs V) {X : Option (Option Bytes)} {n : Nat}
    {rest : List Nat} (hp : Pos f vs V X n 0 rest) {s : NodeS3} (hs : vs[n]? = some s)
    (hwf : s.v.wf) {bm hv : Nat} (hb : s.v.bmap = some (bm, hv))
    (hc : (rest = [] ∧ hv = 0) ∨ ∃ σ r, rest = σ :: r ∧ σ < 16 ∧ bm / 2 ^ σ % 2 = 0) :
    X = some none := by
  obtain ⟨s0, hs0, -, hX⟩ := hp
  rw [hs] at hs0; cases hs0
  have hu := H.unf n s hs
  cases hv' : s.v with
  | leaf => rw [hv'] at hb; simp [NodeV3.bmap] at hb
  | ext => rw [hv'] at hb; simp [NodeV3.bmap] at hb
  | branch sv kids m =>
    rw [hv'] at hb hu hwf
    simp only [NodeV3.bmap, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [kkey3, hv', List.take_zero, List.nil_append] at hX
    simp only [NodeV3.toRec3, nodeTree3] at hu
    rw [hX, hu]
    rcases hc with ⟨rfl, h0⟩ | ⟨σ, r, rfl, hσ, hbit⟩
    · cases sv with
      | none => simp [PTrie.find]
      | some _ => simp at h0
    · simp only [PTrie.find]
      apply kids_find_none
      have h16 : kids.length = 16 := hwf.1
      have hb := Render.NodeGen3.bitOf_kidBitmap kids σ
      unfold Near.Render.NodeGen.bitOf at hb
      rw [hbit] at hb
      have hk := kbit_zero hb.symm
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hk
      simp only [Option.getD_some] at hk
      simp [List.getElem?_eq_getElem (show σ < kids.length by omega), hk, NKid.toKid3]

end

end ZkFormal.NearV3.Walk3

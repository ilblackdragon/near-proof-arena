import ZkFormal.NearV3.Spec.Records

/-!
# ZkFormal.NearV3.Link.Post3Spec — replacing value records is `PTrie.set`

Spec side of M6c.  Records `ns`, value records `V`:

* `setVal V i v` — `V` with the bytes of value record `i` replaced by `v` (instance kept);
  `setVals V ws` — a list of such replacements, left to right;
* `occ3` / `fullOcc ns i n` — number of occurrences of value record `i` in the unfolding of
  record `n` (with multiplicity: a shared node record counts once per path);
* `vreach3` / `fullReach ns n key` — the value record that the lookup of `key` from record `n`
  ends at (record-level mirror of `PTrie.find`; independent of the value bytes).

Results:
* `reach_find` — `fullReach ns n key = some i → (fullTree ns V n).find key = some (some (valOf V i))`;
* `reach_of_find` — conversely, if `key` finds `x` in `fullTree ns (setVal V i x) n` for
  **every** `x`, then `fullReach ns n key = some i` and `i < |V|`;
* **`post_eq_set`** — `i < |V|`, `fullReach ns root key = some i`, `fullOcc ns i root ≤ 1` ⇒
  `(fullTree ns V root).set key v = some (fullTree ns (setVal V i v) root)`
  (exact `PTrie` equality: `set` keeps every stored `memory_usage`, and so do the records;
  no length hypothesis is needed for this equality);
* `post_eq_sets` — the same for a list of writes (fold of `set`s = `setVals`);
* `setVal_comm` / `setVals_perm` — replacements at distinct value ids commute.
-/

namespace ZkFormal.NearV3

open NearSpec

/-! ## Replacing value records -/

/-- Value record `i` with bytes `v` (instance kept; no-op when `i ≥ |V|`). -/
def setVal : List ValRec3 → Nat → Bytes → List ValRec3
  | [], _, _ => []
  | r :: rs, 0, v => ⟨r.tau, v⟩ :: rs
  | r :: rs, i + 1, v => r :: setVal rs i v

/-- Replacements, left to right. -/
def setVals (V : List ValRec3) : List (Nat × Bytes) → List ValRec3
  | [] => V
  | (i, v) :: ws => setVals (setVal V i v) ws

theorem setVal_length : ∀ (V : List ValRec3) (i : Nat) (v : Bytes), (setVal V i v).length = V.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | r :: rs, i + 1, v => by simp [setVal, setVal_length rs i v]

theorem setVal_get? : ∀ (V : List ValRec3) (i : Nat) (v : Bytes) (j : Nat),
    (setVal V i v)[j]? = if j = i then V[j]?.map (fun r => ⟨r.tau, v⟩) else V[j]?
  | [], _, _, j => by simp [setVal]
  | _ :: _, 0, _, 0 => by simp [setVal]
  | _ :: _, 0, _, _ + 1 => by simp [setVal]
  | _ :: _, _ + 1, _, 0 => by simp [setVal]
  | r :: rs, i + 1, v, j + 1 => by simp [setVal, setVal_get? rs i v j]

theorem valOf_setVal_self {V : List ValRec3} {i : Nat} (hi : i < V.length) (v : Bytes) :
    valOf (setVal V i v) i = v := by
  simp [valOf, setVal_get?, List.getElem?_eq_getElem hi]

theorem valOf_setVal_ne (V : List ValRec3) {i j : Nat} (h : j ≠ i) (v : Bytes) :
    valOf (setVal V i v) j = valOf V j := by
  simp [valOf, setVal_get?, h]

theorem setVal_comm (V : List ValRec3) {i j : Nat} (h : i ≠ j) (a b : Bytes) :
    setVal (setVal V i a) j b = setVal (setVal V j b) i a := by
  apply List.ext_getElem?; intro n
  simp only [setVal_get?]
  by_cases hj : n = j
  · subst hj
    have : n ≠ i := fun e => h e.symm
    simp [this]
  · by_cases hi : n = i
    · subst hi; simp [hj]
    · simp [hj, hi]

theorem setVal_valOf (V : List ValRec3) (i : Nat) : setVal V i (valOf V i) = V := by
  apply List.ext_getElem?; intro n
  rw [setVal_get?]
  by_cases h : n = i
  · subst h; cases hv : V[n]? <;> simp [valOf, hv]
  · simp [h]

theorem setVals_length : ∀ (V : List ValRec3) (ws : List (Nat × Bytes)), (setVals V ws).length = V.length
  | _, [] => rfl
  | V, (i, v) :: ws => by rw [setVals, setVals_length _ ws, setVal_length]

/-- **Replacements at distinct value ids commute.** -/
theorem setVals_perm {ws ws' : List (Nat × Bytes)} (hp : ws.Perm ws') :
    (ws.map Prod.fst).Nodup → ∀ V, setVals V ws = setVals V ws' := by
  induction hp with
  | nil => intro _ _; rfl
  | cons x _ ih =>
    intro hd V
    obtain ⟨i, v⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hd
    simp only [setVals]; exact ih hd.2 _
  | swap x y l =>
    intro hd V
    obtain ⟨i, a⟩ := x; obtain ⟨j, b⟩ := y
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hd
    have hij : i ≠ j := fun e => hd.1 (Or.inl e.symm)
    simp only [setVals]; rw [setVal_comm V (Ne.symm hij)]
  | trans h1 _ ih1 ih2 =>
    intro hd V
    rw [ih1 hd V, ih2 ((List.Perm.map Prod.fst h1).nodup_iff.mp hd) V]

/-! ## Occurrences and reach (record level) -/

/-- Occurrences under a child list, children counted by `g`. -/
def kOcc (g : Nat → Nat) : List Kid3 → Nat
  | [] => 0
  | .node c :: r => g c + kOcc g r
  | .none :: r => kOcc g r
  | .hash _ :: r => kOcc g r

/-- Occurrences of value record `i` in the unfolding of record `n`, fuel `f`. -/
def occ3 (ns : List NodeRec3) (i : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n =>
    match ns[n]? with
    | none => 0
    | some nr => nr.node.vids.count i + kOcc (occ3 ns i f) nr.node.kids

def fullOcc (ns : List NodeRec3) (i n : Nat) : Nat := occ3 ns i ns.length n

/-- One record's lookup step: children looked up by `g`. -/
def recReach (g : Nat → List Nat → Option Nat) : Rec3 → List Nat → Option Nat
  | .leaf k (.val i) _, key => if k = key then some i else none
  | .leaf _ (.ref _ _) _, _ => none
  | .ext k (.node c) _, key => if isPrefix k key = true then g c (key.drop k.length) else none
  | .ext _ .none _, _ => none
  | .ext _ (.hash _) _, _ => none
  | .branch (some (.val i)) _ _, [] => some i
  | .branch (some (.ref _ _)) _ _, [] => none
  | .branch none _ _, [] => none
  | .branch _ kids _, j :: rest =>
    match kids[j]? with
    | some (Kid3.node c) => g c rest
    | _ => none

/-- The value record the lookup of `key` from record `n` ends at (fuel `f`). -/
def vreach3 (ns : List NodeRec3) : Nat → Nat → List Nat → Option Nat
  | 0, _, _ => none
  | f + 1, n, key =>
    match ns[n]? with
    | none => none
    | some nr => recReach (vreach3 ns f) nr.node key

def fullReach (ns : List NodeRec3) (n : Nat) (key : List Nat) : Option Nat := vreach3 ns ns.length n key

/-! ### Child lists -/

theorem kOcc_ge (g : Nat → Nat) : ∀ (kids : List Kid3) (j c : Nat), kids[j]? = some (Kid3.node c) →
    g c ≤ kOcc g kids
  | [], _, _, h => by simp at h
  | kd :: r, 0, c, h => by simp at h; subst h; simp [kOcc]
  | kd :: r, j + 1, c, h => by
    simp at h
    have := kOcc_ge g r j c h
    cases kd <;> simp [kOcc] <;> omega

theorem kOcc_two (g : Nat → Nat) : ∀ (kids : List Kid3) (j j' c c' : Nat), kids[j]? = some (Kid3.node c) →
    kids[j']? = some (Kid3.node c') → j ≠ j' → g c + g c' ≤ kOcc g kids
  | [], _, _, _, _, h, _, _ => by simp at h
  | kd :: r, 0, 0, _, _, _, _, hne => absurd rfl hne
  | kd :: r, 0, j' + 1, c, c', h, h', _ => by
    simp at h h'; subst h; have := kOcc_ge g r j' c' h'; simp [kOcc]; omega
  | kd :: r, j + 1, 0, c, c', h, h', _ => by
    simp at h h'; subst h'; have := kOcc_ge g r j c h; simp [kOcc]; omega
  | kd :: r, j + 1, j' + 1, c, c', h, h', hne => by
    simp at h h'
    have := kOcc_two g r j j' c c' h h' (by omega)
    cases kd <;> simp [kOcc] <;> omega

theorem kOcc_zero (g : Nat → Nat) : ∀ (kids : List Kid3), kOcc g kids = 0 → ∀ c, Kid3.node c ∈ kids → g c = 0
  | [], _, _, h => by simp at h
  | kd :: r, h0, c, h => by
    simp only [List.mem_cons] at h
    cases kd with
    | node c'' =>
      simp only [kOcc] at h0
      rcases h with e | h
      · cases e; omega
      · exact kOcc_zero g r (by omega) c h
    | none =>
      simp only [kOcc] at h0
      rcases h with e | h
      · cases e
      · exact kOcc_zero g r h0 c h
    | hash _ =>
      simp only [kOcc] at h0
      rcases h with e | h
      · cases e
      · exact kOcc_zero g r h0 c h

theorem kidsOf3_congrP {g g' : Nat → PTrie} : ∀ (kids : List Kid3),
    (∀ c, Kid3.node c ∈ kids → g c = g' c) → kidsOf3 g kids = kidsOf3 g' kids
  | [], _ => rfl
  | kid :: r, h => by
    have ih := kidsOf3_congrP r (fun c hc => h c (List.mem_cons_of_mem _ hc))
    cases kid with
    | none => simp [kidsOf3, ih]
    | hash _ => simp [kidsOf3, ih]
    | node c => simp [kidsOf3, ih, h c (by simp)]

theorem kidsOf3_congrI {g g' : Nat → PTrie} : ∀ (kids : List Kid3),
    (∀ (j c : Nat), kids[j]? = some (Kid3.node c) → g c = g' c) → kidsOf3 g kids = kidsOf3 g' kids := by
  intro kids h
  apply kidsOf3_congrP kids
  intro c hc
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hc
  exact h j c (by rw [List.getElem?_eq_getElem hj, he])

theorem kids_find (g : Nat → PTrie) (rest : List Nat) : ∀ (kids : List Kid3) (j c : Nat),
    kids[j]? = some (Kid3.node c) → Kids.find (kidsOf3 g kids) j rest = (g c).find rest
  | [], _, _, h => by simp at h
  | kd :: r, 0, c, h => by simp at h; subst h; simp [kidsOf3, Kids.find]
  | kd :: r, j + 1, c, h => by
    simp at h
    have := kids_find g rest r j c h
    cases kd <;> simp [kidsOf3, Kids.find, this]

theorem kids_find_inv (g : Nat → PTrie) (rest : List Nat) {b : Bytes} : ∀ (kids : List Kid3) (j : Nat),
    Kids.find (kidsOf3 g kids) j rest = some (some b) →
    ∃ c, kids[j]? = some (Kid3.node c) ∧ (g c).find rest = some (some b)
  | [], _, h => by simp [kidsOf3, Kids.find] at h
  | kd :: r, 0, h => by
    cases kd with
    | none => simp [kidsOf3, Kids.find] at h
    | hash _ => simp [kidsOf3, Kids.find, PTrie.find] at h
    | node c => exact ⟨c, by simp, by simpa [kidsOf3, Kids.find] using h⟩
  | kd :: r, j + 1, h => by
    have key : Kids.find (kidsOf3 g r) j rest = some (some b) := by
      cases kd <;> simpa [kidsOf3, Kids.find] using h
    obtain ⟨c, hc, hf⟩ := kids_find_inv g rest r j key
    exact ⟨c, by simpa using hc, hf⟩

theorem kids_set (rest : List Nat) (v : Bytes) {g g' : Nat → PTrie} : ∀ (kids : List Kid3) (j c : Nat),
    kids[j]? = some (Kid3.node c) → (g c).set rest v = some (g' c) →
    (∀ j' c', j' ≠ j → kids[j']? = some (Kid3.node c') → g' c' = g c') →
    Kids.set (kidsOf3 g kids) j rest v = some (kidsOf3 g' kids)
  | [], _, _, h, _, _ => by simp at h
  | kd :: r, 0, c, h, hs, ho => by
    simp at h; subst h
    have hr : kidsOf3 g r = kidsOf3 g' r :=
      kidsOf3_congrI r (fun j c' hj => (ho (j + 1) c' (by omega) (by simpa using hj)).symm)
    simp [kidsOf3, Kids.set, hs, hr]
  | kd :: r, j + 1, c, h, hs, ho => by
    simp at h
    have ih := kids_set rest v r j c h hs (fun j' c' hne hj' => ho (j' + 1) c' (by omega) (by simpa using hj'))
    cases kd with
    | none => simp [kidsOf3, Kids.set, ih]
    | hash _ => simp [kidsOf3, Kids.set, ih]
    | node c'' =>
      have e := ho 0 c'' (by omega) (by simp)
      simp [kidsOf3, Kids.set, ih, e]

/-! ### Records -/

theorem nodeTree3_congrP (V : List ValRec3) {g g' : Nat → PTrie} (r : Rec3)
    (h : ∀ c, Kid3.node c ∈ r.kids → g c = g' c) : nodeTree3 V g r = nodeTree3 V g' r := by
  cases r with
  | leaf => rfl
  | ext k kid m =>
    cases kid with
    | node c => simp [nodeTree3, kidTree3, h c (by simp [Rec3.kids])]
    | _ => rfl
  | branch v kids m => simp [nodeTree3, kidsOf3_congrP kids (fun c hc => h c (by simpa [Rec3.kids]))]

theorem nodeTree3_setVal (V : List ValRec3) (g : Nat → PTrie) {i : Nat} (v : Bytes) (r : Rec3)
    (h : r.vids.count i = 0) : nodeTree3 (setVal V i v) g r = nodeTree3 V g r := by
  cases r with
  | leaf k s m =>
    cases s with
    | ref => rfl
    | val j =>
      have : j ≠ i := by intro e; subst e; simp [Rec3.vids] at h
      simp [nodeTree3, slot3, valOf_setVal_ne V this]
  | ext => rfl
  | branch sv kids m =>
    cases sv with
    | none => rfl
    | some s =>
      cases s with
      | ref => rfl
      | val j =>
        have : j ≠ i := by intro e; subst e; simp [Rec3.vids] at h
        simp [nodeTree3, slot3, valOf_setVal_ne V this]

variable {ns : List NodeRec3}

/-- No occurrence: the replacement does not change the subtrie. -/
theorem occ_zero (V : List ValRec3) (i : Nat) (v : Bytes) :
    ∀ f n, occ3 ns i f n = 0 → treeOf3 ns (setVal V i v) f n = treeOf3 ns V f n := by
  intro f
  induction f with
  | zero => intro n _; rfl
  | succ f ih =>
    intro n h
    simp only [occ3] at h
    simp only [treeOf3]
    cases hn : ns[n]? with
    | none => rfl
    | some nr =>
      rw [hn] at h; simp only at h ⊢
      rw [nodeTree3_congrP (setVal V i v) nr.node (g' := treeOf3 ns V f)
        (fun c hc => ih c (kOcc_zero _ _ (by omega) c hc))]
      exact nodeTree3_setVal V _ v nr.node (by omega)

/-- A reached value record occurs. -/
theorem reach_pos {i : Nat} : ∀ f n key, vreach3 ns f n key = some i → 1 ≤ occ3 ns i f n := by
  intro f
  induction f with
  | zero => intro n key h; simp [vreach3] at h
  | succ f ih =>
    intro n key h
    simp only [vreach3] at h
    simp only [occ3]
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp at h
    | some nr =>
      rw [hn] at h; simp only at h ⊢
      generalize nr.node = r at h ⊢
      cases r with
      | leaf k s m =>
        cases s with
        | ref => simp [recReach] at h
        | val j =>
          simp only [recReach] at h; split at h <;> simp at h; subst h; simp [Rec3.vids]
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [recReach] at h; split at h
          · have := ih c _ h; simp [Rec3.vids, Rec3.kids, kOcc]; omega
          · simp at h
        | none => simp [recReach] at h
        | hash _ => simp [recReach] at h
      | branch sv kids m =>
        cases key with
        | nil =>
          cases sv with
          | none => simp [recReach] at h
          | some s =>
            cases s with
            | ref => simp [recReach] at h
            | val j => simp [recReach] at h; subst h; simp [Rec3.vids]
        | cons j rest =>
          simp only [recReach] at h
          split at h
          · rename_i c hc
            have h1 := ih c rest h
            have h2 := kOcc_ge (occ3 ns i f) kids j c hc
            simp only [Rec3.kids]; omega
          · simp at h

/-- **Reach gives the lookup.** -/
theorem reach_find (V : List ValRec3) {i : Nat} : ∀ f n key, vreach3 ns f n key = some i →
    (treeOf3 ns V f n).find key = some (some (valOf V i)) := by
  intro f
  induction f with
  | zero => intro n key h; simp [vreach3] at h
  | succ f ih =>
    intro n key h
    simp only [vreach3] at h
    simp only [treeOf3]
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp at h
    | some nr =>
      rw [hn] at h; simp only at h ⊢
      generalize nr.node = r at h ⊢
      cases r with
      | leaf k s m =>
        cases s with
        | ref => simp [recReach] at h
        | val j =>
          simp only [recReach] at h; split at h <;> simp at h; subst h
          rename_i hk; subst hk; simp [nodeTree3, slot3, PTrie.find, Slot.get]
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [recReach] at h; split at h
          · rename_i hp; simp [nodeTree3, kidTree3, PTrie.find, hp, ih c _ h]
          · simp at h
        | none => simp [recReach] at h
        | hash _ => simp [recReach] at h
      | branch sv kids m =>
        cases key with
        | nil =>
          cases sv with
          | none => simp [recReach] at h
          | some s =>
            cases s with
            | ref => simp [recReach] at h
            | val j => simp [recReach] at h; subst h; simp [nodeTree3, slot3, PTrie.find, Slot.get]
        | cons j rest =>
          simp only [recReach] at h
          split at h
          · rename_i c hc
            simp only [nodeTree3, PTrie.find]
            rw [kids_find _ rest kids j c hc]; exact ih c rest h
          · simp at h

/-- **A found value is reached.** -/
theorem find_reach (V : List ValRec3) {b : Bytes} : ∀ f n key,
    (treeOf3 ns V f n).find key = some (some b) → ∃ j, vreach3 ns f n key = some j ∧ valOf V j = b := by
  intro f
  induction f with
  | zero => intro n key h; simp [treeOf3, PTrie.find] at h
  | succ f ih =>
    intro n key h
    simp only [treeOf3] at h
    simp only [vreach3]
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp [PTrie.find] at h
    | some nr =>
      rw [hn] at h; simp only at h ⊢
      generalize nr.node = r at h ⊢
      cases r with
      | leaf k s m =>
        cases s with
        | ref => simp [nodeTree3, slot3, PTrie.find, Slot.get] at h
        | val j =>
          simp only [nodeTree3, slot3, PTrie.find, Slot.get] at h
          split at h
          · rename_i hk; subst hk; simp at h; exact ⟨j, by simp [recReach], h⟩
          · simp at h
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [nodeTree3, kidTree3, PTrie.find] at h
          split at h
          · rename_i hp
            obtain ⟨j, hj, hv⟩ := ih c _ h
            exact ⟨j, by simp [recReach, hp, hj], hv⟩
          · simp at h
        | none =>
          simp only [nodeTree3, kidTree3, PTrie.find] at h; split at h <;> simp at h
        | hash _ =>
          simp only [nodeTree3, kidTree3, PTrie.find] at h; split at h <;> simp at h
      | branch sv kids m =>
        cases key with
        | nil =>
          cases sv with
          | none => simp [nodeTree3, PTrie.find] at h
          | some s =>
            cases s with
            | ref => simp [nodeTree3, slot3, PTrie.find, Slot.get] at h
            | val j =>
              simp [nodeTree3, slot3, PTrie.find, Slot.get] at h
              exact ⟨j, by simp [recReach], h⟩
        | cons j rest =>
          simp only [nodeTree3, PTrie.find] at h
          obtain ⟨c, hc, hf⟩ := kids_find_inv _ rest kids j h
          obtain ⟨j', hj', hv⟩ := ih c rest hf
          exact ⟨j', by simp [recReach, hc, hj'], hv⟩

theorem valOf_len_le (V : List ValRec3) (j : Nat) :
    (valOf V j).length ≤ (V.map fun r => r.bytes.length).sum := by
  unfold valOf
  cases hj : V[j]? with
  | none => simp
  | some r =>
    simp only [Option.map_some, Option.getD_some]
    have hm : r ∈ V := List.mem_of_getElem? hj
    clear hj
    induction V with
    | nil => simp at hm
    | cons a V ih =>
      simp only [List.mem_cons] at hm
      simp only [List.map_cons, List.sum_cons]
      rcases hm with rfl | hm
      · omega
      · have := ih hm; omega

/-- **The semantic form of reach**: if `key` finds `x` for every replacement `x` of value
record `i`, the lookup reaches record `i` (`x` fresh: longer than every value). -/
theorem reach_of_find (V : List ValRec3) {i f n : Nat} {key : List Nat}
    (h : ∀ x, (treeOf3 ns (setVal V i x) f n).find key = some (some x)) :
    vreach3 ns f n key = some i ∧ i < V.length := by
  let x : Bytes := List.replicate ((V.map fun r => r.bytes.length).sum + 1) 0
  have hx : x.length = (V.map fun r => r.bytes.length).sum + 1 := by simp [x]
  obtain ⟨j, hj, hv⟩ := find_reach _ f n key (h x)
  by_cases hji : j = i
  · subst hji
    refine ⟨hj, ?_⟩
    apply Classical.byContradiction; intro hlt
    have e : valOf (setVal V j x) j = [] := by
      simp [valOf, setVal_get?, List.getElem?_eq_none (by omega : V.length ≤ j)]
    rw [e] at hv; have := congrArg List.length hv; simp [hx] at this
  · rw [valOf_setVal_ne V hji] at hv
    have := valOf_len_le V j; rw [hv, hx] at this; omega

/-! ## `set` -/

/-- **One write (fuel form).** -/
theorem treeOf3_set (V : List ValRec3) {i : Nat} (hi : i < V.length) (v : Bytes) :
    ∀ f n key, vreach3 ns f n key = some i → occ3 ns i f n ≤ 1 →
      (treeOf3 ns V f n).set key v = some (treeOf3 ns (setVal V i v) f n) := by
  intro f
  induction f with
  | zero => intro n key h; simp [vreach3] at h
  | succ f ih =>
    intro n key h ho
    simp only [vreach3] at h
    simp only [occ3] at ho
    simp only [treeOf3]
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp at h
    | some nr =>
      rw [hn] at h ho; simp only at h ho ⊢
      generalize nr.node = r at h ho ⊢
      cases r with
      | leaf k s m =>
        cases s with
        | ref => simp [recReach] at h
        | val j =>
          simp only [recReach] at h; split at h <;> simp at h; subst h
          rename_i hk; subst hk
          simp [nodeTree3, slot3, PTrie.set, Slot.get, valOf_setVal_self hi]
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [recReach] at h; split at h
          · rename_i hp
            have hoc : occ3 ns i f c ≤ 1 := by simp [Rec3.vids, Rec3.kids, kOcc] at ho; omega
            simp [nodeTree3, kidTree3, PTrie.set, hp, ih c _ h hoc]
          · simp at h
        | none => simp [recReach] at h
        | hash _ => simp [recReach] at h
      | branch sv kids m =>
        cases key with
        | nil =>
          cases sv with
          | none => simp [recReach] at h
          | some s =>
            cases s with
            | ref => simp [recReach] at h
            | val j =>
              simp [recReach] at h; subst h
              simp only [Rec3.vids, Rec3.kids, List.count_singleton_self] at ho
              have hk : kidsOf3 (treeOf3 ns V f) kids = kidsOf3 (treeOf3 ns (setVal V j v) f) kids :=
                kidsOf3_congrP kids (fun c hc => (occ_zero V j v f c (kOcc_zero _ kids (by omega) c hc)).symm)
              simp [nodeTree3, slot3, PTrie.set, valOf_setVal_self hi, hk]
        | cons j rest =>
          simp only [recReach] at h
          split at h
          · rename_i c hc
            have h1 := reach_pos f c rest h
            have h2 := kOcc_ge (occ3 ns i f) kids j c hc
            simp only [Rec3.kids] at ho
            have hvid : (Rec3.branch sv kids m).vids.count i = 0 := by omega
            have hs := ih c rest h (by omega)
            have hkids := kids_set rest v kids j c hc hs (fun j' c' hne hj' => by
              have := kOcc_two (occ3 ns i f) kids j j' c c' hc hj' (Ne.symm hne)
              exact occ_zero V i v f c' (by omega))
            have hsv := nodeTree3_setVal V (treeOf3 ns (setVal V i v) f) v (.branch sv kids m) hvid
            rw [hsv]
            simp [nodeTree3, PTrie.set, hkids]
          · simp at h

/-- **`post_eq_set`**: replacing the value record that `key` reaches (one occurrence) is
`PTrie.set key`. -/
theorem post_eq_set (V : List ValRec3) {root i : Nat} {key : List Nat} (v : Bytes) (hi : i < V.length)
    (hr : fullReach ns root key = some i) (ho : fullOcc ns i root ≤ 1) :
    (fullTree ns V root).set key v = some (fullTree ns (setVal V i v) root) :=
  treeOf3_set V hi v _ root key hr ho

/-- The semantic form: `key` finds `x` after replacing value record `i` by any `x`. -/
theorem post_eq_set' (V : List ValRec3) {root i : Nat} {key : List Nat} (v : Bytes)
    (hr : ∀ x, (fullTree ns (setVal V i x) root).find key = some (some x)) (ho : fullOcc ns i root ≤ 1) :
    (fullTree ns V root).set key v = some (fullTree ns (setVal V i v) root) := by
  obtain ⟨hr', hi⟩ := reach_of_find V hr
  exact post_eq_set V v hi hr' ho

/-- Apply `set`s left to right. -/
def setAll (t : PTrie) : List (List Nat × Bytes) → Option PTrie
  | [] => some t
  | (k, v) :: r => (t.set k v).bind fun t' => setAll t' r

/-- **A list of writes** `(value id, key, new value)`: the fold of `set`s is `setVals`.
(Reach and occurrence counts do not depend on the value bytes, so they are stated once.) -/
theorem post_eq_sets {root : Nat} : ∀ (ws : List (Nat × List Nat × Bytes)) (V : List ValRec3),
    (∀ w ∈ ws, w.1 < V.length ∧ fullReach ns root w.2.1 = some w.1 ∧ fullOcc ns w.1 root ≤ 1) →
    setAll (fullTree ns V root) (ws.map fun w => (w.2.1, w.2.2)) =
      some (fullTree ns (setVals V (ws.map fun w => (w.1, w.2.2))) root)
  | [], _, _ => rfl
  | (i, k, v) :: ws, V, h => by
    obtain ⟨hi, hr, ho⟩ := h (i, k, v) (by simp)
    simp only [List.map_cons, setAll, setVals, post_eq_set V v hi hr ho, Option.bind_some]
    exact post_eq_sets ws _ (fun w hw => by
      obtain ⟨a, b, c⟩ := h w (by simp [hw]); exact ⟨by rw [setVal_length]; exact a, b, c⟩)

end ZkFormal.NearV3

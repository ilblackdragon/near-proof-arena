import ZkFormal.NearV3.Spec.StoreSound
import ZkFormal.NearV3.Spec.StoreBuilt

/-!
# ZkFormal.NearV3.Spec.Occs — occurrences in a partial trie, node skeletons

Tools for the completeness direction of `StoreBuildStmt`:

* `occs t` — the revealed node subtrees of `t` (pre-order); `valsOf t` — the
  revealed values; `children t` — the immediate child subtrees;
* inheritance of `wf` / `Stored` to occurrences;
* `skel_eq` — two well-formed revealed nodes with the same preimage
  (`nodeEnc`) have the same *skeleton*: same constructor, key, `memory_usage`,
  value references and child hashes.  (Decoding by `buildFor` is a function of
  the bytes.)
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

mutual
/-- Revealed node subtrees, pre-order. -/
def occs : PTrie → List PTrie
  | .hash _ => []
  | .leaf k v m => [.leaf k v m]
  | .ext k c m => .ext k c m :: occs c
  | .branch v cs m => .branch v cs m :: kOccs cs
def kOccs : Kids → List PTrie
  | .nil => []
  | .none r => kOccs r
  | .some c r => occs c ++ kOccs r
end

/-- Revealed value of a slot. -/
def slotVal : Slot → List Bytes
  | .val v => [v]
  | .ref _ _ => []

def optSlotVal : Option Slot → List Bytes
  | some s => slotVal s
  | none => []

/-- Revealed values held directly by a node. -/
def ownVals : PTrie → List Bytes
  | .leaf _ s _ => slotVal s
  | .branch v _ _ => optSlotVal v
  | _ => []

/-- Revealed values of `t`. -/
def valsOf (t : PTrie) : List Bytes := (occs t).flatMap ownVals

def kidsList : Kids → List PTrie
  | .nil => []
  | .none r => kidsList r
  | .some c r => c :: kidsList r

/-- Immediate child subtrees. -/
def children : PTrie → List PTrie
  | .ext _ c _ => [c]
  | .branch _ cs _ => kidsList cs
  | _ => []

/-! ## Occurrences -/

theorem self_mem_occs {t : PTrie} (h : isNode t = true) : t ∈ occs t := by
  cases t <;> simp_all [occs, isNode]

mutual
theorem occs_isNode : ∀ (t o : PTrie), o ∈ occs t → isNode o = true
  | .hash _, o, h => by simp [occs] at h
  | .leaf .., o, h => by simp [occs] at h; subst h; rfl
  | .ext k c m, o, h => by
    simp only [occs, List.mem_cons] at h
    rcases h with rfl | h; · rfl
    exact occs_isNode c o h
  | .branch v cs m, o, h => by
    simp only [occs, List.mem_cons] at h
    rcases h with rfl | h; · rfl
    exact kOccs_isNode cs o h
theorem kOccs_isNode : ∀ (cs : Kids) (o : PTrie), o ∈ kOccs cs → isNode o = true
  | .nil, o, h => by simp [kOccs] at h
  | .none r, o, h => kOccs_isNode r o (by simpa [kOccs] using h)
  | .some c r, o, h => by
    simp only [kOccs, List.mem_append] at h
    rcases h with h | h
    · exact occs_isNode c o h
    · exact kOccs_isNode r o h
end

mutual
/-- Occurrences of an occurrence are occurrences. -/
theorem occs_trans : ∀ (t o : PTrie), o ∈ occs t → ∀ o', o' ∈ occs o → o' ∈ occs t
  | .hash _, o, h, _, _ => by simp [occs] at h
  | .leaf .., o, h, o', h' => by simp [occs] at h; subst h; exact h'
  | .ext k c m, o, h, o', h' => by
    simp only [occs, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simpa [occs] using h'
    · exact Or.inr (occs_trans c o h o' h')
  | .branch v cs m, o, h, o', h' => by
    simp only [occs, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simpa [occs] using h'
    · exact Or.inr (kOccs_trans cs o h o' h')
theorem kOccs_trans : ∀ (cs : Kids) (o : PTrie), o ∈ kOccs cs → ∀ o', o' ∈ occs o → o' ∈ kOccs cs
  | .nil, o, h, _, _ => by simp [kOccs] at h
  | .none r, o, h, o', h' => by simpa [kOccs] using kOccs_trans r o (by simpa [kOccs] using h) o' h'
  | .some c r, o, h, o', h' => by
    simp only [kOccs, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (occs_trans c o h o' h')
    · exact Or.inr (kOccs_trans r o h o' h')
end

theorem kidsList_occs : ∀ (cs : Kids) (c : PTrie), c ∈ kidsList cs → isNode c = true → c ∈ kOccs cs
  | .nil, c, h, _ => by simp [kidsList] at h
  | .none r, c, h, hn => by simpa [kOccs] using kidsList_occs r c (by simpa [kidsList] using h) hn
  | .some d r, c, h, hn => by
    simp only [kidsList, List.mem_cons] at h
    simp only [kOccs, List.mem_append]
    rcases h with rfl | h
    · exact Or.inl (self_mem_occs hn)
    · exact Or.inr (kidsList_occs r c h hn)

/-- A revealed child of an occurrence is an occurrence. -/
theorem child_occ {t o c : PTrie} (ho : o ∈ occs t) (hc : c ∈ children o) (hn : isNode c = true) :
    c ∈ occs t := by
  apply occs_trans t o ho
  cases o with
  | hash => simp [children] at hc
  | leaf => simp [children] at hc
  | ext k c' m =>
    simp [children] at hc; subst hc
    simp [occs, self_mem_occs hn]
  | branch v cs m =>
    simp only [children] at hc
    simp only [occs, List.mem_cons]
    exact Or.inr (kidsList_occs cs c hc hn)

theorem ownVals_sub {t o : PTrie} (ho : o ∈ occs t) {v : Bytes} (hv : v ∈ ownVals o) : v ∈ valsOf t :=
  List.mem_flatMap.2 ⟨o, ho, hv⟩

/-! ## Inherited properties -/

mutual
theorem occs_wf : ∀ (t : PTrie), t.wf = true → ∀ o ∈ occs t, o.wf = true
  | .hash _, _, o, h => by simp [occs] at h
  | .leaf .., hw, o, h => by simp [occs] at h; subst h; exact hw
  | .ext k c m, hw, o, h => by
    simp only [occs, List.mem_cons] at h
    rcases h with rfl | h; · exact hw
    exact occs_wf c (wf_ext hw).2 o h
  | .branch v cs m, hw, o, h => by
    simp only [occs, List.mem_cons] at h
    rcases h with rfl | h; · exact hw
    exact kOccs_wf cs 16 (wf_branch hw) o h
theorem kOccs_wf : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → ∀ o ∈ kOccs cs, o.wf = true
  | .nil, _, _, o, h => by simp [kOccs] at h
  | .none r, n, hw, o, h => kOccs_wf r (n - 1) (wf_kids_none hw) o (by simpa [kOccs] using h)
  | .some c r, n, hw, o, h => by
    simp only [kOccs, List.mem_append] at h
    rcases h with h | h
    · exact occs_wf c (wf_kids_some hw).1 o h
    · exact kOccs_wf r (n - 1) (wf_kids_some hw).2 o h
end

mutual
theorem occs_stored (s : Store) : ∀ (t : PTrie), Stored s t → ∀ o ∈ occs t, Stored s o
  | .hash _, _, o, h => by simp [occs] at h
  | .leaf .., hs, o, h => by simp [occs] at h; subst h; exact hs
  | .ext k c m, hs, o, h => by
    simp only [occs, List.mem_cons] at h
    rcases h with rfl | h; · exact hs
    exact occs_stored s c hs.2 o h
  | .branch v cs m, hs, o, h => by
    simp only [occs, List.mem_cons] at h
    rcases h with rfl | h; · exact hs
    exact kOccs_stored s cs hs.2.2 o h
theorem kOccs_stored (s : Store) : ∀ (cs : Kids), KidsStored s cs → ∀ o ∈ kOccs cs, Stored s o
  | .nil, _, o, h => by simp [kOccs] at h
  | .none r, hs, o, h => kOccs_stored s r hs o (by simpa [kOccs] using h)
  | .some c r, hs, o, h => by
    simp only [kOccs, List.mem_append] at h
    rcases h with h | h
    · exact occs_stored s c hs.1 o h
    · exact kOccs_stored s r hs.2 o h
end

theorem stored_found {s : Store} {o : PTrie} (hs : Stored s o) (hn : isNode o = true) :
    Found s (nodeEnc o) := by
  cases o with
  | hash => simp [isNode] at hn
  | leaf => exact hs.1
  | ext => exact hs.1
  | branch => exact hs.1

theorem stored_ownVals {s : Store} {o : PTrie} (hs : Stored s o) : ∀ v ∈ ownVals o, Found s v := by
  intro v hv
  cases o with
  | hash => simp [ownVals] at hv
  | ext => simp [ownVals] at hv
  | leaf k sl m =>
    cases sl with
    | val b => simp [ownVals, slotVal] at hv; subst hv; exact hs.2
    | ref => simp [ownVals, slotVal] at hv
  | branch bv cs m =>
    cases bv with
    | none => simp [ownVals, optSlotVal] at hv
    | some sl =>
      cases sl with
      | val b => simp [ownVals, optSlotVal, slotVal] at hv; subst hv; exact hs.2.1
      | ref => simp [ownVals, optSlotVal, slotVal] at hv

/-- Two found entries with the same digest are equal. -/
theorem found_inj {s : Store} {a b : Bytes} (ha : Found s a) (hb : Found s b)
    (h : sha256 a = sha256 b) : a = b := by
  unfold Found at ha hb; rw [h] at ha; rw [ha] at hb; exact Option.some.inj hb

/-! ## Skeletons -/

/-- Children replaced by their hashes, values by their references. -/
def skelKids : List (Option Bytes) → Kids
  | [] => .nil
  | none :: r => .none (skelKids r)
  | some h :: r => .some (.hash h) (skelKids r)

theorem skelKids_inj : ∀ (a b : List (Option Bytes)), skelKids a = skelKids b → a = b
  | [], [], _ => rfl
  | [], none :: _, h => by simp [skelKids] at h
  | [], some _ :: _, h => by simp [skelKids] at h
  | none :: _, [], h => by simp [skelKids] at h
  | some _ :: _, [], h => by simp [skelKids] at h
  | none :: r, none :: r', h => by simp [skelKids] at h; rw [skelKids_inj r r' h]
  | none :: _, some _ :: _, h => by simp [skelKids] at h
  | some _ :: _, none :: _, h => by simp [skelKids] at h
  | some x :: r, some y :: r', h => by
    simp [skelKids] at h; rw [h.1, skelKids_inj r r' h.2]

theorem buildKids_zero (s : Store) : ∀ (i : Nat) (hs : List (Option Bytes)) (keys : List (List Nat)),
    buildKidsWith (buildFor s 0) i hs keys = skelKids hs
  | _, [], _ => rfl
  | i, none :: r, keys => by simp [buildKidsWith, skelKids, buildKids_zero s (i + 1) r keys]
  | i, some h :: r, keys => by
    simp only [buildKidsWith, skelKids, buildKids_zero s (i + 1) r keys]; rfl

/-- Decoding skeleton of a node's preimage. -/
def skelOf (t : PTrie) : PTrie := buildFor (mkStore [nodeEnc t]) 1 t.hashOf [[16]]

theorem found_single (b : Bytes) : Found (mkStore [b]) b := by
  simp [Found, storeGet, mkStore]

theorem skel_eq {a b : PTrie} (ha : isNode a = true) (hb : isNode b = true)
    (h : nodeEnc a = nodeEnc b) : skelOf a = skelOf b := by
  unfold skelOf
  rw [hashOf_eq_enc a ha, hashOf_eq_enc b hb, h]

theorem not_key16 {k : List Nat} (hk : nibblesOk k = true) : ([[16]] : List (List Nat)).any (· == k) = false := by
  simp only [List.any_cons, List.any_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
  intro e; subst e; simp [nibblesOk] at hk

theorem mkSlot_false (s : Store) (len : Nat) (vh : Bytes) : mkSlot s len vh false = .ref len vh := by
  simp [mkSlot]

theorem skel_leaf {k : List Nat} {v : Slot} {m : Nat} (hw : (PTrie.leaf k v m).wf = true) :
    skelOf (.leaf k v m) = .leaf k (.ref v.len (slotHash v)) m := by
  unfold skelOf
  rw [buildFor_leaf _ 0 _ rfl k v m hw (found_single _), not_key16 (wf_leaf hw), mkSlot_false]

theorem skel_ext {k : List Nat} {c : PTrie} {m : Nat} (hw : (PTrie.ext k c m).wf = true) :
    skelOf (.ext k c m) = .ext k (.hash c.hashOf) m := by
  unfold skelOf
  rw [buildFor_ext _ 0 _ rfl k c m hw (found_single _)]; rfl

theorem skel_branch {cs : Kids} {m : Nat} (hw : (PTrie.branch none cs m).wf = true) :
    skelOf (.branch none cs m) = .branch none (skelKids (Kids.optHashes cs)) m := by
  unfold skelOf
  rw [buildFor_branch _ 0 _ rfl cs m hw (found_single _), buildKids_zero]

theorem skel_branchV {v : Slot} {cs : Kids} {m : Nat} (hw : (PTrie.branch (some v) cs m).wf = true) :
    skelOf (.branch (some v) cs m) =
      .branch (some (.ref v.len (slotHash v))) (skelKids (Kids.optHashes cs)) m := by
  unfold skelOf
  rw [buildFor_branchV _ 0 _ rfl v cs m hw (found_single _), buildKids_zero]
  simp [mkSlot]

end ZkFormal.NearV3

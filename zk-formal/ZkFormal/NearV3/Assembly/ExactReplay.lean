import ZkFormal.NearV3.Assembly.StoreReplay

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Lookup restriction permits dropping bytes, but never changes the winning preimage. -/
def StoreSubset (small large : Store) : Prop :=
  ∀ h b, storeGet small h = some b → storeGet large h = some b

theorem built_hashOf_all (ws : List Bytes) (fuel : Nat) (root : Bytes)
    (keys : List (List Nat)) : (buildFor (mkStore ws) fuel root keys).hashOf = root := by
  by_cases hr : root.length = 32
  · exact (built_spec ws fuel root keys hr).1
  · have hn : storeGet (mkStore ws) root = none := by
      cases h : storeGet (mkStore ws) root with
      | none => rfl
      | some b =>
        have he := (storeGet_some h).1
        have hl := congrArg List.length he
        simp only [sha256, ArenaCore.sha256_length] at hl
        exact False.elim (hr hl.symm)
    cases fuel with
    | zero => rfl
    | succ f => simp [buildFor, hn, PTrie.hashOf]

theorem stored_lookup_none {s : Store} (t : PTrie)
    (ht : Stored s t) (hn : storeGet s t.hashOf = none) : t = .hash t.hashOf := by
  cases t with
  | hash => rfl
  | leaf k v m =>
    have hf := ht.1
    simp only [Found, nodeEnc, PTrie.hashOf] at hf hn
    rw [hf] at hn
    cases hn
  | ext k c m =>
    have hf := ht.1
    simp only [Found, nodeEnc, PTrie.hashOf] at hf hn
    rw [hf] at hn
    cases hn
  | branch v cs m =>
    have hf := ht.1
    cases v <;> simp only [Found, nodeEnc, PTrie.hashOf] at hf hn <;> rw [hf] at hn <;> cases hn

theorem mkSlot_replay {small : Store} {ws : List Bytes} (hs : StoreSubset small (mkStore ws))
    (len : Nat) (vh : Bytes) (want : Bool)
    (hv : SlotStored small (mkSlot (mkStore ws) len vh want)) :
    mkSlot small len vh want = mkSlot (mkStore ws) len vh want := by
  cases want with
  | false => rfl
  | true =>
    simp only [mkSlot, ite_true] at hv ⊢
    cases hl : storeGet (mkStore ws) vh with
    | none =>
      have hn : storeGet small vh = none := by
        cases hh : storeGet small vh with
        | none => rfl
        | some b => have := hs vh b hh; rw [hl] at this; cases this
      rw [hn]
    | some b =>
      simp only [hl] at hv ⊢
      split at hv
      · rename_i he
        have hf : storeGet small (sha256 b) = some b := hv
        rw [(storeGet_some hl).1] at hf
        rw [hf]
      · rename_i he
        cases hh : storeGet small vh with
        | none => simp [he]
        | some b' =>
          have heq := hs vh b' hh
          rw [hl] at heq
          cases heq
          simp [he]

theorem buildKidsWith_replay (small : Store) (f g : Bytes → List (List Nat) → PTrie)
    (hf : ∀ root keys, Stored small (f root keys) → g root keys = f root keys) :
    ∀ i hs keys, KidsStored small (buildKidsWith f i hs keys) →
      buildKidsWith g i hs keys = buildKidsWith f i hs keys := by
  intro i hs
  induction hs generalizing i with
  | nil => intro keys h; rfl
  | cons h hs ih =>
    intro keys hh
    cases h with
    | none =>
      simp only [buildKidsWith] at hh ⊢
      rw [ih _ _ hh]
    | some root =>
      simp only [buildKidsWith, KidsStored] at hh ⊢
      rw [hf _ _ hh.1, ih _ _ hh.2]

theorem branchWith_replay (small : Store) (f g : Bytes → List (List Nat) → PTrie)
    (hf : ∀ root keys, Stored small (f root keys) → g root keys = f root keys)
    (h : Bytes) (v : Option Slot) (rest : Bytes) (keys : List (List Nat)) (mem : Nat)
    (ht : Stored small (branchWith f h v rest keys mem)) :
    branchWith g h v rest keys mem = branchWith f h v rest keys mem := by
  unfold branchWith at ht ⊢
  dsimp only at ht ⊢
  split
  · rfl
  · rename_i he
    simp only [he, ite_false, Stored] at ht
    rw [buildKidsWith_replay small f g hf _ _ _ ht.2.2]

theorem branchWith_slots_replay (small : Store) (f g : Bytes → List (List Nat) → PTrie)
    (hf : ∀ root keys, Stored small (f root keys) → g root keys = f root keys)
    (h : Bytes) (v v' : Option Slot) (rest : Bytes) (keys : List (List Nat)) (mem : Nat)
    (hv : OptSlotStored small v → v' = v)
    (ht : Stored small (branchWith f h v rest keys mem)) :
    branchWith g h v' rest keys mem = branchWith f h v rest keys mem := by
  unfold branchWith at ht ⊢
  dsimp only at ht ⊢
  split
  · rfl
  · rename_i he
    simp only [he, ite_false, Stored] at ht
    rw [hv ht.2.1, buildKidsWith_replay small f g hf _ _ _ ht.2.2]

/-- Restricting a native store while retaining all revealed preimages exactly replays its builder. -/
theorem buildFor_replay {small : Store} {ws : List Bytes}
    (hs : StoreSubset small (mkStore ws)) :
    ∀ fuel root keys, Stored small (buildFor (mkStore ws) fuel root keys) →
      buildFor small fuel root keys = buildFor (mkStore ws) fuel root keys := by
  intro fuel
  induction fuel with
  | zero => intro root keys ht; rfl
  | succ f ih =>
    intro root keys ht
    cases hh : storeGet small root with
    | none =>
      have hroot := built_hashOf_all ws (f+1) root keys
      have hn : storeGet small (buildFor (mkStore ws) (f+1) root keys).hashOf = none := by
        rw [hroot]; exact hh
      have he := stored_lookup_none _ ht hn
      rw [hroot] at he
      rw [he]
      simp [buildFor, hh]
    | some node =>
      have hl := hs root node hh
      simp only [buildFor, hh, hl] at ht ⊢
      split
      · rfl
      · rename_i hk
        simp only [hk, ite_false] at ht
        split
        · rfl
        · rename_i hn
          simp only [hn, ite_false] at ht
          try dsimp only at ht ⊢
          split
          · rename_i rest hb
            simp only [hb] at ht
            split
            · rename_i k hp
              simp only [hp] at ht
              split
              · rfl
              · rename_i hv
                simp only [hv, ite_false, Stored] at ht
                rw [mkSlot_replay hs _ _ _ ht.2]
            · rfl
          · rename_i rest hb
            simp only [hb] at ht
            split
            · rename_i k hp
              simp only [hp] at ht
              split
              · rfl
              · rename_i hv
                simp only [hv, ite_false, Stored] at ht
                rw [ih _ _ ht.2]
            · rfl
          · rename_i rest hb
            simp only [hb] at ht
            exact branchWith_replay small _ _ ih _ _ _ _ _ ht
          · rename_i rest hb
            simp only [hb] at ht
            split
            · rfl
            · rename_i hv
              simp only [hv, ite_false] at ht
              apply branchWith_slots_replay small _ _ ih _ _ _ _ _ _ _ ht
              intro hslot
              exact congrArg some (mkSlot_replay hs _ _ _ hslot)
          · rfl

/-- Exact native replay for the same keys, including missing/malformed queried blobs.
No read-determinacy, SHA injectivity, A6, or budget premise is needed. -/
theorem partialTrie_normalStore (ws : List Bytes) (root : Bytes)
    (keys : List (List Nat)) (hr : root.length = 32) :
    partialTrie (normalStore (partialTrie ws root keys)) root keys =
      partialTrie ws root keys := by
  have ht := (built_spec ws trieFuel root keys hr).2.2.1
  exact buildFor_replay (fun _ _ h => normalStore_lookup_sub ht h) trieFuel root keys
    (normalStore_stored ht)

end ZkFormal.NearV3.Assembly

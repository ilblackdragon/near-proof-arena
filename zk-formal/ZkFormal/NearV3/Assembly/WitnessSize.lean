import ZkFormal.NearV3.Assembly.CodecSize
import ZkFormal.NearV3.Assembly.StoreNormal

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem concatAll_size {α : Type} (enc : α → Bytes) (xs : List α) :
    (concatAll (xs.map enc)).length = (xs.map fun x => (enc x).length).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, concatAll, List.length_append, List.sum_cons] at *; omega

theorem encList_storeCost (ws : List Bytes) :
    (encList borshBytes ws).length = storeCost ws := by
  simp only [encList, List.length_append, concatAll_size, storeCost]
  have he : (fun x : Bytes => (borshBytes x).length) = entryCost := by
    funext x
    simp [borshBytes, entryCost, u32, leN]
    omega
  rw [he]
  simp [u32, leN]

/-- Replacing a transition's store by a cheaper vector cannot enlarge its encoding. -/
theorem encodeTransition_size_mono {a b : Transition}
    (hb : a.blockHash.length ≤ b.blockHash.length)
    (hp : a.postStateRoot.length ≤ b.postStateRoot.length)
    (hv : storeCost a.values ≤ storeCost b.values) :
    (V3.encodeTransition a).length ≤ (V3.encodeTransition b).length := by
  simp only [V3.encodeTransition, ReexecV3D0.encTr, List.length_append,
    encList_storeCost]
  omega

/-- Pointwise relation retaining every list position and the exact list length. -/
inductive Aligned {α : Type} (r : α → α → Prop) : List α → List α → Prop
  | nil : Aligned r [] []
  | cons {a b xs ys} : r a b → Aligned r xs ys → Aligned r (a :: xs) (b :: ys)

theorem encList_size_mono {α : Type} (enc : α → Bytes) {xs ys : List α}
    (h : Aligned (fun a b => (enc a).length ≤ (enc b).length) xs ys) :
    (encList enc xs).length ≤ (encList enc ys).length := by
  have hs : (xs.map fun x => (enc x).length).sum ≤ (ys.map fun y => (enc y).length).sum := by
    induction h with
    | nil => simp
    | cons h _ ih => simp only [List.map_cons, List.sum_cons]; omega
  simp only [encList, List.length_append, concatAll_size, u32, leN,
    List.length_cons, List.length_nil]
  omega

/-- Whole-witness size preservation composes individual store costs with actual decoding. -/
theorem decodeStateWitness_replace_stores_size {raw : Bytes} {s : StateWitness}
    (hd : decodeStateWitness raw = .ok s) (main : Transition) (implicit : List Transition)
    (hm : main.blockHash.length ≤ s.main.blockHash.length ∧
      main.postStateRoot.length ≤ s.main.postStateRoot.length ∧
      storeCost main.values ≤ storeCost s.main.values)
    (hi : Aligned (fun a b => a.blockHash.length ≤ b.blockHash.length ∧
      a.postStateRoot.length ≤ b.postStateRoot.length ∧
      storeCost a.values ≤ storeCost b.values) implicit s.implicit) :
    (V3.encodeSW {s with main := main, implicit := implicit}).length ≤ raw.length := by
  have hm' := encodeTransition_size_mono hm.1 hm.2.1 hm.2.2
  have hi' : Aligned (fun a b => (V3.encodeTransition a).length ≤
      (V3.encodeTransition b).length) implicit s.implicit := by
    generalize he : s.implicit = original at hi ⊢
    clear he
    induction hi with
    | nil => exact .nil
    | cons h _ ih => exact .cons (encodeTransition_size_mono h.1 h.2.1 h.2.2) ih
  have hi'' := encList_size_mono V3.encodeTransition hi'
  have hd' := decodeStateWitness_encodeSW_size hd
  simp only [V3.encodeSW, List.length_append] at *
  omega

/-- Computational store replacement; semantic replay equivalence is a separate obligation. -/
def compactTransition (t : Transition) (root : Bytes) (keys : List (List Nat)) : Transition :=
  {t with values := normalStore (partialTrie t.values root keys)}

theorem compactTransition_cost (t : Transition) (root : Bytes) (keys : List (List Nat))
    (hr : root.length = 32) :
    storeCost (compactTransition t root keys).values ≤ storeCost t.values :=
  partialTrie_normalStore_cost t.values root keys hr

/-- An executable per-transition reconstruction preserves the original whole-witness cap. -/
theorem decodeStateWitness_compact_size {raw : Bytes} {s : StateWitness}
    (hd : decodeStateWitness raw = .ok s) (root : Transition → Bytes)
    (keys : Transition → List (List Nat))
    (hr : ∀ t, (root t).length = 32) :
    (V3.encodeSW {s with
      main := compactTransition s.main (root s.main) (keys s.main),
      implicit := s.implicit.map (fun t => compactTransition t (root t) (keys t))}).length
      ≤ raw.length := by
  apply decodeStateWitness_replace_stores_size hd
  · exact ⟨Nat.le_refl _, Nat.le_refl _, compactTransition_cost _ _ _ (hr _)⟩
  · generalize he : s.implicit = ts
    clear he
    induction ts with
    | nil => exact .nil
    | cons t ts ih =>
      exact .cons ⟨Nat.le_refl _, Nat.le_refl _, compactTransition_cost _ _ _ (hr _)⟩ ih

end ZkFormal.NearV3.Assembly

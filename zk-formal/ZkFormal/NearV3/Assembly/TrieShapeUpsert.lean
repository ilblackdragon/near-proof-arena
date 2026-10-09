import ZkFormal.NearV3.Assembly.TrieShape

namespace ZkFormal.NearV3.Assembly
open NearSpec

theorem shape_newLeaf {k : List Nat} (hk : nibblesOk k=true) (v : Bytes) : TrieShape (newLeaf k v) := hk

theorem shape_wrapExt {k : List Nat} {t : PTrie} (hk : nibblesOk k=true) (ht : TrieShape t) :
    TrieShape (wrapExt k t) := by
  cases k with
  | nil => exact ht
  | cons _ _ => exact ⟨hk,ht⟩

theorem shape_kidsFrom (n i : Nat) (f : Nat → Option PTrie)
    (h : ∀ j c, f j=some c → TrieShape c) : KidsShape (kidsFrom n i f) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
    simp only [kidsFrom]
    cases hf : f i with
    | none => exact ih (i+1)
    | some c => exact ⟨h i c hf,ih (i+1)⟩

theorem shape_kids1 (i : Nat) {c : PTrie} (hc : TrieShape c) : KidsShape (kids1 i c) := by
  apply shape_kidsFrom
  intro j t ht
  split at ht
  · cases ht; exact hc
  · contradiction

theorem shape_kids2 (i j : Nat) {c d : PTrie} (hc : TrieShape c) (hd : TrieShape d) :
    KidsShape (kids2 i c j d) := by
  apply shape_kidsFrom
  intro k t ht
  split at ht
  · cases ht; exact hc
  · split at ht
    · cases ht; exact hd
    · contradiction

theorem shape_splitLeaf (k key : List Nat) (s : Slot) (v : Bytes)
    (hk : nibblesOk k=true) (hkey : nibblesOk key=true) : TrieShape (splitLeaf k s key v) := by
  have hp : nibblesOk (commonPrefix k key)=true := by
    have he := commonPrefix_left k key
    rw [he,nibblesOk_append] at hk
    exact hk.1
  have hks := nibblesOk_drop (commonPrefix k key).length hk
  have hvs := nibblesOk_drop (commonPrefix k key).length hkey
  unfold splitLeaf
  dsimp only
  cases ha : k.drop (commonPrefix k key).length with
  | nil =>
    cases hb : key.drop (commonPrefix k key).length with
    | nil => exact shape_newLeaf hkey v
    | cons y ys =>
      rw [hb,nibblesOk_cons] at hvs
      apply shape_wrapExt hp
      exact shape_kids1 y (shape_newLeaf hvs.2 v)
  | cons x xs =>
    rw [ha,nibblesOk_cons] at hks
    cases hb : key.drop (commonPrefix k key).length with
    | nil =>
      apply shape_wrapExt hp
      exact shape_kids1 x (c := .leaf xs s (leafMem xs s.len)) hks.2
    | cons y ys =>
      rw [hb,nibblesOk_cons] at hvs
      apply shape_wrapExt hp
      exact shape_kids2 x y (c := .leaf xs s (leafMem xs s.len)) hks.2 (shape_newLeaf hvs.2 v)

def shapeExtTail (xs : List Nat) (c : PTrie) (m : Nat) : PTrie :=
  match xs with | [] => c | _::_ => .ext xs c m

theorem shape_splitExt (k key : List Nat) (c : PTrie) (m : Nat) (v : Bytes)
    (hk : nibblesOk k=true) (hkey : nibblesOk key=true) (hc : TrieShape c) :
    TrieShape (splitExt k c m key v) := by
  have hp : nibblesOk (commonPrefix k key)=true := by
    have he := commonPrefix_left k key
    rw [he,nibblesOk_append] at hk
    exact hk.1
  have hks := nibblesOk_drop (commonPrefix k key).length hk
  have hvs := nibblesOk_drop (commonPrefix k key).length hkey
  unfold splitExt
  dsimp only
  cases ha : k.drop (commonPrefix k key).length with
  | nil => exact ⟨hk,hc⟩
  | cons x xs =>
    rw [ha,nibblesOk_cons] at hks
    have hsub : TrieShape (shapeExtTail xs c (extOwnMem xs+(m-extOwnMem k))) := by
      cases xs with
      | nil => exact hc
      | cons _ _ => exact ⟨hks.2,hc⟩
    cases hb : key.drop (commonPrefix k key).length with
    | nil =>
      apply shape_wrapExt hp
      exact shape_kids1 x hsub
    | cons y ys =>
      rw [hb,nibblesOk_cons] at hvs
      apply shape_wrapExt hp
      exact shape_kids2 x y hsub (shape_newLeaf hvs.2 v)

mutual
/-- Native upserts preserve lookup structure even when memory totals overflow u64. -/
theorem shape_upsert : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    TrieShape t → nibblesOk key=true → t.upsert key v=some t' → TrieShape t'
  | .hash _,_,_,_,_,_,h => by simp [PTrie.upsert] at h
  | .leaf k s m,key,v,t',hw,hk,h => by
    simp only [PTrie.upsert] at h
    by_cases he : k=key
    · simp only [he,ite_true,Option.some.injEq] at h
      subst t'
      exact shape_newLeaf hk v
    · simp only [he,ite_false,Option.some.injEq] at h
      subst t'
      exact shape_splitLeaf k key s v hw hk
  | .ext k c m,key,v,t',hw,hk,h => by
    simp only [PTrie.upsert] at h
    by_cases hp : isPrefix k key=true
    · simp only [hp,ite_true] at h
      cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm,hu] at h
      subst t'
      exact ⟨hw.1,shape_upsert c _ v _ hw.2 (nibblesOk_drop _ hk) hu⟩
    · simp only [hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst t'
      exact shape_splitExt k key c m v hw.1 hk hw.2
  | .branch bv cs m,[],v,t',hw,_,h => by
    simp only [PTrie.upsert,Option.some.injEq] at h
    subst t'
    exact hw
  | .branch bv cs m,n::key,v,t',hw,hk,h => by
    simp only [PTrie.upsert] at h
    cases hu : Kids.upsert cs n key v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu,Option.map_some,Option.some.injEq] at h
      subst t'
      exact shape_kids_upsert cs n key v r.1 r.2.1 r.2.2 hw (nibblesOk_cons.mp hk).2 hu

theorem shape_kids_upsert : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (cs' : Kids) (a b : Nat),
    KidsShape cs → nibblesOk key=true → Kids.upsert cs n key v=some (cs',a,b) → KidsShape cs'
  | .nil,_,_,_,_,_,_,_,_,h => by simp [Kids.upsert] at h
  | .none cs,0,key,v,cs',a,b,hw,hk,h => by
    simp only [Kids.upsert,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,_,_⟩ := h
    exact ⟨shape_newLeaf hk v,hw⟩
  | .some c cs,0,key,v,cs',a,b,hw,hk,h => by
    simp only [Kids.upsert] at h
    cases hm : c.mem? <;> cases hu : c.upsert key v <;> simp [hm,hu] at h
    obtain ⟨rfl,_,_⟩ := h
    exact ⟨shape_upsert c key v _ hw.1 hk hu,hw.2⟩
  | .none cs,n+1,key,v,cs',a,b,hw,hk,h => by
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert cs n key v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,_⟩ := h
      exact shape_kids_upsert cs n key v r.1 r.2.1 r.2.2 hw hk hu
  | .some c cs,n+1,key,v,cs',a,b,hw,hk,h => by
    simp only [Kids.upsert] at h
    cases hu : Kids.upsert cs n key v with
    | none => simp [hu] at h
    | some r =>
      simp only [hu,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,_⟩ := h
      exact ⟨hw.1,shape_kids_upsert cs n key v r.1 r.2.1 r.2.2 hw.2 hk hu⟩
end

end ZkFormal.NearV3.Assembly

import NearSpecV3.Logged.LazyTrie

/-!
# The lazy trie operations compute the eager ones

For every operation `opL` of `LazyTrie`: running it on the store `hGet s` gives the eager
operation's result on `t.force s` (`*_spec`), and `hashOfL` is `hashOf ∘ force` on a store whose keys
are the SHA-256 of their values (`hashOfL_spec`).
-/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

def decAt (s : HStore) (h : Bytes) : Option RNode :=
  match hGet s h with
  | none => none
  | some n => dec n

theorem revealAll_succ' (s : HStore) (f : Nat) (h : Bytes) :
    revealAll s (f + 1) h = match decAt s h with
      | none => .hash h
      | some r => buildR s (revealAll s f) r := by
  rw [revealAll_succ, decAt]; cases hGet s h <;> rfl

@[simp] theorem run_getDec (s : HStore) (h : Bytes) : SM.run (hGet s) (getDec h) = .ok (decAt s h) := by
  simp only [getDec, decAt, SM.bind_eq, SM.get', SM.run_bind]
  simp only [SM.run_get, SM.run_ok]
  cases hGet s h <;> rfl

theorem kidsL_force (s : HStore) (f : Nat) : ∀ hs, (kidsL f hs).force s = revealKids (revealAll s f) hs
  | [] => rfl
  | none :: more => by simp only [kidsL, LK.force, revealKids, kidsL_force s f more]
  | some c :: more => by simp only [kidsL, LK.force, LT.force, revealKids, kidsL_force s f more]

theorem toLT_force (s : HStore) (f : Nat) (r : RNode) : (toLT f r).force s = buildR s (revealAll s f) r := by
  cases r with
  | leaf k len vh mem => rfl
  | ext k c mem => rfl
  | branch v hs mem =>
    simp only [toLT, LT.force, buildR, kidsL_force]
    cases v <;> rfl

theorem slotGetL_spec (s : HStore) (v : Slot) : SM.run (hGet s) (slotGetL v) = .ok (fSlot s v).get := by
  cases v with
  | val v => rfl
  | ref len vh =>
    simp only [slotGetL, fSlot, hSlot, hGet, SM.bind_eq, SM.get', SM.run_bind, SM.run_get, SM.run_ok]
    cases s.get? vh with
    | none => rfl
    | some w =>
      simp only [Except.bind]
      by_cases h : (w.length == len) = true <;> simp [h, Slot.get]

theorem findL_spec (s : HStore) :
    (∀ (t : LT) (key : List Nat), SM.run (hGet s) (findL t key) = .ok ((t.force s).find key)) ∧
    (∀ (cs : LK) (n : Nat) (key : List Nat), SM.run (hGet s) (findLK cs n key) = .ok (Kids.find (cs.force s) n key)) := by
  apply findL.mutual_induct
    (motive1 := fun t key => SM.run (hGet s) (findL t key) = .ok ((t.force s).find key))
    (motive2 := fun cs n key => SM.run (hGet s) (findLK cs n key) = .ok (Kids.find (cs.force s) n key))
  · intro h key; rw [findL]; simp [LT.force, revealAll_zero, PTrie.find]
  · intro h f key ih
    rw [findL]
    simp only [SM.bind_eq, SM.run_bind, run_getDec, LT.force, revealAll_succ']
    cases hd : decAt s h with
    | none => rfl
    | some r => simp only [Except.bind]; rw [ih r, toLT_force]
  · intro v mem key
    rw [findL]
    simp only [ite_eq_left, SM.bind_eq, SM.run_bind, slotGetL_spec, LT.force, PTrie.find]
    simp [Except.bind]
  · intro k v mem key hk
    rw [findL]; simp [hk, LT.force, PTrie.find]
  · intro k c mem key hk ih
    rw [findL]; simp only [hk, ite_true, ih, LT.force, PTrie.find]
  · intro k c mem key hk
    rw [findL]; simp [hk, LT.force, PTrie.find]
  · intro cs mem; rw [findL]; rfl
  · intro cs mem v
    rw [findL]
    simp only [SM.bind_eq, SM.run_bind, slotGetL_spec, LT.force, PTrie.find, Option.map_some]
    rfl
  · intro v cs mem n rest ih
    rw [findL]; simp only [ih, LT.force, PTrie.find]
  · intro n key; rw [findLK]; rfl
  · intro r key; rw [findLK]; rfl
  · intro c r key ih; rw [findLK]; simp only [ih, LK.force, Kids.find]
  · intro r i key ih; rw [findLK]; simp only [ih, LK.force, Kids.find]
  · intro c r i key ih; rw [findLK]; simp only [ih, LK.force, Kids.find]


theorem hSlot_len (s : HStore) (len : Nat) (vh : Bytes) : (hSlot s len vh).len = len := by
  unfold hSlot
  split
  · split
    · rename_i v _ hl; simp at hl; simp [Slot.len, hl]
    · rfl
  · rfl

@[simp] theorem fSlot_len (s : HStore) (v : Slot) : (fSlot s v).len = v.len := by
  cases v with
  | val v => rfl
  | ref len vh => exact hSlot_len s len vh

theorem findRefL_spec (s : HStore) :
    (∀ (t : LT) (key : List Nat),
      SM.run (hGet s) (findRefL t key) = .ok (((t.force s).findRef key).map (·.map Slot.len))) ∧
    (∀ (cs : LK) (n : Nat) (key : List Nat),
      SM.run (hGet s) (findRefLK cs n key) = .ok ((Kids.findRef (cs.force s) n key).map (·.map Slot.len))) := by
  apply findRefL.mutual_induct
    (motive1 := fun t key => SM.run (hGet s) (findRefL t key) = .ok (((t.force s).findRef key).map (·.map Slot.len)))
    (motive2 := fun cs n key =>
      SM.run (hGet s) (findRefLK cs n key) = .ok ((Kids.findRef (cs.force s) n key).map (·.map Slot.len)))
  · intro h key; rw [findRefL]; simp [LT.force, revealAll_zero, PTrie.findRef]
  · intro h f key ih
    rw [findRefL]
    simp only [SM.bind_eq, SM.run_bind, run_getDec, LT.force, revealAll_succ']
    cases hd : decAt s h with
    | none => rfl
    | some r => simp only [Except.bind]; rw [ih r, toLT_force]
  · intro k v mem key
    rw [findRefL]
    by_cases hk : k = key
    · simp [hk, LT.force, PTrie.findRef]
    · simp [hk, LT.force, PTrie.findRef]
  · intro k c mem key hk ih
    rw [findRefL]; simp only [hk, ite_true, ih, LT.force, PTrie.findRef]
  · intro k c mem key hk
    rw [findRefL]; simp [hk, LT.force, PTrie.findRef]
  · intro v cs mem
    rw [findRefL]; cases v <;> simp [LT.force, PTrie.findRef]
  · intro v cs mem n rest ih
    rw [findRefL]; simp only [ih, LT.force, PTrie.findRef]
  · intro n key; rw [findRefLK]; rfl
  · intro r key; rw [findRefLK]; rfl
  · intro c r key ih; rw [findRefLK]; simp only [ih, LK.force, Kids.findRef]
  · intro r i key ih; rw [findRefLK]; simp only [ih, LK.force, Kids.findRef]
  · intro c r i key ih; rw [findRefLK]; simp only [ih, LK.force, Kids.findRef]


theorem slotHasL_spec (s : HStore) (v : Slot) :
    SM.run (hGet s) (slotHasL v) = .ok (match fSlot s v with | .val _ => true | .ref _ _ => false) := by
  simp only [slotHasL, SM.bind_eq, SM.run_bind, slotGetL_spec]
  cases fSlot s v <;> rfl

theorem allKeysL_spec (s : HStore) :
    (∀ (t : LT) (acc : List Nat), SM.run (hGet s) (allKeysL t acc) = .ok ((t.force s).allKeys acc)) ∧
    (∀ (cs : LK) (i : Nat) (acc : List Nat),
      SM.run (hGet s) (allKeysLK cs i acc) = .ok (Kids.allKeys (cs.force s) i acc)) := by
  apply allKeysL.mutual_induct
    (motive1 := fun t acc => SM.run (hGet s) (allKeysL t acc) = .ok ((t.force s).allKeys acc))
    (motive2 := fun cs i acc => SM.run (hGet s) (allKeysLK cs i acc) = .ok (Kids.allKeys (cs.force s) i acc))
  · intro h acc; rw [allKeysL]; simp [LT.force, revealAll_zero, PTrie.allKeys]
  · intro h f acc ih
    rw [allKeysL]
    simp only [SM.bind_eq, SM.run_bind, run_getDec, LT.force, revealAll_succ']
    cases hd : decAt s h with
    | none => rfl
    | some r => simp only [Except.bind]; rw [ih r, toLT_force]
  · intro k v mem acc
    rw [allKeysL]
    simp only [SM.bind_eq, SM.run_bind, slotHasL_spec, LT.force, PTrie.allKeys]
    cases fSlot s v <;> rfl
  · intro k c mem acc ih
    rw [allKeysL]; simp only [ih, LT.force, PTrie.allKeys]
  · intro cs mem acc ih
    rw [allKeysL]
    simp only [SM.pure_eq, SM.bind_eq, SM.ok_bind, SM.run_bind, ih, LT.force, LK.force, PTrie.allKeys,
      Option.map_none]
    cases Kids.allKeys (cs.force s) 0 acc <;> rfl
  · intro cs mem acc v ih
    rw [allKeysL]
    simp only [SM.pure_eq, SM.bind_eq, SM.run_bind, slotHasL_spec, LT.force, PTrie.allKeys, Option.map_some]
    cases fSlot s v with
    | val w =>
      simp only [Except.bind, ite_true, SM.ok_bind, SM.run_bind, SM.run_ok, ih]
      cases Kids.allKeys (cs.force s) 0 acc <;> rfl
    | ref len vh => rfl
  · intro i acc; rw [allKeysLK]; rfl
  · intro r i acc ih; rw [allKeysLK]; simp only [ih, LK.force, Kids.allKeys]
  · intro c r i acc ih1 ih2
    rw [allKeysLK]
    simp only [SM.bind_eq, SM.run_bind, ih1, LK.force, Kids.allKeys]
    cases (c.force s).allKeys (acc ++ [i]) with
    | none => rfl
    | some a =>
      simp only [Except.bind, SM.run_bind, ih2]
      cases Kids.allKeys (r.force s) (i + 1) acc <;> rfl
theorem prefixKeysL_spec (s : HStore) :
    (∀ (t : LT) (pre acc : List Nat),
      SM.run (hGet s) (prefixKeysL t pre acc) = .ok ((t.force s).prefixKeys pre acc)) ∧
    (∀ (cs : LK) (n : Nat) (rest acc : List Nat),
      SM.run (hGet s) (prefixKeysLK cs n rest acc) = .ok (Kids.prefixKeys (cs.force s) n rest acc)) := by
  apply prefixKeysL.mutual_induct
    (motive1 := fun t pre acc => SM.run (hGet s) (prefixKeysL t pre acc) = .ok ((t.force s).prefixKeys pre acc))
    (motive2 := fun cs n rest acc =>
      SM.run (hGet s) (prefixKeysLK cs n rest acc) = .ok (Kids.prefixKeys (cs.force s) n rest acc))
  · intro h pre acc; rw [prefixKeysL]; simp [LT.force, revealAll_zero, PTrie.prefixKeys]
  · intro h f pre acc ih
    rw [prefixKeysL]
    simp only [SM.bind_eq, SM.run_bind, run_getDec, LT.force, revealAll_succ']
    cases hd : decAt s h with
    | none => rfl
    | some r => simp only [Except.bind]; rw [ih r, toLT_force]
  all_goals intros
  all_goals first
    | (rw [prefixKeysLK]; simp_all [LK.force, Kids.prefixKeys]; done)
    | (rw [prefixKeysL]; simp_all [LT.force, PTrie.prefixKeys, (allKeysL_spec s).1]; done)
end NearSpecV3.Logged

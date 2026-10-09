import ReexecV3D3.Logged.LazyTrieSpec
import NearSpecV3.D2.State

/-!
# Lazy `upsert` / `del` / `finalize` compute the eager ones

`upsertL_spec`, `delL_spec`: on the store `hGet s`, the lazy operations return (after forcing)
the eager results on `t.force s`, with the node's own `memory_usage`; results are never `lz`.
`applyChangesL_spec`, `preTrieL_spec` and `hashOfL_spec` assemble `Ovl.finalize`.
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2


def NotLz : LT → Prop
  | .lz _ _ => False
  | _ => True

theorem memDL_force (s : HStore) : ∀ (t : LT), NotLz t → memDL t = (t.force s).memD
  | .lz _ _, h => absurd h id
  | .leaf .., _ => rfl
  | .ext .., _ => rfl
  | .branch .., _ => rfl

theorem kidsFromL_force (s : HStore) : ∀ (n i : Nat) (f : Nat → Option LT),
    (kidsFromL n i f).force s = kidsFrom n i (fun j => (f j).map (·.force s))
  | 0, _, _ => rfl
  | n + 1, i, f => by
    simp only [kidsFromL, kidsFrom]
    cases f i <;> simp [LK.force, kidsFromL_force s n (i + 1) f]

theorem kids1L_force (s : HStore) (x : Nat) (c : LT) : (kids1L x c).force s = kids1 x (c.force s) := by
  simp only [kids1L, kids1, kidsFromL_force]; congr; funext i; split <;> rfl

theorem kids2L_force (s : HStore) (x : Nat) (c : LT) (y : Nat) (d : LT) :
    (kids2L x c y d).force s = kids2 x (c.force s) y (d.force s) := by
  simp only [kids2L, kids2, kidsFromL_force]; congr; funext i; split <;> (try split) <;> rfl

theorem wrapExtL_force (s : HStore) (p : List Nat) (b : LT) (hb : NotLz b) :
    (wrapExtL p b).force s = wrapExt p (b.force s) := by
  cases p with
  | nil => rfl
  | cons x xs => simp only [wrapExtL, wrapExt, LT.force, memDL_force s b hb]

@[simp] theorem fSlot_val (s : HStore) (v : Bytes) : fSlot s (.val v) = .val v := rfl

theorem wrapExtL_branch (s : HStore) (p : List Nat) (v : Option Slot) (cs : LK) (m : Nat) :
    (wrapExtL p (.branch v cs m)).force s = wrapExt p ((LT.branch v cs m).force s) :=
  wrapExtL_force s p _ trivial

theorem splitLeafL_force (s : HStore) (k : List Nat) (sl : Slot) (key : List Nat) (v : Bytes) :
    (splitLeafL k sl key v).force s = splitLeaf k (fSlot s sl) key v := by
  simp only [splitLeafL, splitLeaf]
  split <;> rename_i h1 h2 <;> simp only [h1, h2] <;>
    simp only [wrapExtL_branch, LT.force, kids1L_force, kids2L_force, fSlot_len,
      newLeafL, newLeaf, fSlot_val, Option.map_some, Option.map_none]

theorem splitExtL_force (s : HStore) (k : List Nat) (c : LT) (m : Nat) (key : List Nat) (v : Bytes) :
    (splitExtL k c m key v).force s = splitExt k (c.force s) m key v := by
  simp only [splitExtL, splitExt]
  split
  · rename_i h1; simp only [h1]; rfl
  · rename_i x xs h1
    simp only [h1]
    split <;> rename_i h2 <;> simp only [h2] <;>
    cases xs <;> simp only [wrapExtL_branch, LT.force, kids1L_force, kids2L_force,
      newLeafL, newLeaf, fSlot_val, Option.map_some, Option.map_none]

theorem splitLeafL_notLz (k : List Nat) (sl : Slot) (key : List Nat) (v : Bytes) : NotLz (splitLeafL k sl key v) := by
  simp only [splitLeafL]; split <;> simp only [wrapExtL, newLeafL] <;> first | trivial | (split <;> trivial)

theorem splitExtL_notLz (k : List Nat) (c : LT) (m : Nat) (key : List Nat) (v : Bytes) :
    NotLz (splitExtL k c m key v) := by
  simp only [splitExtL]; split
  · trivial
  · split <;> simp only [wrapExtL] <;> first | trivial | (split <;> trivial)


theorem upsert_mem (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie) (h : t.upsert key v = some t') :
    t.mem? = some t.memD := by
  cases t with
  | hash h0 => simp [PTrie.upsert] at h
  | leaf k0 v0 m0 => rfl
  | ext k0 c0 m0 => rfl
  | branch v0 c0 m0 => rfl

@[simp] theorem memD_leaf (k : List Nat) (v : Slot) (m : Nat) : (PTrie.leaf k v m).memD = m := rfl
@[simp] theorem memD_ext (k : List Nat) (c : PTrie) (m : Nat) : (PTrie.ext k c m).memD = m := rfl
@[simp] theorem memD_branch (v : Option Slot) (cs : Kids) (m : Nat) : (PTrie.branch v cs m).memD = m := rfl

def UpRel (s : HStore) (t : LT) (key : List Nat) (v : Bytes) (o : Option (Nat × LT)) : Prop :=
  o.map (fun p => (p.1, p.2.force s)) = ((t.force s).upsert key v).map (fun t' => ((t.force s).memD, t')) ∧
  ∀ p, o = some p → NotLz p.2

def UpRelK (s : HStore) (cs : LK) (n : Nat) (key : List Nat) (v : Bytes) (o : Option (LK × Nat × Nat)) : Prop :=
  o.map (fun p => (p.1.force s, p.2)) = Kids.upsert (cs.force s) n key v

theorem force_lz_succ (s : HStore) (h : Bytes) (f : Nat) (r : RNode) (hd : decAt s h = some r) :
    (LT.lz h (f + 1)).force s = (toLT f r).force s := by
  simp only [LT.force, revealAll_succ', hd, toLT_force]

theorem force_lz_none (s : HStore) (h : Bytes) (f : Nat) (hd : decAt s h = none) :
    (LT.lz h (f + 1)).force s = .hash h := by
  simp only [LT.force, revealAll_succ', hd]

theorem upsertL_spec (s : HStore) :
    (∀ (t : LT) (key : List Nat) (v : Bytes), ∃ o, SM.run (hGet s) (upsertL t key v) = .ok o ∧ UpRel s t key v o) ∧
    (∀ (cs : LK) (n : Nat) (key : List Nat) (v : Bytes),
      ∃ o, SM.run (hGet s) (upsertLK cs n key v) = .ok o ∧ UpRelK s cs n key v o) := by
  apply upsertL.mutual_induct
    (motive1 := fun t key v => ∃ o, SM.run (hGet s) (upsertL t key v) = .ok o ∧ UpRel s t key v o)
    (motive2 := fun cs n key v => ∃ o, SM.run (hGet s) (upsertLK cs n key v) = .ok o ∧ UpRelK s cs n key v o)
  · intro h key v
    refine ⟨none, by rw [upsertL]; rfl, ?_, ?_⟩
    · simp [LT.force, revealAll_zero, PTrie.upsert]
    · intro p hp; cases hp
  · intro h f key v ih
    rw [upsertL]
    simp only [SM.bind_eq, SM.run_bind, run_getDec]
    cases hd : decAt s h with
    | none =>
      refine ⟨none, rfl, ?_, ?_⟩
      · simp [force_lz_none s h f hd, PTrie.upsert]
      · intro p hp; cases hp
    | some r =>
      obtain ⟨o, ho, hr⟩ := ih r
      refine ⟨o, by simpa [Except.bind] using ho, ?_⟩
      unfold UpRel at hr ⊢; rw [force_lz_succ s h f r hd]; exact hr
  · intro k sl m key v
    refine ⟨some (m, if k = key then newLeafL k v else splitLeafL k sl key v), by rw [upsertL]; rfl, ?_, ?_⟩
    · by_cases hk : k = key
      · simp [hk, LT.force, PTrie.upsert, PTrie.memD, PTrie.mem?, newLeafL, newLeaf]
      · simp [hk, LT.force, PTrie.upsert, PTrie.memD, PTrie.mem?, splitLeafL_force]
    · intro p hp
      cases hp
      by_cases hk : k = key
      · simp [hk, newLeafL, NotLz]
      · simp only [hk, ite_false]; exact splitLeafL_notLz _ _ _ _
  · intro k c m key v hk ih
    obtain ⟨o, ho, hr1, hr2⟩ := ih
    rw [upsertL]
    simp only [hk, ite_true, SM.bind_eq, SM.run_bind, ho, Except.bind]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_, ?_⟩
      · simp only [Option.map_none] at hr1
        have : (c.force s).upsert (key.drop k.length) v = none := by
          cases hh : (c.force s).upsert (key.drop k.length) v with
          | none => rfl
          | some _ => rw [hh] at hr1; simp at hr1
        simp [LT.force, PTrie.upsert, hk, this]
      · intro p hp; cases hp
    | some p =>
      obtain ⟨cm, c'⟩ := p
      refine ⟨some (m, .ext k c' (m + memDL c' - cm)), rfl, ?_, ?_⟩
      · simp only [Option.map_some] at hr1
        cases hh : (c.force s).upsert (key.drop k.length) v with
        | none => rw [hh] at hr1; simp at hr1
        | some ct =>
          rw [hh] at hr1
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
          obtain ⟨h1, h2⟩ := hr1
          have hm := upsert_mem _ _ _ _ hh
          subst h2 h1
          simp only [LT.force, PTrie.upsert, hk, ite_true, hm, hh, Option.map_some, memD_ext,
            memDL_force s c' (hr2 _ rfl)]
      · intro p hp; cases hp; trivial
  · intro k c m key v hk
    refine ⟨some (m, splitExtL k c m key v), by rw [upsertL]; simp [hk], ?_, ?_⟩
    · simp [LT.force, PTrie.upsert, hk, splitExtL_force, PTrie.memD, PTrie.mem?]
    · intro p hp; cases hp; exact splitExtL_notLz _ _ _ _ _
  · intro bv cs m v
    refine ⟨some (m, .branch (some (.val v)) cs
      (m + valueMem v.length - (match bv with | some s => valueMem s.len | none => 0))), by
        rw [upsertL.eq_def]; rfl, ?_, ?_⟩
    · cases bv <;> simp [LT.force, PTrie.upsert]
    · intro p hp; cases hp; trivial
  · intro bv cs m n rest v ih
    obtain ⟨o, ho, hr⟩ := ih
    rw [upsertL]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    unfold UpRelK at hr
    cases o with
    | none =>
      refine ⟨none, rfl, ?_, ?_⟩
      · simp only [Option.map_none] at hr
        simp [LT.force, PTrie.upsert, ← hr]
      · intro p hp; cases hp
    | some p =>
      obtain ⟨cs', a, b⟩ := p
      refine ⟨some (m, .branch bv cs' (m + b - a)), rfl, ?_, ?_⟩
      · simp only [Option.map_some] at hr
        simp [LT.force, PTrie.upsert, ← hr]
      · intro p hp; cases hp; trivial
  · intro n key v; exact ⟨none, by rw [upsertLK]; rfl, by simp [UpRelK, LK.force, Kids.upsert]⟩
  · intro r key v
    exact ⟨_, by rw [upsertLK]; rfl, by simp [UpRelK, LK.force, LT.force, Kids.upsert, newLeafL, newLeaf]⟩
  · intro c r key v ih
    obtain ⟨o, ho, hr1, hr2⟩ := ih
    rw [upsertLK]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_⟩
      simp only [Option.map_none] at hr1
      have : (c.force s).upsert key v = none := by
        cases hh : (c.force s).upsert key v with
        | none => rfl
        | some _ => rw [hh] at hr1; simp at hr1
      simp [UpRelK, LK.force, Kids.upsert, this]
    | some p =>
      obtain ⟨cm, c'⟩ := p
      refine ⟨_, rfl, ?_⟩
      simp only [Option.map_some] at hr1
      cases hh : (c.force s).upsert key v with
      | none => rw [hh] at hr1; simp at hr1
      | some ct =>
        rw [hh] at hr1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
        obtain ⟨h1, h2⟩ := hr1
        have hm := upsert_mem _ _ _ _ hh
        subst h2 h1
        simp [UpRelK, LK.force, Kids.upsert, hm, hh, memDL_force s c' (hr2 _ rfl)]
  · intro r i key v ih
    obtain ⟨o, ho, hr⟩ := ih
    rw [upsertLK]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    unfold UpRelK at hr
    cases o with
    | none => exact ⟨none, rfl, by simp [UpRelK, LK.force, Kids.upsert, ← hr]⟩
    | some p => exact ⟨_, rfl, by simp [UpRelK, LK.force, Kids.upsert, ← hr]⟩
  · intro c r i key v ih
    obtain ⟨o, ho, hr⟩ := ih
    rw [upsertLK]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    unfold UpRelK at hr
    cases o with
    | none => exact ⟨none, rfl, by simp [UpRelK, LK.force, Kids.upsert, ← hr]⟩
    | some p => exact ⟨_, rfl, by simp [UpRelK, LK.force, Kids.upsert, ← hr]⟩


theorem presentL_force (s : HStore) : ∀ (cs : LK) (i : Nat),
    (presentL cs i).map (fun p => (p.1, p.2.force s)) = Kids.present (cs.force s) i
  | .nil, _ => rfl
  | .none r, i => by simp only [presentL, LK.force, Kids.present]; exact presentL_force s r (i + 1)
  | .some c r, i => by
    simp only [presentL, LK.force, Kids.present, List.map_cons]; rw [presentL_force s r (i + 1)]

def OptNotLz : Option (Option LT) → Prop
  | some (some c) => NotLz c
  | _ => True

theorem extendChildP_force (s : HStore) (k : List Nat) (t : LT) (ht : NotLz t) :
    (extendChildP k t).map (Option.map (·.force s)) = extendChild k (t.force s) ∧ OptNotLz (extendChildP k t) := by
  cases t with
  | lz _ _ => exact absurd ht id
  | leaf k2 sl m => exact ⟨by simp [extendChildP, extendChild, LT.force], trivial⟩
  | ext k2 c m => exact ⟨by simp [extendChildP, extendChild, LT.force], trivial⟩
  | branch v cs m => exact ⟨by simp [extendChildP, extendChild, LT.force], trivial⟩

theorem toLT_notLz (f : Nat) (r : RNode) : NotLz (toLT f r) := by cases r <;> trivial

theorem extendChildL_spec (s : HStore) (k : List Nat) (t : LT) :
    ∃ o, SM.run (hGet s) (extendChildL k t) = .ok o ∧
      o.map (Option.map (·.force s)) = extendChild k (t.force s) ∧ OptNotLz o := by
  cases t with
  | lz h f =>
    cases f with
    | zero => exact ⟨none, by rw [extendChildL]; rfl, by simp [LT.force, revealAll_zero, extendChild], trivial⟩
    | succ f =>
      cases hd : decAt s h with
      | none =>
        refine ⟨none, ?_, by simp [force_lz_none s h f hd, extendChild], trivial⟩
        rw [extendChildL]; simp [hd]; rfl
      | some r =>
        refine ⟨extendChildP k (toLT f r), ?_, ?_⟩
        · rw [extendChildL]; simp [hd]; rfl
        · rw [force_lz_succ s h f r hd]; exact extendChildP_force s k _ (toLT_notLz f r)
  | leaf k2 sl m =>
    exact ⟨_, by unfold extendChildL; rfl, extendChildP_force s k (.leaf k2 sl m) trivial⟩
  | ext k2 c m =>
    exact ⟨_, by unfold extendChildL; rfl, extendChildP_force s k (.ext k2 c m) trivial⟩
  | branch v cs m =>
    exact ⟨_, by unfold extendChildL; rfl, extendChildP_force s k (.branch v cs m) trivial⟩

theorem squashBranchL_spec (s : HStore) (v : Option Slot) (cs : LK) (m : Nat) :
    ∃ o, SM.run (hGet s) (squashBranchL v cs m) = .ok o ∧
      o.map (Option.map (·.force s)) = squashBranch (v.map (fSlot s)) (cs.force s) m ∧ OptNotLz o := by
  have hp := presentL_force s cs 0
  unfold squashBranchL squashBranch
  rw [← hp]
  generalize presentL cs 0 = ps
  match ps, v with
  | [], none => exact ⟨some none, rfl, rfl, trivial⟩
  | [], some sl => exact ⟨_, rfl, by simp [LT.force, fSlot_len], trivial⟩
  | [(i, c)], none =>
    obtain ⟨o, ho, h1, h2⟩ := extendChildL_spec s [i] c
    exact ⟨o, ho, h1, h2⟩
  | [(i, c)], some sl => exact ⟨_, rfl, by simp [LT.force], trivial⟩
  | _ :: _ :: _, v => exact ⟨_, rfl, by cases v <;> simp [LT.force], trivial⟩

theorem del_mem (t : PTrie) (key : List Nat) (x : Bool × Option PTrie) (h : t.del key = some x) :
    t.mem? = some t.memD := by
  cases t with
  | hash h0 => simp [PTrie.del] at h
  | leaf k0 v0 m0 => rfl
  | ext k0 c0 m0 => rfl
  | branch v0 c0 m0 => rfl

def DelRel (s : HStore) (t : LT) (key : List Nat) (o : Option (Nat × Bool × Option LT)) : Prop :=
  o.map (fun p => (p.1, p.2.1, p.2.2.map (·.force s))) =
    ((t.force s).del key).map (fun p => ((t.force s).memD, p.1, p.2)) ∧
  ∀ m d c, o = some (m, d, some c) → NotLz c

def DelRelK (s : HStore) (cs : LK) (n : Nat) (key : List Nat) (o : Option (Option (LK × Nat × Nat))) : Prop :=
  o.map (Option.map fun p => (p.1.force s, p.2)) = Kids.delAt (cs.force s) n key


theorem del_none_of {t : PTrie} {key : List Nat} {f : Bool × Option PTrie → Nat × Bool × Option PTrie}
    (h : none = (t.del key).map f) : t.del key = none := by
  cases hh : t.del key with
  | none => rfl
  | some _ => rw [hh] at h; simp at h

theorem delL_spec (s : HStore) :
    (∀ (t : LT) (key : List Nat), ∃ o, SM.run (hGet s) (delL t key) = .ok o ∧ DelRel s t key o) ∧
    (∀ (cs : LK) (n : Nat) (key : List Nat),
      ∃ o, SM.run (hGet s) (delAtLK cs n key) = .ok o ∧ DelRelK s cs n key o) := by
  apply delL.mutual_induct
    (motive1 := fun t key => ∃ o, SM.run (hGet s) (delL t key) = .ok o ∧ DelRel s t key o)
    (motive2 := fun cs n key => ∃ o, SM.run (hGet s) (delAtLK cs n key) = .ok o ∧ DelRelK s cs n key o)
  · intro h key
    refine ⟨none, by rw [delL]; rfl, by simp [LT.force, revealAll_zero, PTrie.del], ?_⟩
    intro m d c hc; cases hc
  · intro h f key ih
    rw [delL]
    simp only [SM.bind_eq, SM.run_bind, run_getDec]
    cases hd : decAt s h with
    | none =>
      refine ⟨none, rfl, by simp [force_lz_none s h f hd, PTrie.del], ?_⟩
      intro m d c hc; cases hc
    | some r =>
      obtain ⟨o, ho, hr⟩ := ih r
      refine ⟨o, by simpa [Except.bind] using ho, ?_⟩
      unfold DelRel at hr ⊢; rw [force_lz_succ s h f r hd]; exact hr
  · intro k v mem key
    refine ⟨some (mem, if k = key then (true, none) else (false, some (.leaf k v mem))), by rw [delL]; rfl, ?_, ?_⟩
    · by_cases hk : k = key <;> simp [hk, LT.force, PTrie.del]
    · intro m d c hc
      by_cases hk : k = key <;> simp [hk] at hc
      obtain ⟨_, _, rfl⟩ := hc; trivial
  · intro k c mem key hk ih
    obtain ⟨o, ho, hr1, hr2⟩ := ih
    rw [delL]
    simp only [hk, ite_true, SM.bind_eq, SM.run_bind, ho, Except.bind]
    match o, hr1, hr2 with
    | none, hr1, _ =>
      refine ⟨none, rfl, ?_, ?_⟩
      · simp only [Option.map_none] at hr1
        simp [LT.force, PTrie.del, hk, del_none_of hr1]
      · intro m d c hc; cases hc
    | some (cm, true, none), hr1, _ =>
      refine ⟨some (mem, true, none), rfl, ?_, ?_⟩
      · cases hh : (c.force s).del (key.drop k.length) with
        | none => rw [hh] at hr1; simp at hr1
        | some x =>
          rw [hh] at hr1
          obtain ⟨d', x'⟩ := x
          simp only [Option.map_some, Option.map_none, Option.some.injEq, Prod.mk.injEq] at hr1
          obtain ⟨_, h1, h2⟩ := hr1
          subst h1 h2
          simp [LT.force, PTrie.del, hk, hh, del_mem _ _ _ hh]
      · intro m d c hc; cases hc
    | some (cm, true, some c'), hr1, hr2 =>
      obtain ⟨o2, ho2, h21, h22⟩ := extendChildL_spec s k c'
      simp only [SM.run_bind, ho2, Except.bind]
      cases hh : (c.force s).del (key.drop k.length) with
      | none => rw [hh] at hr1; simp at hr1
      | some x =>
        rw [hh] at hr1
        obtain ⟨d', x'⟩ := x
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
        obtain ⟨_, h1, h2⟩ := hr1
        subst h1 h2
        cases o2 with
        | none =>
          refine ⟨none, rfl, ?_, ?_⟩
          · simp only [Option.map_none] at h21
            simp [LT.force, PTrie.del, hk, hh, del_mem _ _ _ hh, ← h21]
          · intro m d c hc; cases hc
        | some r =>
          refine ⟨some (mem, true, r), rfl, ?_, ?_⟩
          · simp only [Option.map_some] at h21
            simp [LT.force, PTrie.del, hk, hh, del_mem _ _ _ hh, ← h21]
          · intro m d c hc; cases hc; exact h22
    | some (cm, false, x), hr1, _ =>
      refine ⟨some (mem, false, some (.ext k c mem)), rfl, ?_, ?_⟩
      · cases hh : (c.force s).del (key.drop k.length) with
        | none => rw [hh] at hr1; simp at hr1
        | some y =>
          rw [hh] at hr1
          obtain ⟨d', y'⟩ := y
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
          obtain ⟨_, h1, _⟩ := hr1
          subst h1
          simp [LT.force, PTrie.del, hk, hh, del_mem _ _ _ hh]
      · intro m d c hc; cases hc; trivial
  · intro k c mem key hk
    refine ⟨some (mem, false, some (.ext k c mem)), by rw [delL]; simp [hk], ?_, ?_⟩
    · simp [LT.force, PTrie.del, hk]
    · intro m d c hc; cases hc; trivial
  · intro cs mem
    refine ⟨some (mem, false, some (.branch none cs mem)), by rw [delL.eq_def]; rfl, ?_, ?_⟩
    · simp [LT.force, PTrie.del]
    · intro m d c hc; cases hc; trivial
  · intro cs mem sl
    obtain ⟨o2, ho2, h21, h22⟩ := squashBranchL_spec s none cs (mem - valueMem sl.len)
    rw [delL.eq_def]
    simp only [SM.bind_eq, SM.run_bind, ho2, Except.bind]
    cases o2 with
    | none =>
      refine ⟨none, rfl, ?_, ?_⟩
      · simp only [Option.map_none] at h21
        simp [LT.force, PTrie.del, ← h21]
      · intro m d c hc; cases hc
    | some r =>
      refine ⟨some (mem, true, r), rfl, ?_, ?_⟩
      · simp only [Option.map_some, Option.map_none] at h21
        simp [LT.force, PTrie.del, ← h21]
      · intro m d c hc; cases hc; exact h22
  · intro v cs mem n rest ih
    obtain ⟨o, ho, hr⟩ := ih
    rw [delL]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    unfold DelRelK at hr
    match o, hr with
    | none, hr =>
      refine ⟨none, rfl, ?_, ?_⟩
      · simp only [Option.map_none] at hr; simp [LT.force, PTrie.del, ← hr]
      · intro m d c hc; cases hc
    | some none, hr =>
      refine ⟨some (mem, false, some (.branch v cs mem)), rfl, ?_, ?_⟩
      · simp only [Option.map_some, Option.map_none] at hr; simp [LT.force, PTrie.del, ← hr]
      · intro m d c hc; cases hc; trivial
    | some (some (cs', a, b)), hr =>
      obtain ⟨o2, ho2, h21, h22⟩ := squashBranchL_spec s v cs' (mem - a + b)
      simp only [SM.run_bind, ho2, Except.bind]
      simp only [Option.map_some] at hr
      cases o2 with
      | none =>
        refine ⟨none, rfl, ?_, ?_⟩
        · simp only [Option.map_none] at h21; simp [LT.force, PTrie.del, ← hr, ← h21]
        · intro m d c hc; cases hc
      | some r =>
        refine ⟨some (mem, true, r), rfl, ?_, ?_⟩
        · simp only [Option.map_some] at h21; simp [LT.force, PTrie.del, ← hr, ← h21]
        · intro m d c hc; cases hc; exact h22
  · intro n key; exact ⟨some none, by rw [delAtLK]; rfl, by simp [DelRelK, LK.force, Kids.delAt]⟩
  · intro r key; exact ⟨some none, by rw [delAtLK]; rfl, by simp [DelRelK, LK.force, Kids.delAt]⟩
  · intro c r key ih
    obtain ⟨o, ho, hr1, hr2⟩ := ih
    rw [delAtLK]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    match o, hr1, hr2 with
    | none, hr1, _ =>
      refine ⟨none, rfl, ?_⟩
      simp only [Option.map_none] at hr1
      simp [DelRelK, LK.force, Kids.delAt, del_none_of hr1]
    | some (cm, true, c'), hr1, hr2 =>
      refine ⟨_, rfl, ?_⟩
      cases hh : (c.force s).del key with
      | none => rw [hh] at hr1; simp at hr1
      | some x =>
        rw [hh] at hr1
        obtain ⟨d', x'⟩ := x
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
        obtain ⟨h0, h1, h2⟩ := hr1
        subst h0 h1 h2
        cases c' with
        | none => simp [DelRelK, LK.force, Kids.delAt, hh, del_mem _ _ _ hh]
        | some c' =>
          simp [DelRelK, LK.force, Kids.delAt, hh, del_mem _ _ _ hh, memDL_force s c' (hr2 _ _ _ rfl)]
    | some (cm, false, c'), hr1, _ =>
      refine ⟨some none, rfl, ?_⟩
      cases hh : (c.force s).del key with
      | none => rw [hh] at hr1; simp at hr1
      | some x =>
        rw [hh] at hr1
        obtain ⟨d', x'⟩ := x
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
        obtain ⟨_, h1, _⟩ := hr1
        subst h1
        simp [DelRelK, LK.force, Kids.delAt, hh, del_mem _ _ _ hh]
  · intro r i key ih
    obtain ⟨o, ho, hr⟩ := ih
    rw [delAtLK]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    unfold DelRelK at hr
    cases o with
    | none => exact ⟨none, rfl, by simp [DelRelK, LK.force, Kids.delAt, ← hr]⟩
    | some x => exact ⟨_, rfl, by cases x <;> simp [DelRelK, LK.force, Kids.delAt, ← hr]⟩
  · intro c r i key ih
    obtain ⟨o, ho, hr⟩ := ih
    rw [delAtLK]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind]
    unfold DelRelK at hr
    cases o with
    | none => exact ⟨none, rfl, by simp [DelRelK, LK.force, Kids.delAt, ← hr]⟩
    | some x => exact ⟨_, rfl, by cases x <;> simp [DelRelK, LK.force, Kids.delAt, ← hr]⟩


theorem fSlot_valueRef {s : HStore} (hs : HInv s) (v : Slot) : (fSlot s v).valueRef = v.valueRef := by
  cases v with
  | val w => rfl
  | ref len vh => exact hSlot_valueRef hs len vh

mutual
theorem bitmap_spec (s : HStore) : ∀ (cs : LK) (i : Nat), cs.bitmap i = kidsBitmap (cs.force s) i
  | .nil, _ => rfl
  | .none r, i => by simp only [LK.bitmap, LK.force, kidsBitmap]; exact bitmap_spec s r (i + 1)
  | .some _ r, i => by simp only [LK.bitmap, LK.force, kidsBitmap]; rw [bitmap_spec s r (i + 1)]
end

mutual
theorem hashOfL_spec {s : HStore} (hs : HInv s) : ∀ t : LT, t.hashOfL = (t.force s).hashOf
  | .lz h f => (hashOf_revealAll hs f h).symm
  | .leaf k v m => by simp only [LT.hashOfL, LT.force, PTrie.hashOf, fSlot_valueRef hs]
  | .ext k c m => by simp only [LT.hashOfL, LT.force, PTrie.hashOf]; rw [hashOfL_spec hs c]
  | .branch none cs m => by
    simp only [LT.hashOfL, LT.force, Option.map_none, PTrie.hashOf]; rw [hashesL_spec hs cs, bitmap_spec s cs 0]
  | .branch (some v) cs m => by
    simp only [LT.hashOfL, LT.force, Option.map_some, PTrie.hashOf, fSlot_valueRef hs]
    rw [hashesL_spec hs cs, bitmap_spec s cs 0]
theorem hashesL_spec {s : HStore} (hs : HInv s) : ∀ cs : LK, cs.hashesL = Kids.hashes (cs.force s)
  | .nil => rfl
  | .none r => by simp only [LK.hashesL, LK.force, Kids.hashes]; exact hashesL_spec hs r
  | .some c r => by simp only [LK.hashesL, LK.force, Kids.hashes]; rw [hashOfL_spec hs c, hashesL_spec hs r]
end

theorem rootHashL_spec {s : HStore} (hs : HInv s) (t : Option LT) : rootHashL t = rootHash (t.map (·.force s)) := by
  cases t with
  | none => rfl
  | some t => exact hashOfL_spec hs t

theorem applyChangeL_spec (s : HStore) (t : Option LT) (k : Bytes) (v : Option Bytes) :
    ∃ o, SM.run (hGet s) (applyChangeL t k v) = .ok o ∧
      o.map (Option.map (·.force s)) = applyChange (t.map (·.force s)) k v := by
  unfold applyChangeL applyChange
  match v, t with
  | some x, none => exact ⟨_, rfl, by simp [newLeafL, newLeaf, LT.force]⟩
  | some x, some t =>
    obtain ⟨o, ho, hr1, _⟩ := (upsertL_spec s).1 t (nibbles k) x
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind, Option.map_some]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_⟩
      simp only [Option.map_none] at hr1
      cases hh : (t.force s).upsert (nibbles k) x with
      | none => rfl
      | some _ => rw [hh] at hr1; simp at hr1
    | some p =>
      refine ⟨some (some p.2), rfl, ?_⟩
      cases hh : (t.force s).upsert (nibbles k) x with
      | none => rw [hh] at hr1; simp at hr1
      | some t' =>
        rw [hh] at hr1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
        simp [hr1.2]
  | none, none => exact ⟨_, rfl, rfl⟩
  | none, some t =>
    obtain ⟨o, ho, hr1, _⟩ := (delL_spec s).1 t (nibbles k)
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind, Option.map_some]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_⟩
      simp only [Option.map_none] at hr1
      simp [del_none_of hr1]
    | some p =>
      refine ⟨some p.2.2, rfl, ?_⟩
      cases hh : (t.force s).del (nibbles k) with
      | none => rw [hh] at hr1; simp at hr1
      | some x =>
        rw [hh] at hr1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr1
        simp [hr1.2.2]

theorem applyChangesL_spec (s : HStore) : ∀ (t : Option LT) (cs : List (Bytes × Option Bytes)),
    ∃ o, SM.run (hGet s) (applyChangesL t cs) = .ok o ∧
      o.map (Option.map (·.force s)) = applyChanges (t.map (·.force s)) cs
  | t, [] => ⟨some t, rfl, rfl⟩
  | t, (k, v) :: rest => by
    obtain ⟨o, ho, hr⟩ := applyChangeL_spec s t k v
    rw [applyChangesL]
    simp only [SM.bind_eq, SM.run_bind, ho, Except.bind, applyChanges]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_⟩
      simp only [Option.map_none] at hr; rw [← hr]; rfl
    | some t' =>
      obtain ⟨o2, ho2, hr2⟩ := applyChangesL_spec s t' rest
      refine ⟨o2, ho2, ?_⟩
      simp only [Option.map_some] at hr; rw [← hr]; exact hr2

theorem revealAll_hash (s : HStore) : ∀ (f : Nat) (h h' : Bytes), revealAll s f h = .hash h' → h' = h
  | 0, h, h', e => by rw [revealAll_zero] at e; cases e; rfl
  | f + 1, h, h', e => by
    rw [revealAll_succ'] at e
    split at e
    · cases e; rfl
    · rename_i r _; cases r <;> simp [buildR] at e

/-- `Ovl.finalize`'s starting trie for pre-state root `root`. -/
def t0Of (s : HStore) (root : Bytes) : Option PTrie :=
  match revealAll s revealFuel root with
  | .hash h => if h == emptyRoot then none else some (.hash h)
  | t => some t

theorem preTrieL_spec (s : HStore) (root : Bytes) :
    ∃ o, SM.run (hGet s) (preTrieL root) = .ok o ∧ o.map (·.force s) = t0Of s root := by
  unfold preTrieL t0Of
  by_cases he : (root == emptyRoot) = true
  · simp only [he, ite_true, SM.bind_eq, SM.run_bind, run_getDec, Except.bind]
    have hf : revealFuel = 9999 + 1 := rfl
    rw [hf, revealAll_succ']
    cases hd : decAt s root with
    | none => exact ⟨none, rfl, by simp [he]⟩
    | some r =>
      refine ⟨some (toLT 9999 r), rfl, ?_⟩
      simp only [Option.map_some, toLT_force]
      cases r <;> rfl
  · simp only [he, Bool.false_eq_true, ite_false]
    refine ⟨some (.lz root revealFuel), rfl, ?_⟩
    simp only [Option.map_some, LT.force]
    cases hr : revealAll s revealFuel root with
    | hash h' =>
      have := revealAll_hash s _ _ _ hr; subst this
      simp [he]
    | _ => rfl

end ReexecV3D3.Logged

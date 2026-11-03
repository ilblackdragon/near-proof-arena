/-!
# StateM5a.Merkle — the working-set tree: build (`WSN`) and one write access (`WSA`)

`WSN` builds a complete binary tree level by level: node `(ℓ+1, j) = H (ℓ, 2j) (ℓ, 2j+1)`
(`up`), and the depth-`D` root is `root H D leaves`.  A `WSA` row holds a leaf digest, its new
digest and one Merkle path `ps` (side bit, sibling) per level, recomputing the old root and the new
root with the same siblings (`pathRoot`).

`write_access_sound`: if the row's old path reaches the current root and `H` has no collision,
then the row's old leaf *is* leaf `i` of the working set and its new root is the root of the
working set with leaf `i` replaced, for any new leaf.  So the `RCH` chain of write rows walks the
working set from the INTAKE tree to the FINAL tree one leaf at a time.  (`H` is SHA-384 of
`left48 ‖ right48`; a collision of it is the only way around this lemma.)

**M5a-3: a segment's batched update** (`WSL` / `WSP`).  A segment no longer walks one path per
write: it rehashes the union of its touched paths once.  `Upd` describes that union — an
untouched subtree is one digest shared by both trees (`keep h`), a touched leaf has an old and a
new digest (`leaf o n`), a node on a touched path has both children described (`node l r`).
`batch_update_sound`: if the old digest of the description is the working-set root and `H` has
no collision, then every touched leaf's old digest *is* the working set's leaf at its position
(`Agrees`) and the new digest is the root of the working set with exactly the touched leaves
replaced (`apply`).  `root_succ_split` relates the level-by-level root (`WSN`) to the top-down one.
-/

namespace StateM5a.Merkle

variable {α : Type} (H : α → α → α)

/-- One level up: pairs `(2j, 2j+1)`. -/
def up : List α → List α
  | a :: b :: r => H a b :: up r
  | _ => []

/-- Root of a depth-`D` tree. -/
def root : Nat → List α → Option α
  | 0, [x] => some x
  | 0, _ => none
  | D + 1, l => root D (up H l)

/-- A path's root: at each level the current digest is the right child iff the side bit is set. -/
def pathRoot : α → List (Bool × α) → α
  | x, [] => x
  | x, (s, y) :: ps => pathRoot (if s then H y x else H x y) ps

/-- The side bits of a path are the binary digits of the leaf index, least significant first. -/
def sidesOk : Nat → List (Bool × α) → Prop
  | _, [] => True
  | i, (s, _) :: ps => s = (i % 2 == 1) ∧ sidesOk (i / 2) ps

theorem up_length : ∀ l : List α, (up H l).length = l.length / 2
  | [] => by simp [up]
  | [_] => by simp [up]
  | a :: b :: r => by
    simp only [up, List.length_cons, up_length r]; omega

/-- Pair `j` of a list, and the list with its element `i` replaced. -/
theorem up_pair : ∀ (l : List α) (j : Nat) (a b : α), l[2 * j]? = some a → l[2 * j + 1]? = some b →
    (up H l)[j]? = some (H a b)
  | x :: y :: r, 0, a, b, ha, hb => by simp_all [up]
  | x :: y :: r, j + 1, a, b, ha, hb => by
    simp only [up, List.getElem?_cons_succ]
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    have e2 : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
    rw [e1] at ha; rw [e2] at hb
    simp only [List.getElem?_cons_succ] at ha hb
    exact up_pair r j a b ha hb
  | [], _, _, _, ha, _ => by simp at ha
  | [_], 0, _, _, _, hb => by simp at hb
  | [_], _ + 1, _, _, ha, _ => by simp at ha

theorem up_set_even : ∀ (l : List α) (j : Nat) (x y : α), l[2 * j + 1]? = some y →
    up H (l.set (2 * j) x) = (up H l).set j (H x y)
  | a :: b :: r, 0, x, y, hy => by simp_all [up]
  | a :: b :: r, j + 1, x, y, hy => by
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    have e2 : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
    rw [e2] at hy; simp only [List.getElem?_cons_succ] at hy
    rw [e1]
    simp only [List.set_cons_succ, up]
    rw [up_set_even r j x y hy]
  | [], _, _, _, hy => by simp at hy
  | [_], 0, _, _, hy => by simp at hy
  | [_], _ + 1, _, _, hy => by simp at hy

theorem up_set_odd : ∀ (l : List α) (j : Nat) (x y : α), l[2 * j]? = some y →
    l[2 * j + 1]? ≠ none → up H (l.set (2 * j + 1) x) = (up H l).set j (H y x)
  | a :: b :: r, 0, x, y, hy, _ => by simp_all [up]
  | a :: b :: r, j + 1, x, y, hy, hz => by
    have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    have e2 : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
    rw [e1] at hy; simp only [List.getElem?_cons_succ] at hy
    rw [e2] at hz ⊢; simp only [List.getElem?_cons_succ] at hz
    simp only [List.set_cons_succ, up]
    rw [up_set_odd r j x y hy hz]
  | [], _, _, _, hy, _ => by simp at hy
  | [_], 0, _, _, _, hz => by simp at hz
  | [_], _ + 1, _, _, hy, _ => by simp at hy

/-- **One write access.**  With a collision-free `H`, a path whose root is the working-set root
authenticates leaf `i`, and the same path with a new leaf gives the root of the updated set. -/
theorem write_access_sound (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) :
    ∀ (D : Nat) (l : List α) (i : Nat) (x : α) (ps : List (Bool × α)),
      l.length = 2 ^ D → i < 2 ^ D → ps.length = D → sidesOk i ps →
      root H D l = some (pathRoot H x ps) →
      l[i]? = some x ∧ ∀ x', root H D (l.set i x') = some (pathRoot H x' ps)
  | 0, l, i, x, ps, hl, hi, hp, _, hr => by
    match l, ps with
    | [y], [] =>
      have : i = 0 := by simp at hi; omega
      subst this
      simp only [root, pathRoot, Option.some.injEq] at hr
      subst hr
      exact ⟨rfl, fun x' => rfl⟩
    | [], _ => simp at hl
    | _ :: _ :: _, _ => simp at hl
    | [_], _ :: _ => simp at hp
  | D + 1, l, i, x, ps, hl, hi, hp, hs, hr => by
    match ps with
    | [] => simp at hp
    | (s, y) :: ps' =>
      simp only [sidesOk] at hs
      obtain ⟨hs1, hs2⟩ := hs
      simp only [pathRoot] at hr
      simp only [root] at hr
      have hul : (up H l).length = 2 ^ D := by rw [up_length, hl, Nat.pow_succ]; omega
      have hi2 : i / 2 < 2 ^ D := by rw [Nat.pow_succ] at hi; omega
      have hp' : ps'.length = D := by simpa using hp
      obtain ⟨hx1, hupd⟩ := write_access_sound hinj D (up H l) (i / 2) _ ps' hul hi2 hp' hs2 hr
      have hlen : 2 * (i / 2) + 1 < l.length := by rw [hl, Nat.pow_succ]; omega
      obtain ⟨a, ha⟩ : ∃ a, l[2 * (i / 2)]? = some a :=
        ⟨l[2 * (i / 2)]'(by omega), List.getElem?_eq_getElem _⟩
      obtain ⟨b, hb⟩ : ∃ b, l[2 * (i / 2) + 1]? = some b :=
        ⟨l[2 * (i / 2) + 1]'hlen, List.getElem?_eq_getElem _⟩
      have hpair := up_pair H l (i / 2) a b ha hb
      rw [hpair] at hx1
      simp only [Option.some.injEq] at hx1
      by_cases hodd : i % 2 = 1
      · have hsT : s = true := by simp [hs1, hodd]
        subst hsT
        simp only [ite_true] at hx1
        obtain ⟨hay, hbx⟩ := hinj _ _ _ _ hx1
        subst hay; subst hbx
        have hi' : i = 2 * (i / 2) + 1 := by omega
        refine ⟨by rw [hi']; exact hb, fun x' => ?_⟩
        simp only [root, pathRoot, ite_true]
        rw [hi', up_set_odd H l (i / 2) x' a ha (by rw [hb]; simp)]
        exact hupd (H a x')
      · have hsF : s = false := by simp [hs1, hodd]
        subst hsF
        simp only [Bool.false_eq_true, ite_false] at hx1
        obtain ⟨hax, hby⟩ := hinj _ _ _ _ hx1
        subst hax; subst hby
        have hi' : i = 2 * (i / 2) := by omega
        refine ⟨by rw [hi']; exact ha, fun x' => ?_⟩
        simp only [root, pathRoot, Bool.false_eq_true, ite_false]
        rw [hi', up_set_even H l (i / 2) x' b hb]
        exact hupd (H x' b)

/-! ## M5a-3: the batched update of one segment -/

theorem up_take : ∀ (k : Nat) (l : List α), up H (l.take (2 * k)) = (up H l).take k
  | 0, l => by simp [up]
  | k + 1, a :: b :: r => by
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [e]
    simp only [List.take_succ_cons, up, up_take k r]
  | k + 1, [a] => by
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [e]; simp [up]
  | k + 1, [] => by simp [up]

theorem up_drop : ∀ (k : Nat) (l : List α), up H (l.drop (2 * k)) = (up H l).drop k
  | 0, l => by simp
  | k + 1, a :: b :: r => by
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [e]
    simp only [List.drop_succ_cons, up, up_drop k r]
  | k + 1, [a] => by
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [e]; simp [up]
  | k + 1, [] => by simp [up]

/-- The level-by-level root is the hash of the two halves' roots. -/
theorem root_succ_split : ∀ (D : Nat) (l : List α), l.length = 2 ^ (D + 1) →
    root H (D + 1) l =
      (root H D (l.take (2 ^ D))).bind fun a => (root H D (l.drop (2 ^ D))).map fun b => H a b
  | 0, l, hl => by
    match l, hl with
    | [a, b], _ => simp [root, up]
    | [], h => simp at h
    | [_], h => simp at h
    | _ :: _ :: _ :: _, h => simp at h
  | D + 1, l, hl => by
    have hu : (up H l).length = 2 ^ (D + 1) := by rw [up_length, hl, Nat.pow_succ]; omega
    have h1 : root H (D + 1 + 1) l = root H (D + 1) (up H l) := rfl
    rw [h1, root_succ_split D (up H l) hu]
    have e : 2 ^ (D + 1) = 2 * 2 ^ D := by rw [Nat.pow_succ]; omega
    rw [e, ← up_take, ← up_drop]
    rfl

/-- A segment's update of a subtree (the union of its touched paths). -/
inductive Upd (α : Type) where
  /-- an untouched subtree: one digest in the old and the new tree (`WSP`'s `(1 − tl)(lo − ln)`) -/
  | keep (h : α)
  /-- a touched leaf (`WSL`): old and new leaf digest -/
  | leaf (o n : α)
  /-- a node on a touched path (`WSP`) -/
  | node (l r : Upd α)

namespace Upd

/-- Old / new digest of a described subtree (`WSP`'s two compressions). -/
def old : Upd α → α
  | keep h => h
  | leaf o _ => o
  | node l r => H (old l) (old r)

def new : Upd α → α
  | keep h => h
  | leaf _ n => n
  | node l r => H (new l) (new r)

/-- The description fits a depth-`D` subtree (leaves only at depth `0`). -/
def Fits : Nat → Upd α → Prop
  | _, keep _ => True
  | 0, leaf _ _ => True
  | D + 1, node l r => Fits D l ∧ Fits D r
  | _, _ => False

/-- The touched leaves' old digests are the list's leaves at their positions. -/
def Agrees : Nat → Upd α → List α → Prop
  | _, keep _, _ => True
  | 0, leaf o _, l => l = [o]
  | D + 1, node a b, l => Agrees D a (l.take (2 ^ D)) ∧ Agrees D b (l.drop (2 ^ D))
  | _, _, _ => False

/-- The leaf list with every touched leaf replaced by its new digest. -/
def apply : Nat → Upd α → List α → List α
  | _, keep _, l => l
  | 0, leaf _ n, _ => [n]
  | D + 1, node a b, l => apply D a (l.take (2 ^ D)) ++ apply D b (l.drop (2 ^ D))
  | _, _, l => l

theorem apply_length : ∀ (D : Nat) (u : Upd α) (l : List α), Fits D u → l.length = 2 ^ D →
    (apply D u l).length = 2 ^ D
  | _, keep _, l, _, hl => by simp [apply, hl]
  | 0, leaf _ _, _, _, _ => by simp [apply]
  | D + 1, node a b, l, hf, hl => by
    simp only [Fits] at hf
    have e : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
    have h1 : (l.take (2 ^ D)).length = 2 ^ D := by simp [hl, e]
    have h2 : (l.drop (2 ^ D)).length = 2 ^ D := by simp [hl, e]
    simp only [apply, List.length_append, apply_length D a _ hf.1 h1, apply_length D b _ hf.2 h2, e]
  | D + 1, leaf _ _, _, hf, _ => by simp [Fits] at hf
  | 0, node _ _, _, hf, _ => by simp [Fits] at hf

end Upd

/-- **A segment's batched update.**  With a collision-free `H`: if the description's old digest is
the root of the working set `l`, the touched leaves' old digests are `l`'s leaves at their
positions, and its new digest is the root of `l` with exactly the touched leaves replaced. -/
theorem batch_update_sound (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) :
    ∀ (D : Nat) (u : Upd α) (l : List α), u.Fits D → l.length = 2 ^ D →
      root H D l = some (u.old H) → u.Agrees D l ∧ root H D (u.apply D l) = some (u.new H)
  | D, .keep h, l, _, _, hr => by
    refine ⟨by cases D <;> simp [Upd.Agrees], ?_⟩
    cases D <;> simpa [Upd.apply, Upd.old, Upd.new] using hr
  | 0, .leaf o n, l, _, hl, hr => by
    match l, hl with
    | [x], _ =>
      simp only [root, Upd.old, Option.some.injEq] at hr
      subst hr
      exact ⟨rfl, rfl⟩
    | [], h => simp at h
    | _ :: _ :: _, h => simp at h
  | D + 1, .node a b, l, hf, hl, hr => by
    simp only [Upd.Fits] at hf
    have e : 2 ^ (D + 1) = 2 ^ D + 2 ^ D := by rw [Nat.pow_succ]; omega
    have h1 : (l.take (2 ^ D)).length = 2 ^ D := by simp [hl, e]
    have h2 : (l.drop (2 ^ D)).length = 2 ^ D := by simp [hl, e]
    rw [root_succ_split H D l hl] at hr
    cases hx : root H D (l.take (2 ^ D)) with
    | none => simp [hx] at hr
    | some x =>
      cases hy : root H D (l.drop (2 ^ D)) with
      | none => simp [hx, hy] at hr
      | some y =>
        simp only [hx, hy, Option.bind_some, Option.map_some, Option.some.injEq, Upd.old] at hr
        obtain ⟨rfl, rfl⟩ := hinj _ _ _ _ hr
        obtain ⟨ha1, ha2⟩ := batch_update_sound hinj D a _ hf.1 h1 hx
        obtain ⟨hb1, hb2⟩ := batch_update_sound hinj D b _ hf.2 h2 hy
        refine ⟨⟨ha1, hb1⟩, ?_⟩
        have la := Upd.apply_length D a _ hf.1 h1
        have lb := Upd.apply_length D b _ hf.2 h2
        have hlen : (Upd.apply D a (l.take (2 ^ D)) ++ Upd.apply D b (l.drop (2 ^ D))).length =
            2 ^ (D + 1) := by simp [la, lb, e]
        simp only [Upd.apply]
        rw [root_succ_split H D _ hlen, List.take_left' la, List.drop_left' la, ha2, hb2]
        rfl
  | D + 1, .leaf _ _, _, hf, _, _ => by simp [Upd.Fits] at hf
  | 0, .node _ _, _, hf, _, _ => by simp [Upd.Fits] at hf

end StateM5a.Merkle

import StateM5a.Traffic
import StateM5a.Store
import StateM5a.Dsl

/-!
# StateM5a.BusWalk — from row traffic to `rootHash (applyChanges …)`

`Traffic` proves the bus-level facts generically (one row per walk position, the walk induction
`walk_sem`, the root chain `tch_chain`, the version store `ver_recv`).  This file instantiates
them for the batched FINAL of M5a-2:

* **Views.**  A row's old node is a record `R` (ref children) it either received from `VER`
  under its input ref, or hashed: `OldOK σ a R` (`a = vid n` with `σ n = R`, or `a = dig h` with
  `R` all-digest, well-formed, `Shallow` and hashing to `h`).  `in_view`: the expansion `P` of
  `a` reveals to `R` with expanded children (`RecExp`), so any further reveal of that node is a
  reveal of `P` (`Rv`).  Its new node is a record `R'` published under its output ref:
  `NewOK σ b R'` (`b = vid n'` with `σ n' = R'`, or a final node hashed to `b = dig h'`).
  `out_view`: a node whose children are collapses of the expansions of `R'`'s children
  (`RecCl`) is a collapse (`Cl`) of the expansion of `b`.
* **Collapse with written values.**  A written leaf holds `(|x|, sha256 x)` in the circuit and
  `.val x` in the spec: `Cl` is `Rv` (without the reveal side conditions) plus the value-slot
  collapse `.ref |x| (sha256 x) ↦ .val x`; `cl_collapse`: collapsing keeps refinement.
* **Walk semantics** `Sem` (per walk mode: `0` find, `1` upsert, `2` delete), the row-local
  lemmas for the upsert ops `SN.oLR` (`loc_leafRep`), `BR.oUD` (`loc_brDesc`), `SN.oEU`
  (`loc_extDesc`), and the assembly `bus_batched_changes`: from `DOWN`/`UP`/`TCH` balance, the
  walk shape, every row's local step, the `TCH` / root link of the writing `WSB` rows and the
  write log, on any revealed well-formed witness trie with root `prev_state_root`,
  `applyChanges` succeeds and its `rootHash` is `post_state_root`.
-/

namespace StateM5a.BusWalk

open StateM5a NearSpec NearSpecV3.D2 StateM5a.Steps StateM5a.Walk StateM5a.Store StateM5a.Traffic

/-! ## Collapse with written values -/

/-- `Cl x y`: `x` is `y` with revealed subtrees collapsed to their digests and written values
collapsed to their `ValueRef`. -/
inductive Cl : Sum PTrie Kids → Sum PTrie Kids → Prop
  | refl (x : Sum PTrie Kids) : Cl x x
  | stub (h : Bytes) (n n' : PTrie) (hh : n.hashOf = h) (hr : Cl (.inl n) (.inl n')) :
      Cl (.inl (.hash h)) (.inl n')
  | ext (k : List Nat) (c c' : PTrie) (m : Nat) (hr : Cl (.inl c) (.inl c')) :
      Cl (.inl (.ext k c m)) (.inl (.ext k c' m))
  | branch (v : Option Slot) (cs cs' : Kids) (m : Nat) (hr : Cl (.inr cs) (.inr cs')) :
      Cl (.inl (.branch v cs m)) (.inl (.branch v cs' m))
  | knone (r r' : Kids) (hr : Cl (.inr r) (.inr r')) : Cl (.inr (.none r)) (.inr (.none r'))
  | ksome (c c' : PTrie) (r r' : Kids) (hc : Cl (.inl c) (.inl c')) (hr : Cl (.inr r) (.inr r')) :
      Cl (.inr (.some c r)) (.inr (.some c' r'))
  | slot (k : List Nat) (x : Bytes) (m : Nat) :
      Cl (.inl (.leaf k (.ref x.length (sha256 x)) m)) (.inl (.leaf k (.val x) m))

/-- **Collapsing keeps refinement** (no assumption). -/
theorem cl_collapse {x y : Sum PTrie Kids} (h : Cl x y) : ∀ T, RB y T → RB x T := by
  induction h with
  | refl x => intro T hb; exact hb
  | stub h n n' hh hr ih =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      have h1 := ih (.inl T₀) hb
      simp only [RB, PTrie.refinedBy] at h1 ⊢
      rw [← hh]; exact PTrie.hashOf_refinedBy _ _ h1
  | ext k c c' m hr ih =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i k₀ c₀ m₀
      obtain ⟨rfl, rfl, hc⟩ := hb
      have := ih (.inl c₀) hc
      simp only [RB, PTrie.refinedBy, true_and] at this ⊢
      exact this
  | branch v cs cs' m hr ih =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i v₀ cs₀ m₀
      obtain ⟨rfl, hv, hc⟩ := hb
      have := ih (.inr cs₀) hc
      simp only [RB, PTrie.refinedBy, true_and] at this ⊢
      exact ⟨hv, this⟩
  | knone r r' hr ih =>
    intro T hb
    cases T with
    | inl _ => exact hb.elim
    | inr T₀ =>
      cases T₀ <;> simp only [RB, Kids.refinedBy] at hb
      rename_i r₀
      simpa only [RB, Kids.refinedBy] using ih (.inr r₀) hb
  | ksome c c' r r' hc hr ihc ihr =>
    intro T hb
    cases T with
    | inl _ => exact hb.elim
    | inr T₀ =>
      cases T₀ <;> simp only [RB, Kids.refinedBy] at hb
      rename_i c₀ r₀
      have h1 := ihc (.inl c₀) hb.1
      have h2 := ihr (.inr r₀) hb.2
      simp only [RB, Kids.refinedBy] at h1 h2 ⊢
      exact ⟨h1, h2⟩
  | slot k x m =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i k₀ s₀ m₀
      obtain ⟨rfl, rfl, hs⟩ := hb
      simp only [SlotRefines] at hs
      rcases hs with rfl | ⟨v, hv, -⟩
      · simp only [RB, PTrie.refinedBy, true_and, SlotRefines]
        exact Or.inr ⟨x, rfl, rfl⟩
      · cases hv

/-! ## Records as nodes -/

end StateM5a.BusWalk

namespace StateM5a.Store
open NearSpec

def Ref.toP : Ref → PTrie
  | .dig h => .hash h
  | .vid _ => .hash []

def Ref.IsDig : Ref → Prop
  | .dig _ => True
  | .vid _ => False

def RKids.toK : RKids → Kids
  | .nil => .nil
  | .none r => .none r.toK
  | .some c r => .some c.toP r.toK

def RKids.AllDig : RKids → Prop
  | .nil => True
  | .none r => r.AllDig
  | .some c r => c.IsDig ∧ r.AllDig

/-- The node of a record whose children are digests (children as hash stubs). -/
def Rec.toP : Rec → PTrie
  | .leaf k v m => .leaf k v m
  | .ext k c m => .ext k c.toP m
  | .branch v cs m => .branch v cs.toK m

def Rec.AllDig : Rec → Prop
  | .leaf .. => True
  | .ext _ c _ => c.IsDig
  | .branch _ cs _ => cs.AllDig

def RKids.at : RKids → Nat → Option Ref
  | .nil, _ => Option.none
  | .none _, 0 => Option.none
  | .some c _, 0 => Option.some c
  | .none r, i + 1 => RKids.at r i
  | .some _ r, i + 1 => RKids.at r i

def RKids.put : RKids → Nat → Option Ref → RKids
  | .nil, _, _ => .nil
  | .none r, 0, c => match c with | Option.some c => .some c r | Option.none => .none r
  | .some _ r, 0, c => match c with | Option.some c => .some c r | Option.none => .none r
  | .none r, i + 1, c => .none (RKids.put r i c)
  | .some x r, i + 1, c => .some x (RKids.put r i c)

end StateM5a.Store

namespace StateM5a.BusWalk

open StateM5a NearSpec NearSpecV3.D2 StateM5a.Steps StateM5a.Walk StateM5a.Store StateM5a.Traffic

theorem exp_dig {σ : Store} {h : Bytes} {P : PTrie} (e : Exp σ (.inl (.dig h)) (.inl P)) :
    P = .hash h := by cases e; rfl

theorem kexp_toK {σ : Store} : ∀ {cs : RKids}, cs.AllDig → Exp σ (.inr cs) (.inr cs.toK)
  | .nil, _ => .knil
  | .none r, h => .knone _ _ (kexp_toK (cs := r) h)
  | .some (.dig g) r, h => .ksome _ _ _ _ (.dig g) (kexp_toK (cs := r) h.2)
  | .some (.vid _) _, h => h.1.elim

/-- The old node a row sees, as the expansion of its record's children. -/
def RecExp (σ : Store) : Rec → PTrie → Prop
  | .leaf k v m, N => N = .leaf k v m
  | .ext k c m, N => ∃ P, N = .ext k P m ∧ Exp σ (.inl c) (.inl P)
  | .branch v cs m, N => ∃ ks, N = .branch v ks m ∧ Exp σ (.inr cs) (.inr ks)

/-- A row's old record `R` under its input ref `a`: read from the store under a version id, or
hashed (by the row, or by the digest's publisher) to `a`'s digest. -/
def OldOK (σ : Store) (a : Ref) (R : Rec) : Prop :=
  (∃ n, a = .vid n ∧ σ n = some R) ∨
  (∃ h, a = .dig h ∧ R.AllDig ∧ R.toP.wf = true ∧ Shallow R.toP ∧ R.toP.hashOf = h)

theorem recExp_toP {σ : Store} : ∀ {R : Rec}, R.AllDig → RecExp σ R R.toP
  | .leaf .., _ => rfl
  | .ext k (.dig g) m, _ => ⟨_, rfl, .dig g⟩
  | .ext _ (.vid _) _, h => h.elim
  | .branch v cs m, h => ⟨_, rfl, kexp_toK h⟩

theorem toP_not_hash : ∀ (R : Rec) (g : Bytes), R.toP ≠ .hash g
  | .leaf .., _, e => by cases e
  | .ext .., _, e => by cases e
  | .branch .., _, e => by cases e

/-- **The input view.**  The expansion `P` of the row's input ref reveals to its record with
expanded children; revealing that node further is revealing `P`. -/
theorem in_view {σ : Store} {a : Ref} {R : Rec} {P : PTrie} (hR : OldOK σ a R)
    (he : Exp σ (.inl a) (.inl P)) :
    ∃ N, RecExp σ R N ∧ ∀ t, Rv (.inl N) (.inl t) → Rv (.inl P) (.inl t) := by
  rcases hR with ⟨n, rfl, hn⟩ | ⟨h, rfl, hd, hw, hs, hh⟩
  · refine ⟨P, ?_, fun t ht => ht⟩
    cases he with
    | leaf _ k v m hn' => rw [hn] at hn'; cases hn'; rfl
    | ext _ k c m t hn' hc => rw [hn] at hn'; cases hn'; exact ⟨t, rfl, hc⟩
    | branch _ v cs m ks hn' hc => rw [hn] at hn'; cases hn'; exact ⟨ks, rfl, hc⟩
  · rw [exp_dig he]
    exact ⟨R.toP, recExp_toP hd, fun t ht => .stub h R.toP t (toP_not_hash R) hw hs hh ht⟩

/-- Children collapses: each child of the node is a collapse of the expansion of the record's
child ref. -/
inductive KCl (σ : Store) : RKids → Kids → Prop
  | nil : KCl σ .nil .nil
  | none (r : RKids) (ks : Kids) (h : KCl σ r ks) : KCl σ (.none r) (.none ks)
  | some (c : Ref) (r : RKids) (t : PTrie) (ks : Kids) (hc : ∃ P, Exp σ (.inl c) (.inl P) ∧ Cl (.inl P) (.inl t))
      (h : KCl σ r ks) : KCl σ (.some c r) (.some t ks)

def RecCl (σ : Store) : Rec → PTrie → Prop
  | .leaf k v m, N => N = .leaf k v m ∨ ∃ x, v = .ref x.length (sha256 x) ∧ N = .leaf k (.val x) m
  | .ext k c m, N => ∃ t, N = .ext k t m ∧ ∃ P, Exp σ (.inl c) (.inl P) ∧ Cl (.inl P) (.inl t)
  | .branch v cs m, N => ∃ ks, N = .branch v ks m ∧ KCl σ cs ks

/-- A row's new record `R'` under its output ref `b`: published under a version id, or a final
node hashed to `b`'s digest. -/
def NewOK (σ : Store) (b : Ref) (R : Rec) : Prop :=
  (∃ n, b = .vid n ∧ σ n = some R) ∨ (∃ h, b = .dig h ∧ R.AllDig ∧ R.toP.hashOf = h)

theorem kcl_exp {σ : Store} {cs : RKids} {ks : Kids} (h : KCl σ cs ks) :
    ∃ kp, Exp σ (.inr cs) (.inr kp) ∧ Cl (.inr kp) (.inr ks) := by
  induction h with
  | nil => exact ⟨.nil, .knil, .refl _⟩
  | none r ks _ ih =>
    obtain ⟨kp, he, hc⟩ := ih
    exact ⟨.none kp, .knone _ _ he, .knone _ _ hc⟩
  | some c r t ks hc' _ ih =>
    obtain ⟨P, hP, hPc⟩ := hc'
    obtain ⟨kp, he, hc⟩ := ih
    exact ⟨.some P kp, .ksome _ _ _ _ hP he, .ksome _ _ _ _ hPc hc⟩

theorem kcl_toK {σ : Store} {cs : RKids} {ks : Kids} (h : KCl σ cs ks) (hd : cs.AllDig) :
    Cl (.inr cs.toK) (.inr ks) := by
  induction h with
  | nil => exact .refl _
  | none r ks _ ih => exact .knone _ _ (ih hd)
  | some c r t ks hc' _ ih =>
    obtain ⟨P, hP, hPc⟩ := hc'
    cases c with
    | dig g => rw [exp_dig hP] at hPc; exact .ksome _ _ _ _ hPc (ih hd.2)
    | vid _ => exact (hd.1 : False).elim

/-- **The output view.**  A node whose children collapse to the expansions of the published
record's children is a collapse of the expansion of the output ref. -/
theorem out_view {σ : Store} {b : Ref} {R : Rec} {N : PTrie} (hR : NewOK σ b R) (hc : RecCl σ R N) :
    ∃ P', Exp σ (.inl b) (.inl P') ∧ Cl (.inl P') (.inl N) := by
  rcases hR with ⟨n, rfl, hn⟩ | ⟨h, rfl, hd, hh⟩
  · cases R with
    | leaf k v m =>
      refine ⟨.leaf k v m, .leaf n k v m hn, ?_⟩
      rcases hc with rfl | ⟨x, rfl, rfl⟩
      · exact .refl _
      · exact .slot k x m
    | ext k c m =>
      obtain ⟨t, rfl, P, hP, hPc⟩ := hc
      exact ⟨.ext k P m, .ext n k c m P hn hP, .ext _ _ _ _ hPc⟩
    | branch v cs m =>
      obtain ⟨ks, rfl, hk⟩ := hc
      obtain ⟨kp, he, hcl⟩ := kcl_exp hk
      exact ⟨.branch v kp m, .branch n v cs m kp hn he, .branch _ _ _ _ hcl⟩
  · refine ⟨.hash h, .dig h, .stub h R.toP N hh ?_⟩
    cases R with
    | leaf k v m =>
      rcases hc with rfl | ⟨x, rfl, rfl⟩
      · exact .refl _
      · exact .slot k x m
    | ext k c m =>
      obtain ⟨t, rfl, P, hP, hPc⟩ := hc
      cases c with
      | dig g => rw [exp_dig hP] at hPc; exact .ext _ _ _ _ hPc
      | vid _ => exact (hd : False).elim
    | branch v cs m =>
      obtain ⟨ks, rfl, hk⟩ := hc
      exact .branch _ _ _ _ (kcl_toK hk hd)

/-! ## Kids lemmas -/

theorem rv_cl {x y : Sum PTrie Kids} (h : Rv x y) : Cl x y := by
  induction h with
  | refl x => exact .refl x
  | stub h n n' _ _ _ hh _ ih => exact .stub h n n' hh ih
  | ext k c c' m _ ih => exact .ext k c c' m ih
  | branch v cs cs' m _ ih => exact .branch v cs cs' m ih
  | knone r r' _ ih => exact .knone r r' ih
  | ksome c c' r r' _ _ ihc ihr => exact .ksome c c' r r' ihc ihr

theorem kexp_at {σ : Store} : ∀ {rcs : RKids} {ks : Kids} {n : Nat} {c : Ref},
    Exp σ (.inr rcs) (.inr ks) → rcs.at n = some c →
      ∃ P, Kids.at ks n = some P ∧ Exp σ (.inl c) (.inl P)
  | .nil, _, n, _, _, h => by cases n <;> simp [RKids.at] at h
  | .none r, _, 0, _, _, h => by simp [RKids.at] at h
  | .some c' r, _, 0, c, e, h => by
    simp only [RKids.at, Option.some.injEq] at h; subst h
    cases e with
    | ksome _ _ t ks hc _ => exact ⟨t, rfl, hc⟩
  | .none r, _, n + 1, _, e, h => by
    cases e with
    | knone _ ks hr => simp only [RKids.at] at h; simp only [Kids.at]; exact kexp_at hr h
  | .some c' r, _, n + 1, _, e, h => by
    cases e with
    | ksome _ _ t ks _ hr => simp only [RKids.at] at h; simp only [Kids.at]; exact kexp_at hr h

theorem kids_put_at : ∀ {ks : Kids} {n : Nat} {P : PTrie} (t : PTrie), Kids.at ks n = some P →
    Kids.at (Kids.put ks n (some t)) n = some t
  | .nil, n, _, _, h => by cases n <;> simp [Kids.at] at h
  | .none r, 0, _, _, h => by simp [Kids.at] at h
  | .some _ r, 0, _, _, _ => rfl
  | .none r, n + 1, _, t, h => by simp only [Kids.at, Kids.put] at h ⊢; exact kids_put_at t h
  | .some _ r, n + 1, _, t, h => by simp only [Kids.at, Kids.put] at h ⊢; exact kids_put_at t h

theorem kids_put_put : ∀ (ks : Kids) (n : Nat) (x y : Option PTrie),
    Kids.put (Kids.put ks n x) n y = Kids.put ks n y
  | .nil, _, _, _ => rfl
  | .none r, 0, x, y => by cases x <;> cases y <;> rfl
  | .some _ r, 0, x, y => by cases x <;> cases y <;> rfl
  | .none r, n + 1, x, y => by simp only [Kids.put]; rw [kids_put_put r n x y]
  | .some _ r, n + 1, x, y => by simp only [Kids.put]; rw [kids_put_put r n x y]

/-- Revealing one child. -/
theorem rv_kids_put : ∀ {ks : Kids} {n : Nat} {P t : PTrie}, Kids.at ks n = some P →
    Rv (.inl P) (.inl t) → Rv (.inr ks) (.inr (Kids.put ks n (some t)))
  | .nil, n, _, _, h, _ => by cases n <;> simp [Kids.at] at h
  | .none r, 0, _, _, h, _ => by simp [Kids.at] at h
  | .some c r, 0, P, t, h, hr => by
    simp only [Kids.at, Option.some.injEq] at h; subst h
    exact .ksome _ _ _ _ hr (.refl _)
  | .none r, n + 1, _, _, h, hr => by
    simp only [Kids.at] at h; simp only [Kids.put]; exact .knone _ _ (rv_kids_put h hr)
  | .some c r, n + 1, _, _, h, hr => by
    simp only [Kids.at] at h; simp only [Kids.put]; exact .ksome _ _ _ _ (.refl _) (rv_kids_put h hr)

/-- An expansion is a trivial collapse, slot by slot. -/
theorem kcl_of_exp {σ : Store} {rcs : RKids} {ks : Kids} (h : Exp σ (.inr rcs) (.inr ks)) :
    KCl σ rcs ks := by
  generalize ex : (Sum.inr rcs : Sum Ref RKids) = x at h
  generalize ey : (Sum.inr ks : Sum PTrie Kids) = y at h
  induction h generalizing rcs ks with
  | dig => cases ex
  | leaf => cases ex
  | ext => cases ex
  | branch => cases ex
  | knil => cases ex; cases ey; exact .nil
  | knone r ks' _ ih => cases ex; cases ey; exact .none _ _ (ih rfl rfl)
  | ksome c r t ks' hc _ _ ihr =>
    cases ex; cases ey; exact .some _ _ _ _ ⟨t, hc, .refl _⟩ (ihr rfl rfl)

/-- Replacing one child by a collapse of a new ref's expansion. -/
theorem kcl_put {σ : Store} : ∀ {rcs : RKids} {ks : Kids} {n : Nat} {c c' : Ref} {t : PTrie},
    KCl σ rcs ks → rcs.at n = some c → (∃ P, Exp σ (.inl c') (.inl P) ∧ Cl (.inl P) (.inl t)) →
      KCl σ (rcs.put n (some c')) (Kids.put ks n (some t))
  | .nil, _, n, _, _, _, _, h, _ => by cases n <;> simp [RKids.at] at h
  | .none r, _, 0, _, _, _, _, h, _ => by simp [RKids.at] at h
  | .some _ r, _, 0, _, _, _, k, _, hc => by
    cases k with
    | some _ _ _ ks _ hk => exact .some _ _ _ _ hc hk
  | .none r, _, n + 1, _, _, _, k, h, hc => by
    cases k with
    | none _ ks hk => simp only [RKids.at] at h; exact .none _ _ (kcl_put hk h hc)
  | .some _ r, _, n + 1, _, _, _, k, h, hc => by
    cases k with
    | some _ _ t₀ ks h₀ hk => simp only [RKids.at] at h; exact .some _ _ _ _ h₀ (kcl_put hk h hc)

/-! ## The store from `VER` traffic -/

/-- A record hashed to `h` by its publisher (`FieldVer`: a digest publisher hashed its old node,
whose children are digests and whose value slot is a ref). -/
def Hashed (R : Rec) (h : Bytes) : Prop :=
  R.AllDig ∧ R.toP.wf = true ∧ Shallow R.toP ∧ R.toP.hashOf = h

/-- The store of the version-publishing rows: `(id, new record)`. -/
def storeOf (vers : List (Nat × Rec)) : Store := fun n => (vers.find? (·.1 == n)).map (·.2)

theorem storeOf_mem {vers : List (Nat × Rec)} (hnd : (vers.map (·.1)).Nodup) :
    ∀ {n R}, (n, R) ∈ vers → storeOf vers n = some R := by
  induction vers with
  | nil => intro n R h; exact absurd h List.not_mem_nil
  | cons p ps ih =>
    intro n R h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [storeOf, List.find?_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h'
    · simp
    · have hne : p.1 ≠ n := fun e => hnd.1 ⟨(n, R), h', e.symm⟩
      have hb : (p.1 == n) = false := by simp [hne]
      simp only [hb]
      exact ih hnd.2 h'

theorem slot_eq_of_refines {s s' : Slot} (h : SlotRefines s s') (hs' : ∃ len g, s' = .ref len g) :
    s = s' := by
  rcases h with h | ⟨v, -, rfl⟩
  · exact h
  · obtain ⟨_, _, e⟩ := hs'; cases e

theorem kids_eq_of_refinedBy : ∀ {cs cs' : Kids},
    (∀ n c, Kids.at cs' n = some c → ∃ h, c = .hash h) → Kids.refinedBy cs cs' →
    (∀ n c, Kids.at cs n = some c → ∃ h, c = .hash h) → cs = cs'
  | .nil, .nil, _, _, _ => rfl
  | .none r, .none r', h', hr, h => by
    simp only [Kids.refinedBy] at hr
    rw [kids_eq_of_refinedBy (fun n c e => h' (n + 1) c e) hr (fun n c e => h (n + 1) c e)]
  | .some c r, .some c' r', h', hr, h => by
    simp only [Kids.refinedBy] at hr
    obtain ⟨g, rfl⟩ := h 0 c rfl
    obtain ⟨g', rfl⟩ := h' 0 c' rfl
    have hc := hr.1
    simp only [PTrie.refinedBy, PTrie.hashOf] at hc
    rw [hc, kids_eq_of_refinedBy (fun n c e => h' (n + 1) c e) hr.2 (fun n c e => h (n + 1) c e)]
  | .nil, .none _, _, hr, _ | .nil, .some .., _, hr, _ | .none _, .nil, _, hr, _
  | .none _, .some .., _, hr, _ | .some .., .nil, _, hr, _ | .some .., .none _, _, hr, _ => by
    simp [Kids.refinedBy] at hr

/-- Refinement between two row nodes (children stubs, value refs) is equality. -/
theorem shallow_eq {n₁ n₂ : PTrie} (h₁ : Shallow n₁) (h₂ : Shallow n₂) (hr : n₁.refinedBy n₂)
    (hn : ∀ g, n₁ ≠ .hash g) : n₁ = n₂ := by
  cases n₁ with
  | hash g => exact absurd rfl (hn g)
  | leaf k s m =>
    cases n₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    rw [slot_eq_of_refines hs h₂]
  | ext k c m =>
    cases n₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    obtain ⟨g, rfl⟩ := h₁
    obtain ⟨g', rfl⟩ := h₂
    simp only [PTrie.refinedBy, PTrie.hashOf] at hc
    rw [hc]
  | branch v cs m =>
    cases n₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v' cs' m'
    obtain ⟨rfl, hv, hc⟩ := hr
    have : v = v' := by
      cases v with
      | none => cases v' <;> simp [OptSlotRefines] at hv; rfl
      | some s =>
        cases v' with
        | none => simp [OptSlotRefines] at hv
        | some s' =>
          simp only [OptSlotRefines] at hv
          rw [slot_eq_of_refines hv (h₂.1 s' rfl)]
    subst this
    rw [kids_eq_of_refinedBy h₂.2 hc h₁.2]

theorem ref_toP_inj : ∀ {c c' : Ref}, c.IsDig → c'.IsDig → c.toP = c'.toP → c = c'
  | .dig _, .dig _, _, _, e => by simp only [Ref.toP, PTrie.hash.injEq] at e; rw [e]
  | .vid _, _, h, _, _ => h.elim
  | _, .vid _, _, h, _ => h.elim

theorem rkids_toK_inj : ∀ {cs cs' : RKids}, cs.AllDig → cs'.AllDig → cs.toK = cs'.toK → cs = cs'
  | .nil, .nil, _, _, _ => rfl
  | .none r, .none r', h, h', e => by
    simp only [RKids.toK, Kids.none.injEq] at e; rw [rkids_toK_inj (cs := r) (cs' := r') h h' e]
  | .some c r, .some c' r', h, h', e => by
    simp only [RKids.toK, Kids.some.injEq] at e
    rw [ref_toP_inj h.1 h'.1 e.1, rkids_toK_inj (cs := r) (cs' := r') h.2 h'.2 e.2]
  | .nil, .none _, _, _, e | .nil, .some .., _, _, e | .none _, .nil, _, _, e
  | .none _, .some .., _, _, e | .some .., .nil, _, _, e | .some .., .none _, _, _, e => by
    simp [RKids.toK] at e

theorem rec_toP_inj : ∀ {R R' : Rec}, R.AllDig → R'.AllDig → R.toP = R'.toP → R = R'
  | .leaf .., .leaf .., _, _, e => by simp only [Rec.toP, PTrie.leaf.injEq] at e; rw [e.1, e.2.1, e.2.2]
  | .ext k c m, .ext k' c' m', h, h', e => by
    simp only [Rec.toP, PTrie.ext.injEq] at e
    rw [e.1, ref_toP_inj h h' e.2.1, e.2.2]
  | .branch .., .branch .., h, h', e => by
    simp only [Rec.toP, PTrie.branch.injEq] at e
    rw [e.1, rkids_toK_inj h h' e.2.1, e.2.2]
  | .leaf .., .ext .., _, _, e | .leaf .., .branch .., _, _, e | .ext .., .leaf .., _, _, e
  | .ext .., .branch .., _, _, e | .branch .., .leaf .., _, _, e | .branch .., .ext .., _, _, e => by
    simp [Rec.toP] at e

/-- **Digest publishers agree** (collision resistance; `NodeSerInj` is proved). -/
theorem hashed_agree (hCR : Sha256CR) {R R' : Rec} {h : Bytes} (hR : Hashed R h) (hR' : Hashed R' h) :
    R = R' := by
  obtain ⟨hd, hw, hs, hh⟩ := hR
  obtain ⟨hd', hw', hs', hh'⟩ := hR'
  have hr := refinedBy_of_hash hCR StateM5a.SerInj.nodeSerInj hw hw' (toP_not_hash R) (toP_not_hash R')
    hs (hh.trans hh'.symm)
  exact rec_toP_inj hd hd' (shallow_eq hs hs' hr (toP_not_hash R))

/-- **The version store from `VER` balance.**  `vers` are the `(id, new record)` of the rows
that publish a new node under a version id (ids distinct: the id is `ID + 2·rid + 1`, `FieldVer`
`br_vid` / `sn_vid`); `pubs` the `VER` sends (a version id's record is its row's; a digest's
record was hashed to it, `FieldVer` `*_vm_gsha`, `*_gsha_dig`); `recvs` the `VER` receives.  With
`σ = storeOf vers`: every version-publishing row's record is `σ` of its id (`NewOK`'s first case),
and every reader's record is `OldOK` for the ref it reads. -/
theorem ver_store (hCR : Sha256CR) {P : Type} (k : Nat) (hk : 0 < k) (part : Rec → Nat → P)
    (hext : ∀ x y, (∀ i, i < k → part x i = part y i) → x = y)
    {vers : List (Nat × Rec)} (hnd : (vers.map (·.1)).Nodup)
    {pubs recvs : List (Ref × Rec)}
    (hpub : ∀ p ∈ pubs, (∃ n, p.1 = .vid n ∧ (n, p.2) ∈ vers) ∨ (∃ h, p.1 = .dig h ∧ Hashed p.2 h))
    (hbal : (pubs.flatMap (verMsgs k part)).Perm (recvs.flatMap (verMsgs k part))) :
    (∀ n R, (n, R) ∈ vers → storeOf vers n = some R) ∧
    (∀ a R, (a, R) ∈ recvs → OldOK (storeOf vers) a R) := by
  refine ⟨fun n R h => storeOf_mem hnd h, ?_⟩
  have agree : ∀ ref x y, (ref, x) ∈ pubs → (ref, y) ∈ pubs → x = y := by
    intro ref x y hx hy
    rcases hpub _ hx with ⟨n, e, hn⟩ | ⟨h, e, hh⟩ <;>
      rcases hpub _ hy with ⟨n', e', hn'⟩ | ⟨h', e', hh'⟩ <;> simp only at e e' <;> rw [e] at e'
    · cases e'
      have := (storeOf_mem hnd hn).symm.trans (storeOf_mem hnd hn')
      exact Option.some.inj this
    · cases e'
    · cases e'
    · cases e'; exact hashed_agree hCR hh hh'
  intro a R hR
  have hp := ver_recv k hk part hext hbal agree a R hR
  rcases hpub _ hp with ⟨n, e, hn⟩ | ⟨h, e, hh⟩
  · exact Or.inl ⟨n, e, storeOf_mem hnd hn⟩
  · obtain ⟨hd, hw, hs, hhh⟩ := hh
    exact Or.inr ⟨h, e, hd, hw, hs, hhh⟩

/-! ## Walk payloads, results, semantics -/

/-- `DOWN` payload: key id, mode (`0` find, `1` upsert, `2` delete), the written value's
`(length, sha256)`. -/
structure Pay where
  kid : Nat
  mode : Nat
  vlen : Nat
  vh : Bytes

/-- `UP` result: kind, the node's new (or unchanged) ref, new / old memory, a leaf descriptor
(`kid2`, `st2`, value ref) and a find answer (`fpres`, value ref). -/
structure Res where
  rk : Nat
  ref : Ref
  nm : Nat
  om : Nat
  kid2 : Nat
  st2 : Nat
  alen : Nat
  avh : Bytes
  fpres : Nat

/-- Upsert walk below depth `d`: the expansion of the input ref reveals to a trie on which the
rows' upsert chain runs; its result collapses to the expansion of the output ref; the old /
new memories are the result's. -/
def SemU (σ : Store) (K : List Nat) (x : Bytes) (d : Nat) (a : Ref) (res : Res) : Prop :=
  ∀ P, Exp σ (.inl a) (.inl P) → ∃ t₁ t₁' P', Rv (.inl P) (.inl t₁) ∧ UChain t₁ (K.drop d) x t₁' ∧
    Exp σ (.inl res.ref) (.inl P') ∧ Cl (.inl P') (.inl t₁') ∧ t₁.mem? = some res.om ∧ t₁'.memD = res.nm

/-- Result kinds that carry a ref (`H`, `HB`, `HE`, `SAME`). -/
def RefKind (rk : Nat) : Prop := rk = RK_H ∨ rk = RK_HB ∨ rk = RK_HE ∨ rk = RK_SAME

/-- What a delete result says about the subtree left. -/
def DRes (σ : Store) (keyOf : Nat → List Nat) (res : Res) : Option PTrie → Prop
  | none => res.rk = RK_NONE
  | some t' => (RefKind res.rk ∧ ∃ P', Exp σ (.inl res.ref) (.inl P') ∧ Cl (.inl P') (.inl t') ∧
      t'.memD = res.nm) ∨
    (res.rk = RK_LD ∧ ∃ m2, t' = .leaf ((keyOf res.kid2).drop res.st2) (.ref res.alen res.avh) m2)

/-- Delete walk below depth `d`. -/
def SemD (σ : Store) (keyOf : Nat → List Nat) (K : List Nat) (d : Nat) (a : Ref) (res : Res) : Prop :=
  ∀ P, Exp σ (.inl a) (.inl P) → ∃ t₁ b o, Rv (.inl P) (.inl t₁) ∧ DChain t₁ (K.drop d) (b, o) ∧
    t₁.mem? = some res.om ∧ DRes σ keyOf res o

/-- Find walk below depth `d` (INTAKE): the answer is absent (`fpres = 0`) or the value ref. -/
def SemF (σ : Store) (K : List Nat) (d : Nat) (a : Ref) (res : Res) : Prop :=
  ∀ P, Exp σ (.inl a) (.inl P) → ∃ t₁ ans, Rv (.inl P) (.inl t₁) ∧ FChain t₁ (K.drop d) ans ∧
    ((res.fpres = 0 ∧ ans = none) ∨ (res.fpres = 1 ∧ ans = some (.ref res.alen res.avh)))

/-- The walk property of a `DOWN` position, by mode. -/
def Sem (σ : Store) (keyOf : Nat → List Nat) (_w d : Nat) (a : Ref) (pay : Pay) (res : Res) : Prop :=
  match pay.mode with
  | 0 => SemF σ (keyOf pay.kid) d a res
  | 1 => ∀ x : Bytes, pay.vlen = x.length → pay.vh = sha256 x → SemU σ (keyOf pay.kid) x d a res
  | 2 => SemD σ keyOf (keyOf pay.kid) d a res
  | _ => True

/-! ## Row-local steps (upsert) -/

/-- **`SN.oLR`** (leaf replace): the old leaf `k ↦ s` (`k` = the rest of the walk key: nibble
lookups + `KLEN`), the new leaf `k ↦ (|x|, sha256 x)` published under the output ref. -/
theorem step_leafRep {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a : Ref} {res : Res}
    {k : List Nat} {s : Slot} {m : Nat} (hold : OldOK σ a (.leaf k s m)) (hK : K.drop d = k)
    (hnew : NewOK σ res.ref (.leaf k (.ref x.length (sha256 x)) (leafMem k x.length)))
    (hom : res.om = m) (hnm : res.nm = leafMem k x.length) : SemU σ K x d a res := by
  intro P hP
  obtain ⟨N, hN, hrv⟩ := in_view hold hP
  simp only [RecExp] at hN; subst hN
  obtain ⟨P', hP', hcl⟩ := out_view hnew (N := newLeaf k x) (Or.inr ⟨x, rfl, rfl⟩)
  refine ⟨_, _, P', hrv _ (.refl _), hK ▸ UChain.leafRep k s m x, hP', hcl, ?_, ?_⟩
  · simp [PTrie.mem?, hom]
  · simp [newLeaf, PTrie.memD, PTrie.mem?, hnm]

/-- **`BR.oUD`** (branch descend): the old branch's slot `n` (= the walk key's nibble `d`) holds
the child ref sent down; the new branch holds the child's result ref in slot `n`, memory
`m + nm − om`. -/
theorem step_brDesc {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a c : Ref} {res cres : Res}
    {v : Option Slot} {rcs : RKids} {m n : Nat} (hold : OldOK σ a (.branch v rcs m))
    (hat : rcs.at n = some c) (hK : K.drop d = n :: K.drop (d + 1))
    (hnew : NewOK σ res.ref (.branch v (rcs.put n (some cres.ref)) (m + cres.nm - cres.om)))
    (hom : res.om = m) (hnm : res.nm = m + cres.nm - cres.om)
    (hc : SemU σ K x (d + 1) c cres) : SemU σ K x d a res := by
  intro P hP
  obtain ⟨N, ⟨ks, rfl, hks⟩, hrv⟩ := in_view hold hP
  obtain ⟨Pc, hat', hPc⟩ := kexp_at hks hat
  obtain ⟨tc, tc', Pc', hrc, huc, hPc', hclc, hmc, hnc⟩ := hc Pc hPc
  have hput := kids_put_at tc hat'
  refine ⟨.branch v (Kids.put ks n (some tc)) m,
    .branch v (Kids.put (Kids.put ks n (some tc)) n (some tc')) (m + tc'.memD - cres.om), ?_⟩
  obtain ⟨P', hP', hcl⟩ := out_view hnew (N := .branch v (Kids.put (Kids.put ks n (some tc)) n (some tc'))
    (m + tc'.memD - cres.om)) ⟨_, by rw [hnc], by
      rw [kids_put_put]; exact kcl_put (kcl_of_exp hks) hat ⟨Pc', hPc', hclc⟩⟩
  refine ⟨P', hrv _ (.branch _ _ _ _ (rv_kids_put hat' hrc)), ?_, hP', hcl, by simp [PTrie.mem?, hom], ?_⟩
  · rw [hK]; exact UChain.brDesc v _ m n _ tc tc' cres.om x hput hmc huc
  · show m + tc'.memD - cres.om = res.nm
    rw [hnc, hnm]

/-- **`SN.oEU`** (extension descend): the old extension `k` (= the walk key's nibbles
`d … d + |k|`) over the child ref sent down at depth `d + |k|`; the new extension over the
child's result ref, memory `m + nm − om`. -/
theorem step_extDesc {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a c : Ref} {res cres : Res}
    {k : List Nat} {m : Nat} (hold : OldOK σ a (.ext k c m))
    (hK : K.drop d = k ++ K.drop (d + k.length))
    (hnew : NewOK σ res.ref (.ext k cres.ref (m + cres.nm - cres.om)))
    (hom : res.om = m) (hnm : res.nm = m + cres.nm - cres.om)
    (hc : SemU σ K x (d + k.length) c cres) : SemU σ K x d a res := by
  intro P hP
  obtain ⟨N, ⟨Pc, rfl, hPc⟩, hrv⟩ := in_view hold hP
  obtain ⟨tc, tc', Pc', hrc, huc, hPc', hclc, hmc, hnc⟩ := hc Pc hPc
  obtain ⟨P', hP', hcl⟩ := out_view hnew (N := .ext k tc' (m + tc'.memD - cres.om))
    ⟨tc', by rw [hnc], Pc', hPc', hclc⟩
  refine ⟨.ext k tc m, _, P', hrv _ (.ext _ _ _ _ hrc), ?_, hP', hcl, by simp [PTrie.mem?, hom], ?_⟩
  · rw [hK]; exact UChain.extDesc k _ tc tc' m cres.om x hmc huc
  · show m + tc'.memD - cres.om = res.nm
    rw [hnc, hnm]

/-! ## Row-local steps as `LocalOK` -/

/-- An upsert row's local step, from its `SemU` step. -/
theorem localOK_upsert {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1)
    (hstep : match r.dout with
      | none => ∀ x : Bytes, r.din.pay.vlen = x.length → r.din.pay.vh = sha256 x →
          SemU σ (keyOf r.din.pay.kid) x r.din.d r.din.ref r.uout
      | some c => c.pay = r.din.pay ∧ ∀ x : Bytes, r.din.pay.vlen = x.length → r.din.pay.vh = sha256 x →
          SemU σ (keyOf r.din.pay.kid) x c.d c.ref r.uin →
          SemU σ (keyOf r.din.pay.kid) x r.din.d r.din.ref r.uout) :
    LocalOK (Sem σ keyOf) r := by
  unfold LocalOK
  cases hc : r.dout with
  | none =>
    rw [hc] at hstep
    simp only [Sem, hmode]; exact hstep
  | some c =>
    rw [hc] at hstep
    obtain ⟨hp, hs⟩ := hstep
    simp only [Sem, hp, hmode]
    intro hch x h1 h2
    exact hs x h1 h2 (hch x h1 h2)

/-! ## All changes: the induction on the root chain -/

/-- One committed change's rows, on the expansion `P` of the change's input ref: reveal, run the
change's chain, collapse to the expansion of the output ref `a'`. -/
def StepRows (σ : Store) (P : PTrie) (a' : Ref) : Bytes × Option Bytes → Prop
  | (k, some x) => ∃ t₁ t₁' P', Rv (.inl P) (.inl t₁) ∧ UChain t₁ (nibbles k) x t₁' ∧
      Exp σ (.inl a') (.inl P') ∧ Cl (.inl P') (.inl t₁')
  | (k, none) => ∃ t₁ t₁' P' b, Rv (.inl P) (.inl t₁) ∧ DChain t₁ (nibbles k) (b, some t₁') ∧
      Exp σ (.inl a') (.inl P') ∧ Cl (.inl P') (.inl t₁')

/-- **Every change, along the root chain.**  `A j` is the root ref after `j` changes; each
change's rows step from (the expansion of) `A j` to `A (j + 1)`; `A 0` is the digest
`prev_state_root` of the witness trie and the last ref the digest `post`.  Then `applyChanges`
on the witness succeeds with `rootHash = post`.  Premises: `Sha256CR`, `KeepsFW`. -/
theorem chain_changes (hCR : Sha256CR) (hKeep : KeepsFW) (σ : Store) :
    ∀ (cs : List (Bytes × Option Bytes)) (A : Nat → Ref) (P : PTrie) (T : PTrie),
      Exp σ (.inl (A 0)) (.inl P) → P.refinedBy T → Full T ∧ T.wf = true →
      (∀ j (hj : j < cs.length) P, Exp σ (.inl (A j)) (.inl P) → StepRows σ P (A (j + 1)) cs[j]) →
      ∀ post, A cs.length = .dig post →
      ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post
  | [], A, P, T, hP, h0, _, _, post, hn => by
    refine ⟨T, rfl, ?_⟩
    simp only [List.length_nil] at hn
    rw [hn] at hP
    rw [exp_dig hP] at h0
    simpa [PTrie.refinedBy, rootHash] using h0.symm
  | (k, v) :: rest, A, P, T, hP, h0, hF, hrows, post, hn => by
    have hr0 := hrows 0 (by simp) P hP
    simp only [List.getElem_cons_zero] at hr0
    obtain ⟨T₁, P₁, hT₁, hP₁, h1⟩ : ∃ T₁ P₁, stepOf k v T = some T₁ ∧
        Exp σ (.inl (A 1)) (.inl P₁) ∧ P₁.refinedBy T₁ := by
      cases v with
      | some x =>
        obtain ⟨t₁, t₁', P', hr, hc, hP', hcl⟩ := hr0
        have h1 := rv_refinedBy hCR StateM5a.SerInj.nodeSerInj hr (.inl T) h0 hF
        obtain ⟨T', hT', h2⟩ := upsert_step (nibbles k) x t₁ t₁' T hc h1
        exact ⟨T', P', by simp [stepOf, applyChange, hT'], hP', cl_collapse hcl (.inl T') h2⟩
      | none =>
        obtain ⟨t₁, t₁', P', b, hr, hc, hP', hcl⟩ := hr0
        have h1 := rv_refinedBy hCR StateM5a.SerInj.nodeSerInj hr (.inl T) h0 hF
        obtain ⟨T', hT', h2⟩ := del_step k t₁ t₁' T ⟨b, hc⟩ h1
        exact ⟨T', P', hT', hP', cl_collapse hcl (.inl T') h2⟩
    have hA := stepOf_some hT₁
    obtain ⟨T'', h2, h3⟩ := chain_changes hCR hKeep σ rest (fun j => A (j + 1)) P₁ T₁ hP₁ h1
      (hKeep T T₁ k v hF hA)
      (fun j hj P hP => by
        have := hrows (j + 1) (by simp; omega) P hP
        simp only [List.getElem_cons_succ] at this
        exact this) post (by simpa using hn)
    exact ⟨T'', by simp [applyChanges, hA, h2], h3⟩

/-! ## The assembly -/

/-- The walk payload of a committed change: the key, and mode / value by presence. -/
def PayOf (keyOf : Nat → List Nat) (pay : Pay) : Bytes × Option Bytes → Prop
  | (k, some x) => keyOf pay.kid = nibbles k ∧ pay.mode = 1 ∧ pay.vlen = x.length ∧ pay.vh = sha256 x
  | (k, none) => keyOf pay.kid = nibbles k ∧ pay.mode = 2

/-- From a root's walk property to the change's `StepRows`. -/
theorem stepRows_of_sem {σ : Store} {keyOf : Nat → List Nat} {q : Root Ref Pay Res}
    {ch : Bytes × Option Bytes} (hd : q.dn.d = 0) (hpay : PayOf keyOf q.dn.pay ch)
    (hrk : ch.2 = none → RefKind q.res.rk)
    (hs : Sem σ keyOf q.dn.w q.dn.d q.dn.ref q.dn.pay q.res) :
    ∀ P, Exp σ (.inl q.dn.ref) (.inl P) → StepRows σ P q.res.ref ch := by
  intro P hP
  obtain ⟨k, v⟩ := ch
  cases v with
  | some x =>
    obtain ⟨hk, hm, hl, hh⟩ := hpay
    simp only [Sem, hm, hd, hk] at hs
    obtain ⟨t₁, t₁', P', hr, hc, hP', hcl, -⟩ := hs x hl hh P hP
    exact ⟨t₁, t₁', P', hr, by simpa using hc, hP', hcl⟩
  | none =>
    obtain ⟨hk, hm⟩ := hpay
    have hrk := hrk rfl
    simp only [Sem, hm, hd, hk] at hs
    obtain ⟨t₁, b, o, hr, hc, -, hres⟩ := hs P hP
    simp only [List.drop_zero] at hc
    cases o with
    | none =>
      simp only [DRes] at hres
      rcases hrk with h | h | h | h <;> rw [hres] at h <;> simp [RK_NONE, RK_H, RK_HB, RK_HE, RK_SAME] at h
    | some t' =>
      simp only [DRes] at hres
      rcases hres with ⟨-, P', hP', hcl, -⟩ | ⟨h, -⟩
      · exact ⟨t₁, t', P', b, hr, hc, hP', hcl⟩
      · rcases hrk with e | e | e | e <;> rw [h] at e <;> simp [RK_LD, RK_H, RK_HB, RK_HE, RK_SAME] at e

/-- **Batched FINAL from the bus traffic.**  The trie rows and walk roots satisfy the walk
shape and every active row's local step (`LocalOK` for `Sem`); `DOWN` and `UP` balance; the
writing `WSB` rows `j < N` receive `TCH(j, a j)` and send `TCH(j + 1, b j)` against the public
`TCH(0, prev_state_root)` / `TCH(n, post_state_root)` (`TCH` balance); writing row `j` is the
root of change `cs[j]`'s walk (depth `0`, input ref `a j`, result ref `b j`, payload the change's
key / value, a ref result kind for a delete — the `WSB` constraints).  Then on any revealed,
well-formed witness trie with root hash `prev_state_root`, the spec's `applyChanges` succeeds and
its `rootHash` is `post_state_root`.  Premises: `Sha256CR` and `KeepsFW` (`NodeSerInj` is
proved). -/
theorem bus_batched_changes (hCR : Sha256CR) (hKeep : KeepsFW) (σ : Store) (keyOf : Nat → List Nat)
    {roots : List (Root Ref Pay Res)} {rows : List (WRow Ref Pay Res)} (hs : WalkShape roots rows)
    (hD : (downSends roots rows).Perm (downRecvs rows)) (hU : (upSends rows).Perm (upRecvs roots rows))
    (hloc : ∀ r ∈ rows, LocalOK (Sem σ keyOf) r)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ roots, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post := by
  obtain ⟨hN, ha, hpost⟩ := tch_chain hT
  subst hN
  have hsem := walk_sem (Sem σ keyOf) hs hD hU hloc
  refine chain_changes hCR hKeep σ cs (chainAt (Ref.dig prev) b) (.hash prev) T (.dig prev)
    (by simp [PTrie.refinedBy, hT0]) hF ?_ post hpost.symm
  intro j hj P hP
  obtain ⟨q, hq, hqa, hqb, hqd, hpay⟩ := hroot j hj
  obtain ⟨hpay, hrk⟩ := hpay hj
  have := stepRows_of_sem hqd hpay hrk (hsem q hq) P (by rw [hqa, ha j hj]; exact hP)
  rw [hqb] at this
  exact this

end StateM5a.BusWalk

import ZkFormal.NearV3.Link.Post3Occ

/-!
# ZkFormal.NearV3.Link.Post3OccWalk — a `VAL` walk reaches its value record (M6d, `reach_walk`)

`walk3_find` is generic in the value records `V`: its only `V`-dependent hypothesis is the
unfolding equation `hunf`, which holds for **every** `V` (`fullTree_unfold_any`, the unfolding
only uses the record DAG).  Its head is existential, though, so re-applying it for each `V`
could pick different heads of the same instance.  `walk3_val_at` fixes the head: any head `h`
whose `START` edge is the walk's row-0 edge (`StartsAt`); `start_head` gives one, independent
of `V`.

* `unf_any` — the unfolding equation for any `V'`;
* `walk3_val_at` — for a fixed starting head `h` and any `V` with the walk hypotheses,
  `fk = VAL → (fullTree R V h.rid).find key3 = some (some (valOf V (vpos a wv.k)))`;
* **`reach_walk_at`** — `fk = VAL` ⇒ `fullReach R h.rid wv.key3 = some (vpos a wv.k)` and
  `vpos a wv.k < |es|` (apply `walk3_val_at` to `setVal V⁺ i x` for a padded `V⁺` and every
  `x`, then `reach_of_find`; the bound comes from the reached record's value slot);
* `reach_walk` — the same with the head chosen (`∃ h ∈ hs`, `h.tau = wv.tau`, `StartsAt`);
* `find_walk_any` — the `∀ x` form used by `post_eq_set'`.
-/

set_option linter.deprecated false
set_option autoImplicit false

namespace ZkFormal.NearV3

open NearSpec

/-- A reached value id is a value id of some record. -/
theorem reach_vids {ns : List NodeRec3} {j : Nat} : ∀ (f n : Nat) (key : List Nat), vreach3 ns f n key = some j →
    ∃ m : Nat, ∃ nr : NodeRec3, ns[m]? = some nr ∧ j ∈ nr.node.vids := by
  intro f
  induction f with
  | zero => intro n key h; simp [vreach3] at h
  | succ f ih =>
    intro n key h
    simp only [vreach3] at h
    cases hn : ns[n]? with
    | none => rw [hn] at h; simp at h
    | some nr =>
      rw [hn] at h; simp only at h
      generalize hr : nr.node = r at h
      cases r with
      | leaf k s m =>
        cases s with
        | ref => simp [recReach] at h
        | val j' =>
          simp only [recReach] at h; split at h <;> simp at h; subst h
          exact ⟨n, nr, hn, by rw [hr]; simp [Rec3.vids]⟩
      | ext k kid m =>
        cases kid with
        | node c =>
          simp only [recReach] at h; split at h
          · exact ih c _ h
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
            | val j' =>
              simp [recReach] at h; subst h
              exact ⟨n, nr, hn, by rw [hr]; simp [Rec3.vids]⟩
        | cons j0 rest =>
          simp only [recReach] at h
          split at h
          · rename_i c _; exact ih c rest h
          · simp at h

end ZkFormal.NearV3

namespace ZkFormal.NearV3.Walk3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link ZkFormal.NearV3 ZkFormal.NearV3.Link3
open NearSpec

/-- The walk starts at head `h`: its row-0 edge is `h`'s `START` edge. -/
def StartsAt (wv : WalkR) (h : HeadE) : Prop := (wv.step 0).e = [0, h.tau, SYM_START, h.rres, 0, EK_DOWN]

section
variable {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3} {hs : List HeadE} {ws : List WalkR}

/-- `walk3_pos` at a given starting head. -/
theorem walk3_pos_at (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) {h : HeadE} (hh : h ∈ hs)
    (he0 : StartsAt wv h) :
    ∀ i, 1 ≤ i → i < wv.steps.length → (∀ j < i, (wv.step j).mode = 0) →
      Pos f vs V ((fullTree (recsOf f vs) V h.rid).find wv.key3)
        ((wv.step i).e.getD 0 0) ((wv.step i).e.getD 1 0) (restAt wv i) := by
  unfold StartsAt at he0
  have hL := G.walk.len wv hw
  intro i h1 hi hall
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · obtain ⟨s, hs, hres⟩ := G.hd h hh
      have hp := pos_res G.trie hs hres (r := wv.key3) rfl
      have hok0 := row_ok G hw (i := 0) (by omega)
      obtain ⟨e0, e1⟩ := chain_getD hok0.elen (row_ok G hw (i := 1) hi).elen
        ((G.walk.chain wv hw 0 hi).1 (hall 0 (by omega))).1
      rw [e0, e1, he0, restAt_one]; exact hp
    · exact row_step G hw hpos hi (hall i (by omega))
        (ih hpos (by omega) (fun j hj => hall j (by omega)))

/-- **A `VAL` walk at a given starting head.** -/
theorem walk3_val_at (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) {h : HeadE} (hh : h ∈ hs)
    (he0 : StartsAt wv h) (hfk : wv.fk = FK_VAL) :
    (fullTree (recsOf f vs) V h.rid).find wv.key3 = some (some (valOf V (f wv.k))) := by
  have hpos := walk3_pos_at G hw hh he0
  have hL := G.walk.len wv hw
  have hp1 := hpos 1 (Nat.le_refl _) (by omega) (fun j hj => by
    rw [show j = 0 by omega]; exact (G.walk.start wv hw).1)
  have hc := walk3_concl G hw (wv.steps.length - 2) 1 (by omega) (Nat.le_refl _) (G.walk.start wv hw).1 hp1
  revert hfk
  unfold WalkR.fk WalkR.k
  by_cases hm : wv.last.mode = 0
  · simp only [hm, if_true]; exact fun _ => hc.1 hm
  · simp only [hm, if_false]; exact fun h => absurd h (by decide)

/-- The starting head exists and does not depend on `V`. -/
theorem starts_at (G : WalkHyp f vs V hs ws) {wv : WalkR} (hw : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧ StartsAt wv h :=
  start_head G hw

end

end ZkFormal.NearV3.Walk3

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3
open ZkFormal.NearV3.Walk3 (StartsAt)

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

/-- **The unfolding equation for any value records.** -/
theorem unf_any (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256) (V' : List ValRec3) :
    ∀ n (hn : n < vs.length), fullTree (recsOf (vpos (vid0 es)) vs) V' n =
      nodeTree3 V' (fullTree (recsOf (vpos (vid0 es)) vs) V') (vs[n].v.toRec3 (vpos (vid0 es))) := by
  intro n hn
  obtain ⟨h, hh, ht⟩ := head_of hw hhw hb n hn
  have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
  exact fullTree_unfold_any hd V' (recsOf_get _ _ hn) (by simp only; rw [ht])

/-- The walk hypotheses for any value records. -/
theorem walkHyp_any {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START) (V' : List ValRec3) :
    Walk3.WalkHyp (vpos (vid0 es)) vs V' hs ws :=
  { node := hw, head := hhw, walk := hW, balE := hE, balB := hB, rowsP := wrows_lt hW,
    klen := Walk3.klen_of_rows hw, sym := hsym
    trie := Walk3.TrieHyp.of (unf_any hw hhw hvw hb hvb hbytes V') hw.res
      (fun p hp c l r pre po hk => by
        obtain ⟨hc, -, -, hr⟩ := kid_depth hw hhw hb hp hk; exact ⟨hc, hr⟩)
    hd := fun h hh => by
      obtain ⟨hr, -, -, -, he⟩ := head_link hw hhw hb hh
      exact ⟨vs[h.rid], List.getElem?_eq_getElem hr, he⟩ }

/-- Value ids of the records are positions of value records. -/
theorem vids_lt (hw : NodeWf3 vs) (hvw : ValWf es) (hvb : VParentBal vs es) {m j : Nat} {nr : NodeRec3}
    (hm : (recsOf (vpos (vid0 es)) vs)[m]? = some nr) (hj : j ∈ nr.node.vids) : j < es.length := by
  obtain ⟨hm', rfl⟩ := recsOf_some hm
  obtain ⟨vid, l, pre, po, w, hv, rfl⟩ := vids_toRec3 _ _ hj
  obtain ⟨t, ht, hti, -⟩ := val_link hw hvw hvb hm' hv
  have := vpos_at hvw (vlen_le hvw) ht
  rw [hti] at this; rw [this]; exact ht

/-- **`reach_walk_at`**: a `VAL` walk starting at head `h` reaches value record `vpos a wv.k`
from `h.rid` (record level, independent of the value bytes). -/
theorem reach_walk_at {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) {h : HeadE} (hh : h ∈ hs) (hst : StartsAt wv h) (hfk : wv.fk = FK_VAL) :
    fullReach (recsOf (vpos (vid0 es)) vs) h.rid wv.key3 = some (vpos (vid0 es) wv.k) ∧
      vpos (vid0 es) wv.k < es.length := by
  let i := vpos (vid0 es) wv.k
  let Vp : List ValRec3 := valsOf3 vs es ++ List.replicate (i + 1) default
  have hip : i < Vp.length := by simp [Vp]; omega
  have hx : ∀ x, (fullTree (recsOf (vpos (vid0 es)) vs) (setVal Vp i x) h.rid).find wv.key3 = some (some x) := by
    intro x
    have := Walk3.walk3_val_at (walkHyp_any hw hhw hvw hW hb hvb hE hB hbytes hsym (setVal Vp i x)) hwv hh hst hfk
    rw [this, valOf_setVal_self hip]
  obtain ⟨hr, -⟩ := reach_of_find (f := (recsOf (vpos (vid0 es)) vs).length) Vp hx
  refine ⟨hr, ?_⟩
  obtain ⟨m, nr, hm, hj⟩ := reach_vids _ _ _ hr
  exact vids_lt hw hvw hvb hm hj

/-- **`reach_walk`**: every `VAL` walk has a head of its instance (the one it starts at) whose
root reaches the walk's value record. -/
theorem reach_walk {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧ StartsAt wv h ∧
      (wv.fk = FK_VAL → fullReach (recsOf (vpos (vid0 es)) vs) h.rid wv.key3 = some (vpos (vid0 es) wv.k) ∧
        vpos (vid0 es) wv.k < es.length) := by
  obtain ⟨h, hh, ht, hst⟩ :=
    Walk3.starts_at (walkHyp_any hw hhw hvw hW hb hvb hE hB hbytes hsym (valsOf3 vs es)) hwv
  exact ⟨h, hh, ht, hst, reach_walk_at hw hhw hvw hW hb hvb hE hB hbytes hsym hwv hh hst⟩

/-- **The `∀ x` form** (`post_eq_set'`): replacing the walk's value record by any `x`, the
walk's key finds `x` from the starting head's root. -/
theorem find_walk_any {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) {h : HeadE} (hh : h ∈ hs) (hst : StartsAt wv h) (hfk : wv.fk = FK_VAL)
    (x : Bytes) :
    (fullTree (recsOf (vpos (vid0 es)) vs) (setVal (valsOf3 vs es) (vpos (vid0 es) wv.k) x) h.rid).find wv.key3 =
      some (some x) := by
  obtain ⟨hr, hlt⟩ := reach_walk_at hw hhw hvw hW hb hvb hE hB hbytes hsym hwv hh hst hfk
  unfold fullTree
  rw [reach_find _ _ _ _ hr, valOf_setVal_self (by simp [valsOf3]; exact hlt)]

end ZkFormal.NearV3.Link3

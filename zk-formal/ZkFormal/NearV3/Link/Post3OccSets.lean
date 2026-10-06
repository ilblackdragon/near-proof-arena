import ZkFormal.NearV3.Link.Post3OccWalk

/-!
# ZkFormal.NearV3.Link.Post3OccSets — the post root is the iterated `set` (M6d wrapper)

For a head `h`, `R := recsOf (vpos (vid0 es)) vs`, `V := valsOf3 vs es` and a list of keyed
writes `wk : List (value position × key × new bytes)`:

* **`post_sets_tau`** — if the written value records occurring under `h.rid` are exactly the
  writes of `wk` (`hperm`: `(writesOf vs es pv).filter (0 < fullOcc R · h.rid)` is a permutation
  of `wk` without keys) and each key reaches its value record from `h.rid` (`hreach`), then
  `setAll (fullTree R V h.rid) (keys, bytes of wk) = some (fullTree R (valsPost vs es pv) h.rid)`
  and the `hashOf` of that trie is `toB h.post`;
* `post_sets_walk` — the same with `hreach` from `VAL` walks starting at `h` (`reach_walk_at`).

`occ_le_one` discharges the occurrence bound; `valsPost_eq_setVals` turns the post value records
into the instance writes; writes of value records that do not occur under `h.rid` (other
instances) leave its trie unchanged (`fullTree_setVals_filter`).

The covering hypothesis `hperm` (each written value record of the instance has a keyed write,
with the bytes `pv vid`) is a statement about which walks exist; it is not a record-level fact.
-/

set_option autoImplicit false

namespace ZkFormal.NearV3

open NearSpec

theorem setVals_setVal_comm {i : Nat} (v : Bytes) : ∀ (ws : List (Nat × Bytes)) (V : List ValRec3),
    i ∉ ws.map Prod.fst → setVals (setVal V i v) ws = setVal (setVals V ws) i v
  | [], _, _ => rfl
  | (j, b) :: r, V, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [setVals]
    rw [setVal_comm V (fun e => h.1 e) v b, setVals_setVal_comm v r _ h.2]

/-- A value record with no occurrence under `root` can be replaced freely. -/
theorem fullTree_setVal_occ0 {ns : List NodeRec3} (V : List ValRec3) {i root : Nat} (v : Bytes)
    (h : fullOcc ns i root = 0) : fullTree ns (setVal V i v) root = fullTree ns V root :=
  occ_zero V i v _ root h

/-- **Only the writes occurring under `root` matter.** -/
theorem fullTree_setVals_filter {ns : List NodeRec3} {root : Nat} : ∀ (ws : List (Nat × Bytes)) (V : List ValRec3),
    (ws.map Prod.fst).Nodup →
    fullTree ns (setVals V ws) root = fullTree ns (setVals V (ws.filter fun w => 0 < fullOcc ns w.1 root)) root
  | [], _, _ => rfl
  | (i, v) :: r, V, hd => by
    simp only [List.map_cons, List.nodup_cons] at hd
    have ih := fullTree_setVals_filter (ns := ns) (root := root) r (setVal V i v) hd.2
    simp only [setVals] at ih ⊢
    rw [ih]
    by_cases ho : 0 < fullOcc ns i root
    · simp [ho, setVals]
    · have hnot : i ∉ (r.filter fun w => 0 < fullOcc ns w.1 root).map Prod.fst := fun hm =>
        hd.1 ((List.filter_sublist.map Prod.fst).subset hm)
      simp only [List.filter_cons, ho, decide_false, Bool.false_eq_true, if_false]
      rw [setVals_setVal_comm v _ _ hnot, fullTree_setVal_occ0 _ v (by omega)]

end ZkFormal.NearV3

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3
open ZkFormal.NearV3.Walk3 (StartsAt)

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}
variable {others : List Msg} {shaS shaR : Nat → List Fp → Nat}

/-- **`post_sets_tau`**: the post trie of head `h` is the pre record trie with the keyed writes
`wk` applied by `PTrie.set` (left to right), and its hash is the head's post root. -/
theorem post_sets_tau (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) {pv : Nat → Bytes}
    (HP : VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {h : HeadE} (hh : h ∈ hs) (wk : List (Nat × List Nat × Bytes))
    (hperm : ((writesOf vs es pv).filter fun w => 0 < fullOcc (recsOf (vpos (vid0 es)) vs) w.1 h.rid).Perm
      (wk.map fun w => (w.1, w.2.2)))
    (hreach : ∀ w ∈ wk, fullReach (recsOf (vpos (vid0 es)) vs) h.rid w.2.1 = some w.1) :
    setAll (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid) (wk.map fun w => (w.2.1, w.2.2)) =
        some (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) h.rid) ∧
      (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) h.rid).hashOf = toB h.post := by
  refine ⟨?_, post_tau hw hhw hvw hb hvb H HP hpl hh⟩
  have hlt : ∀ w ∈ wk, w.1 < (valsOf3 vs es).length := by
    intro w hw'
    have hm : (w.1, w.2.2) ∈ (writesOf vs es pv).filter fun w => 0 < fullOcc (recsOf (vpos (vid0 es)) vs) w.1 h.rid :=
      hperm.symm.subset (List.mem_map.mpr ⟨w, hw', rfl⟩)
    have hm := (List.mem_filter.mp hm).1
    unfold writesOf at hm
    obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    have ht := List.mem_range.mp (List.mem_filter.mp ht).1
    simp only [Prod.mk.injEq] at he
    simp [valsOf3]; omega
  have hset := post_eq_sets (ns := recsOf (vpos (vid0 es)) vs) (root := h.rid) wk (valsOf3 vs es)
    (fun w hw' => ⟨hlt w hw', hreach w hw', occ_le_one hw hhw hvw hb hvb w.1 h.rid⟩)
  rw [hset, valsPost_eq_setVals, fullTree_setVals_filter _ _ (writesOf_nodup vs es pv),
    setVals_perm hperm (((writesOf_nodup vs es pv).sublist (List.filter_sublist.map Prod.fst)))]

/-- **`post_sets_walk`**: `post_sets_tau` with the reach hypotheses from `VAL` walks starting at
`h` (each write's key is such a walk's key and its value position the walk's value record). -/
theorem post_sets_walk {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    (H : ShaHyp vs hs es others shaS shaR) {pv : Nat → Bytes} (HP : VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {h : HeadE} (hh : h ∈ hs) (wk : List (Nat × List Nat × Bytes))
    (hperm : ((writesOf vs es pv).filter fun w => 0 < fullOcc (recsOf (vpos (vid0 es)) vs) w.1 h.rid).Perm
      (wk.map fun w => (w.1, w.2.2)))
    (hwalk : ∀ w ∈ wk, ∃ wv ∈ ws, wv.fk = FK_VAL ∧ StartsAt wv h ∧ wv.key3 = w.2.1 ∧ vpos (vid0 es) wv.k = w.1) :
    setAll (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid) (wk.map fun w => (w.2.1, w.2.2)) =
        some (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) h.rid) ∧
      (fullTree (recsOf (vpos (vid0 es)) vs) (valsPost vs es pv) h.rid).hashOf = toB h.post :=
  post_sets_tau hw hhw hvw hb hvb H HP hpl hh wk hperm (fun w hw' => by
    obtain ⟨wv, hwv, hfk, hst, hk, hi⟩ := hwalk w hw'
    rw [← hk, ← hi]
    exact (reach_walk_at hw hhw hvw hW hb hvb hE hB (rec_bytes hw hhw hvw hb H) hsym hwv hh hst hfk).1)

end ZkFormal.NearV3.Link3

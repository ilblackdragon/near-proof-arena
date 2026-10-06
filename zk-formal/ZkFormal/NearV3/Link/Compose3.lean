import ZkFormal.NearV3.Link.NodeHash3
import ZkFormal.NearV3.Link.Walk3

/-!
# ZkFormal.NearV3.Link.Compose3 — discharging the walk link's structural hypotheses

* `head_of` — every record's instance has a head (follow `PARENT` senders upwards; depth
  decreases);
* `unf3` — the unfolding equation of the record trie (`walk3_find`'s `hunf`) from the ranked
  DAG of the record's instance (`rootedDag3`, `fullTree_unfoldR`);
* `walk3_find'` — `walk3_find` with `hunf`, `hpar` (`kid_depth`) and `hhead` (`head_link`)
  discharged.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

/-- Every record's instance has a head. -/
theorem head_of (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) :
    ∀ n (hn : n < vs.length), ∃ h ∈ hs, h.tau = vs[n].tau := by
  have key : ∀ d n (hn : n < vs.length), vs[n].depth = d → ∃ h ∈ hs, h.tau = vs[n].tau := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro n hn hd
      rcases sender_of hw hhw hb hn with ⟨h, hh, -, ht, -⟩ | ⟨p, hp, l, r, pre, po, hk, ht, -⟩
      · exact ⟨h, hh, ht⟩
      · obtain ⟨_hc, _ht, hdc, _hr⟩ := kid_depth hw hhw hb hp hk
        have hdc' : vs[n].depth = vs[p].depth + 1 := hdc
        obtain ⟨h, hh, hth⟩ := ih vs[p].depth (by omega) p hp rfl
        exact ⟨h, hh, by rw [hth, ht]⟩
  exact fun n hn => key _ n hn rfl

/-- **The unfolding equation** (`hunf` of `walk3_find`). -/
theorem unf3 (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (hlen : es.length ≤ 2 ^ 22) (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256) :
    ∀ n (hn : n < vs.length), fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) n =
      nodeTree3 (valsOf3 vs es) (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es))
        (vs[n].v.toRec3 (vpos (vid0 es))) := by
  intro n hn
  obtain ⟨h, hh, ht⟩ := head_of hw hhw hb n hn
  have hd := rootedDag3 hw hhw hvw hb hvb hlen hbytes hh
  exact fullTree_unfoldR hd (recsOf_get _ _ hn) (by simp only; rw [ht])

/-- **`walk3_find` with the structural hypotheses discharged.** -/
theorem walk3_find' {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hlen : es.length ≤ 2 ^ 22) (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hT : (ws.flatMap (·.steps)).length < ZkFormal.Algebra.P)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk = FK_ABS → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 = some none) :=
  Walk3.walk3_find hw hhw hW hE hB hT hsym (unf3 hw hhw hvw hb hvb hlen hbytes)
    (fun p hp c l r pre po hk => by
      obtain ⟨hc, -, -, hr⟩ := kid_depth hw hhw hb hp hk; exact ⟨hc, hr⟩)
    (fun h hh => by obtain ⟨hr, -, -, -, he⟩ := head_link hw hhw hb hh; exact ⟨hr, he⟩) hwv

end ZkFormal.NearV3.Link3

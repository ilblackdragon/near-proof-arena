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

/-- Value records fit the table: `|es| ≤ 2^22` (`ValWf.rows`, one row at least per record). -/
theorem vlen_le (hvw : ValWf es) : es.length ≤ 2 ^ 22 := by
  have hr := hvw.rows
  have : es.length ≤ (es.map fun e => if e.vz then 1 else e.len).sum := by
    have gen : ∀ l : List ValE, (∀ e ∈ l, (e.vz = false → 0 < e.len)) →
        l.length ≤ (l.map fun e => if e.vz then 1 else e.len).sum := by
      intro l; induction l with
      | nil => intro _; simp
      | cons e r ih =>
        intro h
        have := ih (fun e' he' => h e' (by simp [he']))
        have he := h e (by simp)
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        cases hz : e.vz
        · have := he hz; simp only [Bool.false_eq_true, if_false]; omega
        · simp only [if_true]; omega
    exact gen es (fun e he hz => ((hvw.shape e he).2 hz).2)
  omega

/-- Walk rows are below `P` (`WalkWf3.nrows`: `≤ 2^23`, `walkV3` height `≤ 2^21` plus the `upsV3` walks). -/
theorem wrows_lt {ws : List WalkR} (hW : WalkWf3 ws) : (ws.flatMap (·.steps)).length < ZkFormal.Algebra.P := by
  have := hW.nrows; unfold ZkFormal.Algebra.P; omega

/-- **`walk3_find` with the structural hypotheses discharged.** -/
theorem walk3_find' {ws : List WalkR}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    (hsym : ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk = FK_ABS → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 = some none) :=
  Walk3.walk3_find hw hhw hW hE hB (wrows_lt hW) hsym (unf3 hw hhw hvw hb hvb (vlen_le hvw) hbytes)
    (fun p hp c l r pre po hk => by
      obtain ⟨hc, -, -, hr⟩ := kid_depth hw hhw hb hp hk; exact ⟨hc, hr⟩)
    (fun h hh => by obtain ⟨hr, -, -, -, he⟩ := head_link hw hhw hb hh; exact ⟨hr, he⟩) hwv

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (i : Nat) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD]

/-- The `KEYNIB` providers (other tables) send only nibbles and `END`, and every `KEYNIB`
message a walk receives is provided. -/
structure KeynibOk (ws : List WalkR) (prov : List Msg) : Prop where
  sub : ∀ m ∈ walkRecvs3 ws B_KEYNIB, Msg.toFp m ∈ prov.map Msg.toFp
  syms : ∀ m ∈ prov, m.getD 2 0 < ZkFormal.Algebra.P ∧ (m.getD 2 0 < 16 ∨ m.getD 2 0 = SYM_END)

/-- **`hsym` from `KEYNIB`.** -/
theorem hsym_of {ws : List WalkR} {prov : List Msg} (hW : WalkWf3 ws) (hk : KeynibOk ws prov) :
    ∀ wv ∈ ws, ∀ i, 1 ≤ i → i < wv.steps.length → (wv.step i).sym ≠ SYM_START := by
  intro wv hwv i h1 h2 hs
  have hm : [wv.w, i - 1, (wv.step i).sym, if i - 1 + 2 = wv.steps.length then 1 else 0] ∈ walkRecvs3 ws B_KEYNIB := by
    unfold walkRecvs3
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl, List.mem_flatMap]
    refine ⟨wv, hwv, List.mem_map.mpr ⟨i - 1, List.mem_range.mpr (by omega), ?_⟩⟩
    rw [show i - 1 + 1 = i by omega]
  obtain ⟨m, hmp, he⟩ := List.mem_map.mp (hk.sub _ hm)
  obtain ⟨hP, hsy⟩ := hk.syms m hmp
  have hsP : (wv.step i).sym < ZkFormal.Algebra.P := by
    have := (hW.canon wv hwv).2.2 (wv.step i) (by
      simp only [WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
      exact List.getElem_mem h2)
    exact this.1
  have e2 := congrArg (fun l => l.getD 2 (Fp.ofNat 0)) he
  simp only [Msg.toFp, getD_map'] at e2
  simp only [List.getD_cons_succ, List.getD_cons_zero] at e2
  have := ofNat_eq hP hsP e2
  rw [hs] at this; rw [this] at hsy; simp [SYM_START, SYM_END] at hsy

end ZkFormal.NearV3.Link3

import ZkFormal.NearV3.Link.Sha3

/-!
# ZkFormal.NearV3.Link.PerTau3 — per-instance trie statement

For every head `h` (instance `h.tau`, root record `h.rid`), with `R := recsOf (vpos (vid0 es)) vs`,
`V := valsOf3 vs es`:
* `root_tau` — `digest R V h.rid = toB h.pre` (the head's pre-root window);
* `build_tau` — for any key list whose lookups are determined on the record trie, the relation's
  `partialTrie (storeOf R V h.tau) (toB h.pre) keys` has root hash `toB h.pre` and answers every
  key as the record trie (`storeBuildR`, `pathsRevealed_of_rank`, `rk_lt`);
* `walks_tau` — every walk computes `find` / absent on the record trie of a head of its instance
  (`walk3_find'` with `hbytes` from the SHA glue and `hsym` from `KEYNIB`).
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

/-- **Root of an instance.** -/
theorem root_tau (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) {h : HeadE} (hh : h ∈ hs) :
    digest (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid = toB h.pre := by
  have hbytes := rec_bytes hw hhw hvw hb H
  have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
  obtain ⟨hr, -, hpre⟩ := head_sha hw hhw hvw hb H hh
  obtain ⟨_, henc, hnode⟩ := enc_fullTree hd hw hbytes
    (fun p hp c l r pre po hk => by
      obtain ⟨hc, -, he⟩ := kid_sha hw hhw hvw hb H hp hk; exact ⟨hc, he⟩)
    (fun p hp i l pre po w hv => val_sha hw hhw hvw hvb H hp hv)
    h.rid hd.root_inst
  unfold digest
  rw [hashOf_eq_enc _ hnode, henc, hpre, toB_toNat]

/-- **The relation's trie of an instance.** -/
theorem build_tau (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR) {h : HeadE} (hh : h ∈ hs)
    (hHF : HashFunctional (storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau))
    (keys : List (List Nat))
    (hdet : ∀ k ∈ keys, (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find k ≠ none) :
    (partialTrie (storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau) (toB h.pre) keys).hashOf =
        toB h.pre ∧
      ∀ k ∈ keys, (partialTrie (storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau) (toB h.pre) keys).find k =
        (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find k := by
  have hbytes := rec_bytes hw hhw hvw hb H
  have hd := rootedDag3 hw hhw hvw hb hvb (vlen_le hvw) hbytes hh
  have hp := pathsRevealed_of_rank hd (rk_lt hw hhw hb _ h.tau) keys hdet
  have hs' := storeBuildR _ _ _ _ _ keys hHF hd hp
  rw [root_tau hw hhw hvw hb hvb H hh] at hs'
  exact ⟨hs'.2.1, hs'.2.2⟩

/-- **Walks of the instances.** -/
theorem walks_tau {ws : List WalkR} {prov : List Msg}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hW : WalkWf3 ws)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hE : Walk3.BusBal vs hs ws B_EDGE) (hB : Walk3.BusBal vs hs ws B_BMAP) (hK : KeynibOk ws prov)
    {wv : WalkR} (hwv : wv ∈ ws) :
    ∃ h ∈ hs, h.tau = wv.tau ∧
      (wv.fk = FK_VAL → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 =
        some (some (valOf (valsOf3 vs es) (vpos (vid0 es) wv.k)))) ∧
      (wv.fk = FK_ABS → (fullTree (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.rid).find wv.key3 = some none) :=
  walk3_find' hw hhw hvw hW hb hvb hE hB (rec_bytes hw hhw hvw hb H) (hsym_of hW hK) hwv

end ZkFormal.NearV3.Link3

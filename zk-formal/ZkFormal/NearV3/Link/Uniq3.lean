import ZkFormal.NearV3.Link.Uniq3Digs

/-!
# ZkFormal.NearV3.Link.Uniq3 — the witness store of each instance is hash-functional

With `R := recsOf (vpos (vid0 es)) vs`, `V := valsOf3 vs es`, for every head `h`:
`store_hashFunctional : HashFunctional (storeOf R V h.tau)`, from the views (`NodeWf3`,
`HeadWf`, `ValWf`, `UniqWf`), the `PARENT` / `VPARENT` balances, the SHA glue (`ShaHyp`) and
the `DIGS` / `DUP` / `ENT` balances (`DigsBal`, `DupBal`, `EntBal`).

`storeOf_hashFunctional3` (`Uniq3Core`) with `B := bOf vs es` (`NPRE n ↦` record `n`'s bytes,
`VPRE t ↦` value `t`'s bytes):
* `hdup` — `dup_bytes` (`Uniq3Ent`);
* `hbytes` — `uniq_byte_lt`, `|uniq| ≤ P` — `uniq_len` (`Uniq3Digs`);
* `hcov` — `store_cov`: every store entry of instance `τ` (a node record of `τ`, by
  `enc_fullTree` its bytes; a value of `τ`) is `bOf E` for the id `E` of a window that sends
  `DIGS (E, τ, ·)` (the record's sender — `sender_of` — or the value's parent — `VPARENT`), so a
  `uniq` entry with that id and instance exists, and its digest bytes are `digNat (bOf E)`.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat}

theorem cov_of_send (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) {E τ' : Nat} {r : List Nat}
    (hE : E < P) (hτ : τ' < P) (hm : E :: τ' :: r ∈ nodeSends3 vs B_DIGS ++ headSends hs B_DIGS) :
    ∃ e ∈ us, e.tau = τ' ∧ bOf vs es e.eid = bOf vs es E ∧ e.bytes = digNat (bOf vs es E) := by
  obtain ⟨e, he, rfl, rfl⟩ := uniq_of_send huw hD hE hτ hm
  exact ⟨e, he, rfl, rfl, uniq_bytes hw hhw hvw huw hb hvb H hD he⟩

/-- Record `n` has a window `DIGS (NPRE n, τ_n, 0, ·)`. -/
theorem node_window (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) {n : Nat} (hn : n < vs.length) :
    ∃ r : List Nat, msgId K_NPRE n :: vs[n].tau :: r ∈ nodeSends3 vs B_DIGS ++ headSends hs B_DIGS := by
  rcases sender_of hw hhw hb hn with ⟨h, hh, hr, ht, -⟩ | ⟨p, hp, l, r, pre, po, hk, ht, -⟩
  · refine ⟨[0, h.pre.getD 0 0], List.mem_append_right _ ?_⟩
    rw [digsHs, List.mem_flatMap]
    refine ⟨h, hh, ?_⟩
    rw [digsH, List.mem_map]
    exact ⟨0, by simp, by rw [hr, ht]⟩
  · refine ⟨[0, pre.getD 0 0], List.mem_append_left _ ?_⟩
    rw [digsN, List.mem_flatMap]
    refine ⟨(vs[p], p), zip_range_mem vs hp, ?_⟩
    simp only [digsOf, List.mem_append, List.mem_flatMap, List.mem_map]
    left
    exact ⟨(n, l, r, pre, po), hk, 0, by simp, by rw [ht]⟩

/-- Every value record has a parent window. -/
theorem val_parent (hw : NodeWf3 vs) (hvw : ValWf es) (hvb : VParentBal vs es) {t : Nat} (ht : t < es.length) :
    ∃ p, ∃ hp : p < vs.length, ∃ l pre po w, vs[p].v.value = some (es[t].vid, l, pre, po, w) := by
  have h1 : 0 < cnt3 (valRecvs es B_VPARENT) (Msg.toFp [es[t].vid, es[t].len]) := by
    rw [cnt3, List.count_pos_iff, List.mem_map]
    exact ⟨_, by rw [vparentR, List.mem_map]; exact ⟨es[t], List.getElem_mem ht, rfl⟩, rfl⟩
  rw [← hvb, cnt3, List.count_pos_iff, List.mem_map, vparentS] at h1
  obtain ⟨m, hm, he⟩ := h1
  rw [List.mem_flatMap] at hm
  obtain ⟨⟨s, p⟩, hsp, hm⟩ := hm
  obtain ⟨hp, rfl⟩ := mem_zip_range hsp
  cases hv : vs[p].v.value with
  | none => simp [vparMsg, hv] at hm
  | some x =>
    obtain ⟨i, l, pre, po, w⟩ := x
    simp only [vparMsg, hv, List.mem_singleton] at hm
    subst hm
    obtain ⟨ri, -⟩ := value_raw hv
    have ci := hw.canon _ (List.getElem_mem hp) i ri
    have ce := hvw.canon _ (List.getElem_mem ht)
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq] at he
    have := ofNat_eq ci ce.1 he.1
    subst this
    exact ⟨p, hp, l, pre, po, w, hv⟩

/-- **`hcov`**: every store entry of a head's instance is covered by a `uniq` entry. -/
theorem store_cov (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) {h : HeadE} (hh : h ∈ hs) :
    ∀ x ∈ storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau,
      ∃ e ∈ us, e.tau = h.tau ∧ bOf vs es e.eid = x ∧ e.bytes = digNat x := by
  have hvl := vlen_le hvw
  have hbytes := rec_bytes hw hhw hvw hb H
  intro x hx
  rw [storeOf, List.mem_append] at hx
  rcases hx with hx | hx
  · -- a node record of the instance
    simp only [nodeEntries, List.mem_filterMap, List.mem_range, recsOf_length] at hx
    obtain ⟨n, hn, hx⟩ := hx
    rw [recsOf_get _ _ hn] at hx
    simp only at hx
    split at hx
    · rename_i ht
      simp only [Option.some.injEq] at hx
      subst hx
      have hd := rootedDag3 hw hhw hvw hb hvb hvl hbytes hh
      obtain ⟨_, henc, -⟩ := enc_fullTree hd hw hbytes
        (fun p hp c l r pre po hk => by
          obtain ⟨hc, -, he⟩ := kid_sha hw hhw hvw hb H hp hk; exact ⟨hc, he⟩)
        (fun p hp i l pre po w hv => val_sha hw hhw hvw hvb H hp hv)
        n ⟨_, recsOf_get _ _ hn, ht⟩
      rw [henc]
      have hx : toB (vs[n].v.ser false) = bOf vs es (msgId K_NPRE n) := by rw [bOf, bN_node vs es hn]
      rw [hx, ← ht]
      obtain ⟨r, hm⟩ := node_window hw hhw hb hn
      exact cov_of_send hw hhw hvw huw hb hvb H hD (nid_lt hw hn K_NPRE (by decide))
        (hw.small _ (List.getElem_mem hn)).1 hm
    · simp at hx
  · -- a value of the instance
    simp only [valEntries, valsOf3, List.filter_map, List.map_map, List.mem_map, List.mem_filter,
      Function.comp_def, beq_iff_eq] at hx
    obtain ⟨e, ⟨he, ht⟩, rfl⟩ := hx
    obtain ⟨t, htl, rfl⟩ := List.getElem_of_mem he
    obtain ⟨p, hp, l, pre, po, w, hv⟩ := val_parent hw hvw hvb htl
    have htau := valTau_eq hw hvw hvb hvl hp hv
    have hvt := vid_small hvw htl
    rw [hvt] at hv htau
    have hx : toB es[t].bytes = bOf vs es (msgId K_VPRE t) := by rw [bOf, bN_val vs es htl]
    rw [hx, ← ht, hvt, htau]
    have hm : msgId K_VPRE t :: vs[p].tau :: [0, pre.getD 0 0] ∈ nodeSends3 vs B_DIGS ++ headSends hs B_DIGS := by
      apply List.mem_append_left
      rw [digsN, List.mem_flatMap]
      refine ⟨(vs[p], p), zip_range_mem vs hp, ?_⟩
      simp only [digsOf, List.mem_append, hv, List.mem_map]
      right
      exact ⟨0, by simp, rfl⟩
    exact cov_of_send hw hhw hvw huw hb hvb H hD (by unfold msgId K_VPRE P; omega)
      (hw.small _ (List.getElem_mem hp)).1 hm

/-- **The witness store of each instance is hash-functional.** -/
theorem store_hashFunctional (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hDIGS : DigsBal vs hs us) (hDUP : DupBal us vs es) (hENT : EntBal vs es)
    {h : HeadE} (hh : h ∈ hs) :
    HashFunctional (storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau) :=
  storeOf_hashFunctional3 us huw (bOf vs es) (dup_bytes hw hvw huw hDUP hENT)
    (uniq_byte_lt hw hhw hvw huw hb hvb H hDIGS) (uniq_len hw hb hDIGS) h.tau _
    (store_cov hw hhw hvw huw hb hvb H hDIGS hh)

end ZkFormal.NearV3.Link3

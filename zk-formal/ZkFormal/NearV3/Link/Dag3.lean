import ZkFormal.NearV3.Link.Vals3

/-!
# ZkFormal.NearV3.Link.Dag3 — the records of each instance form a ranked rooted DAG

`rootedDag3`: for every head `h`, the node records `recsOf (vpos a) vs` and value records
`valsOf3 vs es` satisfy `RootedDagR … h.tau h.rid depth` (rank = depth, children one deeper,
`Spec/Rank.lean`), from the `PARENT` / `VPARENT` balances, the views' local facts, and byte
bounds on the record serialisations (from the SHA contract).  `depth_lt` gives every rank
`< 400 = trieFuel`.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3

theorem le256_lt : ∀ (l : List Nat), (∀ x ∈ l, x < 256) → le256 l < 256 ^ l.length
  | [], _ => by simp [le256]
  | x :: r, h => by
    have := le256_lt r (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [le256, List.length_cons, Nat.pow_succ]
    have : 256 * le256 r + x < 256 * (le256 r + 1) := by omega
    have : 256 * (le256 r + 1) ≤ 256 * 256 ^ r.length := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm (256 ^ r.length)]; omega

theorem length_le_of_sublist_append {a b c d : List Nat} {x : List Nat} (h : x = a ++ b ++ c ++ d) :
    b.length ≤ x.length ∧ c.length ≤ x.length ∧ d.length ≤ x.length := by
  subst h; simp; omega

variable {vs : List NodeS3} {hs : List HeadE} {es : List ValE}

theorem valTau_eq (hw : NodeWf3 vs) (hvw : ValWf es) (hb : VParentBal vs es) (hlen : es.length ≤ 2 ^ 22)
    {n : Nat} (hn : n < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[n].v.value = some (i, l, pre, po, w)) : valTau vs i = vs[n].tau := by
  unfold valTau
  have hp : (fun s : NodeS3 => match s.v.value with | some (j, _) => j == i | none => false) vs[n] = true := by
    simp [hv]
  cases hf : vs.find? (fun s : NodeS3 => match s.v.value with | some (j, _) => j == i | none => false) with
  | none => exact absurd (List.find?_eq_none.mp hf vs[n] (List.getElem_mem hn)) (by simp [hp])
  | some s =>
    have hs := List.find?_some hf
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hf)
    cases hvm : vs[m].v.value with
    | none => simp [hvm] at hs
    | some x =>
      obtain ⟨j, l', pre', po', w'⟩ := x
      simp only [hvm, beq_iff_eq] at hs
      subst hs
      have := val_unique hw hvw hb hlen hm hn hvm hv
      subst this; rfl

/-- Value positions: a revealed value `vid` of a record is the value record at `vpos a vid`. -/
theorem val_pos (hw : NodeWf3 vs) (hvw : ValWf es) (hb : VParentBal vs es) (hlen : es.length ≤ 2 ^ 22)
    {n : Nat} (hn : n < vs.length) {i l : Nat} {pre po : List Nat} {w : Bool}
    (hv : vs[n].v.value = some (i, l, pre, po, w)) :
    ∃ t, ∃ ht : t < es.length, vpos (vid0 es) i = t ∧ es[t].vid = i ∧ es[t].len = l ∧
      (valsOf3 vs es)[t]? = some ⟨vs[n].tau, toB es[t].bytes⟩ := by
  obtain ⟨t, ht, hi, hl⟩ := val_link hw hvw hb hn hv
  refine ⟨t, ht, by rw [← hi]; exact vpos_at hvw hlen ht, hi, hl, ?_⟩
  simp [valsOf3, ht, hi, valTau_eq hw hvw hb hlen hn hv]

theorem valOf_len (hvw : ValWf es) {τ t : Nat} (ht : t < es.length) (hV : (valsOf3 vs es)[t]? = some ⟨τ, toB es[t].bytes⟩) :
    (valOf (valsOf3 vs es) t).length = es[t].len := by
  simp only [valOf, hV, Option.map_some, Option.getD_some, toB, List.length_map]
  have := (hvw.shape _ (List.getElem_mem ht))
  cases hz : es[t].vz
  · exact (this.2 hz).1
  · rw [(this.1 hz).1, (this.1 hz).2]; rfl

theorem len_le_rows (hvw : ValWf es) {t : Nat} (ht : t < es.length) : es[t].len < 2 ^ 32 := by
  have hr := hvw.rows
  have hm : (if es[t].vz then 1 else es[t].len) ≤ (es.map fun e => if e.vz then 1 else e.len).sum :=
    le_sum_mem (List.mem_map.mpr ⟨es[t], List.getElem_mem ht, rfl⟩)
  have := (hvw.shape _ (List.getElem_mem ht))
  cases hz : es[t].vz
  · rw [hz] at hm; simp at hm; omega
  · rw [(this.1 hz).1]; omega

/-- `Rec3.wf` of a record. -/
theorem rec_wf (hw : NodeWf3 vs) (hvw : ValWf es) (hb : VParentBal vs es) (hlen : es.length ≤ 2 ^ 22)
    (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256) {n : Nat} (hn : n < vs.length) :
    (vs[n].v.toRec3 (vpos (vid0 es))).wf (valsOf3 vs es) := by
  have hmem := List.getElem_mem hn
  have hwf := hw.wf _ hmem
  have hby := hbytes _ hmem
  have hser : (vs[n].v.ser false).length ≤ 2 ^ 22 := by
    have := le_sum_mem (l := vs.map fun s => (s.v.ser false).length) (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    have := hw.rows; omega
  have hval := fun {i l pre po w} (h : vs[n].v.value = some (i, l, pre, po, w)) => val_pos hw hvw hb hlen hn h
  generalize hS : vs[n] = S at hwf hby hser hval
  obtain ⟨v, tau, depth, res, uses, ubm, dup, hd, repE⟩ := S
  simp only at hwf hby hser hval ⊢
  -- value slots
  have slotW : ∀ sl : NSlot3, sl.wf → (∀ x ∈ sl.bytes false, x < 256) →
      (∀ {lb i l pre po w}, sl = .val lb i l pre po w → ∃ t, ∃ ht : t < es.length, vpos (vid0 es) i = t ∧
        es[t].vid = i ∧ es[t].len = l ∧ (valsOf3 vs es)[t]? = some ⟨tau, toB es[t].bytes⟩) →
      (sl.toV3 (vpos (vid0 es))).wf (valsOf3 vs es) := by
    intro sl hsw hsb hsv
    cases sl with
    | ref lenB h =>
      obtain ⟨h4, h32⟩ := hsw
      refine ⟨?_, by simp [toB, h32]⟩
      have := le256_lt lenB (fun x hx => hsb x (by simp [NSlot3.bytes, hx]))
      rw [h4] at this; simp at this ⊢; omega
    | val lb i l pre po w =>
      obtain ⟨t, ht, hp, -, hl, hV⟩ := hsv rfl
      show (valOf (valsOf3 vs es) (vpos (vid0 es) i)).length < 4294967296
      rw [hp, valOf_len hvw ht hV]; have := len_le_rows hvw ht; omega
  have memW : ∀ m : List Nat, m.length = 8 → (∀ x ∈ m, x < 256) → le256 m < 18446744073709551616 := by
    intro m h8 hm; have := le256_lt m hm; rw [h8] at this; simpa using this
  have nib : ∀ k : List Nat, (∀ x ∈ k, x < 16) → nibblesOk k = true := by
    intro k hk; simp [nibblesOk, List.all_eq_true]; exact hk
  cases v with
  | leaf k sl m =>
    obtain ⟨hk, hsw, hm8⟩ := hwf
    simp only [NodeV3.ser, List.mem_append] at hby
    simp only [NodeV3.toRec3, Rec3.wf]
    refine ⟨nib k hk, ?_, slotW sl hsw (fun x hx => hby x (Or.inl (Or.inr hx)))
      (fun {lb i l pre po w} h => by subst h; exact hval (i := i) (l := l) (pre := pre) (po := po) (w := w) (by simp [NodeV3.value])), memW m hm8 (fun x hx => hby x (Or.inr hx))⟩
    have : (hpN k true).length ≤ (NodeV3.ser false (.leaf k sl m)).length := by simp [NodeV3.ser]; omega
    simp only [hpN, List.length_map] at this; omega
  | ext k kid m =>
    obtain ⟨hk, hne, hkw, hm8⟩ := hwf
    simp only [NodeV3.ser, List.mem_append] at hby
    simp only [NodeV3.toRec3, Rec3.wf]
    refine ⟨nib k hk, ?_, ?_, ?_, memW m hm8 (fun x hx => hby x (Or.inr hx))⟩
    · have : (hpN k false).length ≤ (NodeV3.ser false (.ext k kid m)).length := by simp [NodeV3.ser]; omega
      simp only [hpN, List.length_map] at this; omega
    · cases kid <;> simp_all [NKid.toKid3]
    · cases kid <;> simp_all [NKid.toKid3, Kid3.wf, NKid.wf, toB]
  | branch sv kids m =>
    obtain ⟨h16, hsv, hkw, hm8⟩ := hwf
    simp only [NodeV3.ser, List.mem_append] at hby
    simp only [NodeV3.toRec3, Rec3.wf]
    refine ⟨by simp [h16], ?_, ?_, memW m hm8 (fun x hx => hby x (Or.inr hx))⟩
    · intro s hs
      cases sv with
      | none => simp at hs
      | some sl =>
        simp at hs; subst hs
        exact slotW sl (hsv sl rfl) (fun x hx => hby x (Or.inl (Or.inl (Or.inl (by simp [hx])))))
          (fun {lb i l pre po w} h => by subst h; exact hval (i := i) (l := l) (pre := pre) (po := po) (w := w) (by simp [NodeV3.value]))
    · intro kid hk
      simp only [List.mem_map] at hk
      obtain ⟨kd, hkd, rfl⟩ := hk
      have := hkw kd hkd
      cases kd <;> simp_all [NKid.toKid3, Kid3.wf, NKid.wf, toB]

theorem vids_toRec3 (f : Nat → Nat) (v : NodeV3) {i : Nat} (h : i ∈ (v.toRec3 f).vids) :
    ∃ vid l pre po w, v.value = some (vid, l, pre, po, w) ∧ i = f vid := by
  cases v with
  | leaf k sl m =>
    cases sl with
    | ref => simp [NodeV3.toRec3, NSlot3.toV3, Rec3.vids] at h
    | val lb vid l pre po w =>
      simp [NodeV3.toRec3, NSlot3.toV3, Rec3.vids] at h; exact ⟨vid, l, pre, po, w, rfl, h⟩
  | ext => simp [NodeV3.toRec3, Rec3.vids] at h
  | branch sv kids m =>
    cases sv with
    | none => simp [NodeV3.toRec3, Rec3.vids] at h
    | some sl =>
      cases sl with
      | ref => simp [NodeV3.toRec3, NSlot3.toV3, Rec3.vids] at h
      | val lb vid l pre po w =>
        simp [NodeV3.toRec3, NSlot3.toV3, Rec3.vids] at h; exact ⟨vid, l, pre, po, w, rfl, h⟩

theorem lt_of_getElem? {α : Type} {l : List α} {n : Nat} {x : α} (h : l[n]? = some x) : n < l.length := by
  rcases Nat.lt_or_ge n l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

/-- Rank of a record: its depth. -/
def rkOf (vs : List NodeS3) (n : Nat) : Nat := (vs.getD n default).depth

/-- **The records of instance `h.tau` form a ranked rooted DAG under `h.rid`.** -/
theorem rootedDag3 (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (hb : ParentBal vs hs)
    (hvb : VParentBal vs es) (hlen : es.length ≤ 2 ^ 22) (hbytes : ∀ s ∈ vs, ∀ x ∈ s.v.ser false, x < 256)
    {h : HeadE} (hh : h ∈ hs) :
    RootedDagR (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau h.rid (rkOf vs) := by
  have get : ∀ {n : Nat} {nr : NodeRec3}, (recsOf (vpos (vid0 es)) vs)[n]? = some nr →
      ∃ hn : n < vs.length, nr = ⟨vs[n].tau, vs[n].v.toRec3 (vpos (vid0 es))⟩ := by
    intro n nr hr
    have hn : n < vs.length := by
      have := lt_of_getElem? hr; rwa [recsOf_length] at this
    rw [recsOf_get _ _ hn] at hr
    exact ⟨hn, (Option.some.inj hr).symm⟩
  obtain ⟨hr, hrt, -, -, -⟩ := head_link hw hhw hb hh
  refine ⟨⟨_, recsOf_get _ _ hr, hrt⟩, ?_, ?_, ?_⟩
  · intro n nr hn ht c hc
    obtain ⟨hn', rfl⟩ := get hn
    simp only at ht hc
    obtain ⟨l, r, pre, po, hk⟩ := (kids_toRec3 _ _ c).mp hc
    obtain ⟨hcl, htc, hdc, -⟩ := kid_depth hw hhw hb hn' hk
    refine ⟨?_, ⟨_, recsOf_get _ _ hcl, by simp only; rw [htc, ht]⟩⟩
    simp only [rkOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn', List.getElem?_eq_getElem hcl,
      Option.getD_some, hdc]
    omega
  · intro n nr hn ht i hi
    obtain ⟨hn', rfl⟩ := get hn
    simp only at ht hi
    obtain ⟨vid, l, pre, po, w, hv, rfl⟩ := vids_toRec3 _ _ hi
    obtain ⟨t, ht', hp, -, -, hV⟩ := val_pos hw hvw hvb hlen hn' hv
    exact ⟨_, by rw [hp]; exact hV, by simp only; exact ht⟩
  · intro n nr hn _
    obtain ⟨hn', rfl⟩ := get hn
    exact rec_wf hw hvw hvb hlen hbytes hn'

/-- Ranks are below `trieFuel`. -/
theorem rk_lt (hw : NodeWf3 vs) (hhw : HeadWf hs) (hb : ParentBal vs hs) (f : Nat → Nat) (τ : Nat) :
    ∀ n, InInst (recsOf f vs) τ n → rkOf vs n < trieFuel := by
  intro n hI
  obtain ⟨nr, hn, -⟩ := hI
  have hl : n < vs.length := by
    have := lt_of_getElem? hn; rwa [recsOf_length] at this
  simp only [rkOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some, trieFuel]
  exact depth_lt hw hhw hb hl

end ZkFormal.NearV3.Link3

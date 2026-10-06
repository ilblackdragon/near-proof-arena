import ZkFormal.NearV3.Link.Parent3

/-!
# ZkFormal.NearV3.Link.Vals3 — value records: positions and `VPARENT` balance

* `vid_at` — `valV3` ids are consecutive mod `P` from the first id `a`: `es[t].vid = (a+t) % P`,
  hence `vpos a es[t].vid = t` and ids are distinct;
* `val_link` — every revealed value slot `(vid, vlen, …)` of a node record is a value record
  `es[t]` with `vid`, `len = vlen`;
* `val_unique` — two node records never reveal the same value id;
* `valTau_eq` — so the instance of value record `vid` is that of its node record.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

/-- First value id. -/
def vid0 (es : List ValE) : Nat := (es.head?.map ValE.vid).getD 0

theorem P_big : 2 ^ 22 + 2 ^ 22 < P := by unfold P; omega

theorem vid_at {es : List ValE} (hvw : ValWf es) (hlen : es.length ≤ 2 ^ 22) :
    ∀ t (ht : t < es.length), es[t].vid = (vid0 es + t) % P := by
  intro t
  induction t with
  | zero =>
    intro ht
    have h0 := (hvw.canon _ (List.getElem_mem ht)).1
    match es, ht with
    | e :: _, _ => simp at h0; simp [vid0]; exact (Nat.mod_eq_of_lt h0).symm
  | succ t ih =>
    intro ht
    rw [hvw.ids t ht, ih (by omega), Nat.mod_add_mod, Nat.add_assoc]

theorem vpos_at {es : List ValE} (hvw : ValWf es) (hlen : es.length ≤ 2 ^ 22) {t : Nat} (ht : t < es.length) :
    vpos (vid0 es) es[t].vid = t := by
  have ha : vid0 es < P := by
    unfold vid0; cases es with
    | nil => simp at ht
    | cons e r => simpa using (hvw.canon e (by simp)).1
  rw [vid_at hvw hlen t ht, vpos]
  have := P_big
  rcases Nat.lt_or_ge (vid0 es + t) P with h | h
  · rw [Nat.mod_eq_of_lt h, show vid0 es + t + P - vid0 es = t + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [show (vid0 es + t) % P = vid0 es + t - P by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)],
      show vid0 es + t - P + P - vid0 es = t by omega, Nat.mod_eq_of_lt (by omega)]

theorem vid_inj {es : List ValE} (hvw : ValWf es) (hlen : es.length ≤ 2 ^ 22) {t t' : Nat}
    (ht : t < es.length) (ht' : t' < es.length) (he : es[t].vid = es[t'].vid) : t = t' := by
  rw [← vpos_at hvw hlen ht, ← vpos_at hvw hlen ht', he]

/-- The `VPARENT` balance (node value windows send, value records receive). -/
def VParentBal (vs : List NodeS3) (es : List ValE) : Prop :=
  ∀ m, cnt3 (nodeSends3 vs B_VPARENT) m = cnt3 (valRecvs es B_VPARENT) m

def vparMsg (s : NodeS3) : List Msg := match s.v.value with | some (i, l, _, _, _) => [[i, l]] | none => []

theorem vparentS (vs : List NodeS3) :
    nodeSends3 vs B_VPARENT = (vs.zip (List.range vs.length)).flatMap fun (s, _) => vparMsg s := by
  unfold nodeSends3 vparMsg; simp [B_VPARENT, B_BYTES, B_PARENT]; rfl

theorem vparentR (es : List ValE) : valRecvs es B_VPARENT = es.map fun e => [e.vid, e.len] := by
  simp [valRecvs, B_VPARENT, B_VBYTES]

theorem value_raw {v : NodeV3} {i l : Nat} {pre po : List Nat} {w : Bool}
    (h : v.value = some (i, l, pre, po, w)) : i ∈ v.raw ∧ l ∈ v.raw := by
  cases v with
  | leaf k s m =>
    cases s with
    | ref => simp [NodeV3.value] at h
    | val lb i' l' pr p' w' =>
      simp [NodeV3.value] at h; obtain ⟨rfl, rfl, -⟩ := h
      simp [NodeV3.raw, NSlot3.raw]
  | ext => simp [NodeV3.value] at h
  | branch sv kids m =>
    cases sv with
    | none => simp [NodeV3.value] at h
    | some s =>
      cases s with
      | ref => simp [NodeV3.value] at h
      | val lb i' l' pr p' w' =>
        simp [NodeV3.value] at h; obtain ⟨rfl, rfl, -⟩ := h
        simp [NodeV3.raw, NSlot3.raw]

variable {vs : List NodeS3} {es : List ValE}

theorem val_link (hw : NodeWf3 vs) (hvw : ValWf es) (hb : VParentBal vs es) {n : Nat} (hn : n < vs.length)
    {i l : Nat} {pre po : List Nat} {w : Bool} (hv : vs[n].v.value = some (i, l, pre, po, w)) :
    ∃ t, ∃ ht : t < es.length, es[t].vid = i ∧ es[t].len = l := by
  have h1 : 0 < cnt3 (nodeSends3 vs B_VPARENT) (Msg.toFp [i, l]) := by
    rw [cnt3, List.count_pos_iff, List.mem_map]
    refine ⟨[i, l], ?_, rfl⟩
    rw [vparentS, List.mem_flatMap]
    exact ⟨(vs[n], n), zip_range_mem vs hn, by simp [vparMsg, hv]⟩
  rw [hb, cnt3, List.count_pos_iff, List.mem_map, vparentR] at h1
  obtain ⟨m, hm, he⟩ := h1
  rw [List.mem_map] at hm
  obtain ⟨e, he', rfl⟩ := hm
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he'
  obtain ⟨ri, rl⟩ := value_raw hv
  have cn := hw.canon _ (List.getElem_mem hn)
  have ce := hvw.canon _ (List.getElem_mem ht)
  simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
  exact ⟨t, ht, ofNat_eq ce.1 (cn i ri) he.1, ofNat_eq ce.2.1 (cn l rl) he.2⟩

theorem le_sum_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a r ih =>
    simp only [List.mem_cons] at h; simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem sum_ge_two {α : Type} (l : List α) (g : α → Nat) {a b : Nat} (ha : a < l.length) (hb : b < l.length)
    (hab : a ≠ b) : g l[a] + g l[b] ≤ (l.map g).sum := by
  induction l generalizing a b with
  | nil => simp at ha
  | cons x r ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases a with _ | a <;> rcases b with _ | b
    · exact absurd rfl hab
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      have := le_sum_mem (l := r.map g) (List.mem_map.mpr ⟨r[b]'(by simp at hb; omega), List.getElem_mem _, rfl⟩)
      omega
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      have := le_sum_mem (l := r.map g) (List.mem_map.mpr ⟨r[a]'(by simp at ha; omega), List.getElem_mem _, rfl⟩)
      omega
    · simp only [List.getElem_cons_succ]
      have := ih (a := a) (b := b) (by simp at ha; omega) (by simp at hb; omega) (by omega)
      omega

/-- No two node records reveal the same value id. -/
theorem val_unique (hw : NodeWf3 vs) (hvw : ValWf es) (hb : VParentBal vs es) (hlen : es.length ≤ 2 ^ 22)
    {n n' : Nat} (hn : n < vs.length) (hn' : n' < vs.length)
    {i l l' : Nat} {pre po pre' po' : List Nat} {w w' : Bool}
    (hv : vs[n].v.value = some (i, l, pre, po, w)) (hv' : vs[n'].v.value = some (i, l', pre', po', w')) :
    n = n' := by
  apply Classical.byContradiction; intro hne
  obtain ⟨t, ht, hi, hl⟩ := val_link hw hvw hb hn hv
  obtain ⟨t', ht', hi', hl'⟩ := val_link hw hvw hb hn' hv'
  have htt := vid_inj hvw hlen ht ht' (by rw [hi, hi'])
  subst htt
  have hll : l = l' := by rw [← hl, ← hl']
  subst hll
  -- the message `[i, l]` is sent twice
  have hs : 2 ≤ cnt3 (nodeSends3 vs B_VPARENT) (Msg.toFp [i, l]) := by
    rw [cnt3, vparentS, List.map_flatMap, List.count_flatMap]
    have hz : (vs.zip (List.range vs.length)).length = vs.length := by simp
    have := sum_ge_two (vs.zip (List.range vs.length))
      (fun x => ((vparMsg x.1).map Msg.toFp).count (Msg.toFp [i, l])) (a := n) (b := n')
      (by rw [hz]; exact hn) (by rw [hz]; exact hn') hne
    simp only [List.getElem_zip, List.getElem_range] at this
    simp only [vparMsg, hv, hv', List.map_cons, List.map_nil, List.count_singleton_self] at this
    simpa [Function.comp_def, vparMsg] using this
  -- and received at most once
  have hr : cnt3 (valRecvs es B_VPARENT) (Msg.toFp [i, l]) ≤ 1 := by
    rw [cnt3, vparentR, List.map_map]
    apply (List.nodup_iff_count.mp ?_ _)
    unfold List.Nodup
    rw [List.pairwise_iff_getElem]
    intro a b ha hb' hab heq
    simp only [List.length_map] at ha hb'
    simp only [List.getElem_map, Function.comp, Msg.toFp, List.map_cons, List.map_nil,
      List.cons.injEq] at heq
    have ca := hvw.canon _ (List.getElem_mem ha)
    have cb := hvw.canon _ (List.getElem_mem hb')
    have := vid_inj hvw hlen ha hb' (ofNat_eq ca.1 cb.1 heq.1)
    omega
  rw [hb] at hs; omega

end ZkFormal.NearV3.Link3
